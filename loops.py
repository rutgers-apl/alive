#import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
#from codegen import *
from itertools import combinations, izip, count, chain, imap
from copy import copy
import alive
from pprint import pprint, pformat
import logging
import collections
import subsets

NAME, PRE, SRC_BB, TGT_BB, SRC, TGT, SRC_USED, TGT_USED, TGT_SKIP = range(9)

logger = logging.getLogger(__name__)

def dump(instr):
  if isinstance(instr, Instr) and hasattr(instr, 'name'):
    return '<{0}|{1}>#{2}'.format(instr.getName(), instr, id(instr))

  return '<{0}>#{1}'.format(instr, id(instr))

class Visitor(object):
  def default(self, v, *args, **kw):
    raise AliveError('{1}: No default behavior for <{0}>'.format(v,
      type(self).__name__))
    
  def __getattr__(self, name):
    if name.startswith('visit_'):
      return lambda *v, **kw: self.default(*v, **kw)
    
    raise AttributeError


def base_visit(obj, visitor, *args, **kws):
  return getattr(visitor, 'visit_' + obj.__class__.__name__)(obj, *args, **kws)

# monkeypatch Value to handle visiting
Value.visit = base_visit
BoolPred.visit = base_visit


class _DependencyFinder(Visitor):
  def __init__(self, exclude = None, tag = None):
    self.uses = {}
    self.exclude = exclude or set()
    self.tag = tag or (lambda n: n)

  def default(self, v):
    return frozenset()

  def __call__(self, v):
    k = self.tag(v)
    if k in self.exclude:
      return frozenset()

    if k in self.uses:
      return self.uses[k]

    r = v.visit(self)
    self.uses[k] = r
    return r

  def subtree(self, v):
    'If v is not excluded, generate v and its dependencies'

    k = self.tag(v)
    if k in self.exclude:
      return

    yield k
    for d in self(v):
      yield d

  def visit_CopyOperand(self, v):
    return frozenset(self.subtree(v.v))

  def visit_BinOp(self, v):
    return frozenset(chain(self.subtree(v.v1), self.subtree(v.v2)))

  def visit_ConversionOp(self, v):
    return frozenset(chain(self.subtree(v.v)))

  def visit_Icmp(self, v):
    return frozenset(chain(self.subtree(v.v1), self.subtree(v.v2)))

  def visit_Select(self, v):
    return frozenset(
      chain(self.subtree(v.c), self.subtree(v.v1), self.subtree(v.v2)))

  def visit_CnstUnaryOp(self, v):
    return frozenset(self.subtree(v.v))

  def visit_CnstBinaryOp(self, v):
    return frozenset(chain(self.subtree(v.v1), self.subtree(v.v2)))

  def visit_CnstFunction(self, v):
    return frozenset(chain.from_iterable(self.subtree(a) for a in v.args))

  def visit_PredNot(self, t):
    return self(t.v)

  def visit_PredAnd(self, t):
    return frozenset.union(*(self(a) for a in t.args))

  def visit_PredOr(self, t):
    return frozenset.union(*(self(a) for a in t.args))

  def visit_BinaryBoolPred(self, t):
    return frozenset.union(self(t.v1), self(t.v2))

  def visit_LLVMBoolPred(self, t):
    return frozenset.union(*(self(a) for a in t.args))

def all_uses(value, tag=None):
  '''
  Recursively walk value and its dependencies. Return a map from values to
  sets of subvalues.
  '''
  find = _DependencyFinder(tag=tag)
  find(value)
  return find.uses


class UnacceptableArgument(AliveError):
  def __init__(self, cls, arg, val, msg = ''):
    self.cls = cls
    self.arg = arg
    self.val = val
    self.msg = msg

  def __repr__(self):
    return 'UnacceptableArgument({0.cls!r}, {0.arg!r},'\
           ' {0.val!r}, {0.msg!r})'.format(self)

  def __str__(self):
    msg = ', expected ' + self.msg if self.msg else ''

    return 'Unacceptable argument for {0.cls} #{0.arg}: {0.val!r}{1}'.\
      format(self, msg)

def isConstExpr(val):
  if isinstance(val, Input):
    return val.name[0] == 'C'

  return isinstance(val, Constant)


class CopyBase(Visitor):
  logger = logger.getChild('CopyBase')

  def subtree(self, val, *xargs, **kws):
    return self.default(val, *xargs, **kws)

  def operand(self, val, *xargs, **kws):
    return self.subtree(val, *xargs, **kws)
  
  # -- instructions
  def visit_CopyOperand(self, val, *xargs, **kws):
    return CopyOperand(self.operand(val.v, *xargs, **kws), copy_type(val.type))

  def visit_BinOp(self, val, *xargs, **kws):
    return BinOp(val.op, copy_type(val.type),
            self.operand(val.v1, *xargs, **kws),
            self.operand(val.v2, *xargs, **kws),
            copy(val.flags))

  def visit_ConversionOp(self, term, *xargs, **kws):
    return ConversionOp(term.op, copy_type(term.stype),
                        self.operand(term.v, *xargs, **kws),
                        copy_type(term.type))

  def visit_Icmp(self, term, *xargs, **kws):
    op = term.opname if term.op == Icmp.Var else Icmp.opnames[term.op]
    
    return Icmp(op, copy_type(term.stype),
                self.operand(term.v1, *xargs, **kws),
                self.operand(term.v2, *xargs, **kws))

  def visit_Select(self, term, *xargs, **kws):
    c = self.operand(term.c, *xargs, **kws)
    v1 = self.operand(term.v1, *xargs, **kws)
    v2 = self.operand(term.v2, *xargs, **kws)

#     if not isinstance(c.type, IntType):
#       self.logger.info('visit_Select: narrowing type of %s', c)
#       c.type = c.type.ensureIntType()

    return Select(copy_type(term.type), c, v1, v2)

  # -- constants
  @staticmethod
  def _ensure_constant(val, cls, arg):
    if isinstance(val, Input) and val.name[0] == 'C':
      return val

    if isinstance(val, Constant):
      return val

    raise UnacceptableArgument(cls, arg, val, 'constant')

  def visit_ConstantVal(self, val, *xargs, **kws):
    return ConstantVal(val.val, copy_type(val.type))
  
  def visit_UndefVal(self, val, *xargs, **kws):
    return UndefVal(copy_type(val.type))
  
  def visit_CnstUnaryOp(self, val, *xargs, **kws):
    return CnstUnaryOp(val.op,
      self._ensure_constant(self.subtree(val.v, *xargs, **kws), CnstUnaryOp, 1))

  def visit_CnstBinaryOp(self, val, *xargs, **kws):
    return CnstBinaryOp(val.op,
      self._ensure_constant(self.subtree(val.v1, *xargs, **kws), CnstBinaryOp, 1),
      self._ensure_constant(self.subtree(val.v2, *xargs, **kws), CnstBinaryOp, 2))

  def visit_CnstFunction(self, val, *xargs, **kws):
    #FIXME: Alive currently doesn't check arguments to constant functions
    return CnstFunction(val.op, [self.operand(a, *xargs, **kws) for a in val.args],
      copy_type(val.type))
  
  # -- predicates
  def visit_TruePred(self, term, *xargs, **kws):
    return term # FIXME?
  
  def visit_PredNot(self, term, *xargs, **kws):
    return PredNot(self.subtree(term.v, *xargs, **kws))
  
  def visit_PredAnd(self, term, *xargs, **kws):
    return PredAnd(*(self.subtree(a, *xargs, **kws) for a in term.args))
  
  def visit_PredOr(self, term, *xargs, **kws):
    return PredOr(*(self.subtree(a, *xargs, **kws) for a in term.args))
    
  def visit_BinaryBoolPred(self, term, *xargs, **kws):
    return BinaryBoolPred(term.op,
      self.subtree(term.v1, *xargs, **kws),
      self.subtree(term.v2, *xargs, **kws))
  
  def visit_LLVMBoolPred(self, term, *xargs, **kws):
    args = []
    for i,a in izip(count(1), term.args):
      new = self.operand(a, *xargs, **kws)
      ok, msg = LLVMBoolPred.argAccepts(term.op, i, new)
      if not ok:
        raise UnacceptableArgument(LLVMBoolPred.opnames[term.op], i, new, msg)
      args.append(new)

    return LLVMBoolPred(term.op, args)



class ShallowCopier(CopyBase):
  def subtree(self, term):
    return term

def rename_Instr(instr, name):
  assert isinstance(instr, Instr)
  new = instr.visit(ShallowCopier())
  new.setName(name)
  return new

  

class Copier(CopyBase):
  '''Makes a deep copy of a value, renaming as requested.'''
  
  def __init__(self, vars = {}, renamer = None):
    if renamer is None: renamer = lambda n: n
    
    self.renamer = renamer
    self.vars = vars
  
  def __call__(self, term):
    if term in self.vars:
      return self.vars[term]
  
    new_term = term.visit(self)
    self.vars[term] = new_term
    
    if isinstance(new_term, Instr):
      new_term.setName(self.renamer(term.getName()))
    
    return new_term
  
  def subtree(self, term):
    return self(term)
    
  def visit_Input(self, term):
    return Input(self.renamer(term.getName()), copy_type(term.type))


def copy_type(ty):
  '''Copy the argument into a new anonymous type.'''
  
  assert isinstance(ty, Type)
  
  if isinstance(ty, IntType):
    if ty.defined:
      return IntType(ty.size)
    
    return IntType()
  
  if isinstance(ty, PtrType):
    return PtrType(copy_type(ty.type))
  
  if isinstance(ty, NamedType):
    return NamedType(ty.name)
  
  if isinstance(ty, UnknownType):
    if isinstance(ty, NamedType):
      nty = NamedType(ty.name)
      nty.type = copy_type(ty.type)
      # TODO: rethink this
    else:
      nty = UnknownType()

    nty.types = {}
    nty.myType = ty.myType
    for kind, subtype in ty.types.iteritems():
      nty.types[kind] = copy_type(ty.types[kind])
    
    return nty
  
  if isinstance(ty, ArrayType):
    #sys.stderr.write('WARNING: not copying array type {0}\n'.format(ty))
    # FIXME: handle ArrayType better
    return ArrayType()
  
  assert False

# ----

class AliveTypeError(AliveError):
  pass

class Printer(Visitor):
  def __init__(self, names):
    self.names = names

  def visit_TruePred(self, t):
    return "true"

  def visit_PredNot(self, t):
    return '!' + t.v.visit(self)

  def visit_PredAnd(self, t):
    return '(' + ' && '.join(s.visit(self) for s in t.args) + ')'

  def visit_PredOr(self, t):
    return '(' + ' || '.join(s.visit(self) for s in t.args) + ')'

  def visit_BinaryBoolPred(self, t):
    lhs = t.v1.getName() if t.v1 in self.names else repr(t.v1)
    rhs = t.v2.getName() if t.v2 in self.names else repr(t.v2)

    return '(%s %s %s)' % (lhs, t.opnames[t.op], rhs)

  def visit_LLVMBoolPred(self, t):
    args = (a.getName() if a in self.names else repr(a) for a in t.args)

    return '%s(%s)' % (t.opnames[t.op], ', '.join(args))

class Transformation(object):
  '''Represents a single Alive transformation (optimization).'''
  
  def __init__(self, name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used,
                tgt_skip):
    self.name     = name
    self.pre      = pre
    self.src_bb   = src_bb
    self.tgt_bb   = tgt_bb
    self.src      = src
    self.tgt      = tgt
    self.src_used = src_used
    self.tgt_used = tgt_used
    self.tgt_skip = tgt_skip

  def src_root(self):
    '''Returns the root value of the source (i.e., the last instruction)'''

    values = self.src.values()
    root = values.pop()
    while not isinstance(root, Instr):
      root = values.pop()

    return root

  def tgt_root(self):
    '''Returns the root value of the target'''

    return self.tgt[self.src_root().getName()]

  def __str__(self):
    def lines(bbs, skip):
      for bb, instrs in bbs.iteritems():
        if bb != '':
          yield '%s:' % bb

        for k,v in instrs.iteritems():
          if k in skip:
            continue
          k = str(k)
          if k[0] == '%':
            yield '  %s = %s' % (k,v)
          else:
            yield '  %s' % v

    names = self.src.values()
    pre = self.pre.visit(Printer(names))

    return 'Name: {0}\nPre: {1}\n{2}\n=>\n{3}'.format(
      self.name, pre,
      '\n'.join(lines(self.src_bb, set())),
      '\n'.join(lines(self.tgt_bb, self.tgt_skip)))

  def dump(self):
    print str(self)
#     print 'Name:', self.name
#     print 'Pre:', str(self.pre)
#     print_prog(self.src_bb, set())
#     print '=>'
#     print_prog(self.tgt_bb, self.tgt_skip)
#     print
#     print 'src', self.src
#     print 'tgt', self.tgt
#     print 'src_used', self.src_used
#     print 'tgt_used', self.tgt_used
#     print 'tgt_skip', self.tgt_skip
  
  def copy(self, rename = None):
    import copy
    assert len(self.src_bb) == 1 and len(self.tgt_bb) == 1
    # TODO: handle basic blocks
    
    if rename is None:
      rename = lambda n: n
    
    src = collections.OrderedDict()
    vars = {}
    copier = Copier(vars, rename)
    for k,v in self.src.iteritems():
      new_v = copier(v)
      src[new_v.getUniqueName()] = new_v
      
      # print 'copy: Value {0}[{1}] => {2}[{3}]'.format(k,v,new_v.getUniqueName(),new_v)
    
    # precondition
    pre = copier(self.pre)

    
    # target
    tgt = collections.OrderedDict()
    for k,v in self.tgt.iteritems():
      new_v = copier(v)
      tgt[new_v.getUniqueName()] = new_v

      # print 'copy: Value {0}[{1}] => {2}[{3}]'.format(k,v,new_v.getUniqueName(),new_v)
    
    # source basic blocks
    src_bb = collections.OrderedDict()
    for lab,bb in self.src_bb.iteritems():
      new_bb = collections.OrderedDict()
      for v in bb.itervalues():
        new_v = vars[v]
        new_bb[new_v.getUniqueName()] = new_v
      src_bb[lab] = new_bb
    
    # target basic blocks
    tgt_bb = collections.OrderedDict()
    for lab,bb in self.tgt_bb.iteritems():
      new_bb = collections.OrderedDict()
      for v in bb.itervalues():
        new_v = vars[v]
        new_bb[new_v.getUniqueName()] = new_v
      tgt_bb[lab] = new_bb

    # target skip list
    tgt_skip = set(rename(k) for k in self.tgt_skip)

    new = Transformation(self.name, pre, src_bb, tgt_bb, src, tgt,
                         None, None, tgt_skip)
    return new

  def type_models(self):
    '''Yields all type models satisfying the transformation's type constraints.
    '''
    
    reset_pick_one_type()
    global gbl_prev_flags
    gbl_prev_flags = []
    
    # infer allowed types for registers
    type_src = getTypeConstraints(self.src)
    type_tgt = getTypeConstraints(self.tgt)
    type_pre = self.pre.getTypeConstraints()

    s = SolverFor('QF_LIA')
    s.add(type_pre)
    if s.check() != sat:
      raise AliveTypeError(self.name + ': Precondition does not type check')

    # Only one type per variable/expression in the precondition is required.
    for v in s.model().decls():
      register_pick_one_type(v)

    s.add(type_src)
    unregister_pick_one_type(alive.get_smt_vars(type_src))
    if s.check() != sat:
      raise AliveTypeError(self.name + ': Source program does not type check')

    s.add(type_tgt)
    unregister_pick_one_type(alive.get_smt_vars(type_tgt))
    if s.check() != sat:
      raise AliveTypeError(self.name + 
        ': Source and Target programs do not type check')

    # Pointers are assumed to be either 32 or 64 bits
    ptrsize = Int('ptrsize')
    s.add(Or(ptrsize == 32, ptrsize == 64))

    sneg = SolverFor('QF_LIA')
    sneg.add(Not(mk_and([type_pre] + type_src + type_tgt)))


    # temporarily disabled
#     has_unreach = any(v.startswith('unreachable') for v in self.tgt.iterkeys())
#     for v in self.src.iterkeys():
#       if v[0] == '%' and v not in self.src_used and v not in self.tgt_used and\
#          v in self.tgt_skip and not has_unreach:
# 
#          raise AliveError(self.name + 
#            ':ERROR: Temporary register %s unused and not overwritten' % v)
# 
#     for v in self.tgt.iterkeys():
#       if v[0] == '%' and v not in self.tgt_used and v not in self.src:
#         raise AliveError(self.name +
#            ':ERROR: Temporary register %s unused and does not overwrite any'\
#            ' Source register' % v)

    # disabled because it doesn't seem necessary 
#     # build constraints that indicate the number of users for each register.
#     users_count = countUsers(self.src_bb)
#     users = {}
#     for k in self.src.iterkeys():
#       n_users = users_count.get(k)
#       users[k] = [get_users_var(k) != n_users] if n_users else []

    # pick one representative type for types in Pre
    res = s.check()
    assert res != unknown
    if res == sat:
      s2 = SolverFor('QF_LIA')
      s2.add(s.assertions())
      alive.pick_pre_types(s, s2)

    while res == sat:
      types = s.model()
      yield types
      
      alive.block_model(s, sneg, types)
      res = s.check()
      assert res != unknown


# ----

def is_const(value):
  return isinstance(value, Constant) or (isinstance(value, Input) and value.name[0] == 'C')

class TaggedValue(subsets.Tag):
  def __repr__(self):
    if isinstance(self.val, Instr) and hasattr(self.val, 'name'):
      return '{}({} = {})'.format(type(self).__name__, self.val.name, self.val)
    return '{}({})'.format(type(self).__name__, self.val)

class Pattern(TaggedValue): pass
class Code(TaggedValue): pass

# --

class NoMatch(AliveError): pass

class PatternMatchBase(Visitor):
  '''
  Determine if code matches pattern.

  Define subtree() for specializing recursive calls.
  '''

  logger = logger.getChild('PatternMatchBase')

  def __call__(self, pattern, code):
    logger.info('Matching (%s) (%s)', pattern, code)

    if isinstance(pattern, Input) or isinstance(code, Input):
      return

    if pattern.__class__ is not code.__class__:
      raise NoMatch

    pattern.visit(self, code)

  def visit_BinOp(self, pat, code):
    if pat.op != code.op or any(f not in code.flags for f in pat.flags):
      raise NoMatch

    self.subtree(pat.v1, code.v1)
    self.subtree(pat.v2, code.v2)

  def visit_ConversionOp(self, pat, code):
    # TODO: handle types?
    if pat.op != code.op:
      raise NoMatch

    self.subtree(pat.v, code.v)

  def visit_Icmp(self, pat, code):
    if pat.op == Icmp.Var or code.op == Icmp.Var:
      raise AliveError('Matcher: general icmp matching unsupported')

    if pat.op != code.op:
      raise NoMatch

    self.subtree(pat.v1, code.v1)
    self.subtree(pat.v2, code.v2)

  def visit_Select(self, pat, code):
    self.subtree(pat.c, code.c)
    self.subtree(pat.v1, code.v1)
    self.subtree(pat.v2, code.v2)

  # TODO: other instructions

  def visit_ConstantVal(self, pat, code):
    if pat.val != code.val:
      raise NoMatch

  # NOTE: pattern should not contain constant expressions

class BFSMatcher(PatternMatchBase):
  '''Queues subtree matches for later examination.'''

  def __init__(self, queue):
    self.queue = queue

  def subtree(self, pat, code):
    self.queue.append((Pattern(pat), Code(code)))

# --


class PatternMergeBase(Visitor):
  '''
  Given two values, treated as patterns, find their least upper bound, if any.

  Override subtree() to define recursive behavior.
  '''

  logger = logger.getChild('PatternMergeBase')

  def __call__(self, pat1, pat2):
    logger.info('merging |%s| |%s|', pat1, pat2)

    if isinstance(pat2, Input):
      return pat1

    if isinstance(pat1, Input):
      return pat2

    if pat1.__class__ is not pat2.__class__:
      raise NoMatch

    return pat1.visit(self, pat2)

  def visit_BinOp(self, pat1, pat2):
    if pat1.op != pat2.op:
      raise NoMatch

    v1 = self.subtree(pat1.v1, pat2.v1)
    v2 = self.subtree(pat1.v2, pat2.v2)
    flags = copy(pat1.flags)
    flags.extend(f for f in pat2.flags if f not in pat1.flags)

    if v1 is pat1.v1 and v2 is pat1.v2 and flags == pat1.flags:
      return pat1

    pat = BinOp(pat1.op, copy_type(pat1.type), v1, v2, flags)
    pat.setName(pat1.getName())
    return pat

  def visit_ConversionOp(self, pat1, pat2):
    if pat1.op != pat2.op:
      raise NoMatch

    v = self.subtree(pat1.v, pat2.v)
    logger.warning('unifying <%s> and <%s> without checking types',
                      pat1.v, pat2.v)

    if v is pat1.v:
      return pat1

    pat = ConversionOp(pat1.op, copy_type(pat1.stype), v, copy_type(pat1.type))
    pat.setName(pat1.getName())
    return pat

  def visit_Icmp(self, pat1, pat2):
    if pat1.op != pat2.op:
      raise NoMatch

    if pat1.op == Icmp.Var:
      raise AliveError('PatternUnifier: general icmp unifying unsupported')

    v1 = self.subtree(pat1.v1, pat2.v1)
    v2 = self.subtree(pat1.v2, pat2.v2)

    if v1 == pat1.v1 and v2 == pat2.v2:
      return pat1

    pat = Icmp(pat1.op, copy_type(pat1.stype), v1, v2)
    pat.setName(pat1.getName())
    return pat

  def visit_Select(self, pat1, pat2):
    c  = self.subtree(pat1.c,  pat2.c)
    v1 = self.subtree(pat1.v1, pat2.v1)
    v2 = self.subtree(pat1.v2, pat2.v2)

    if (c,v1,v2) == (pat1.c, pat1.v1, pat1.v2):
      return pat1

    pat = Select(copy_type(pat1.type), c, v1, v2)
    pat.setName(pat1.getName())

  def visit_ConstantVal(self, pat1, pat2):
    if pat1.val != pat2.val:
      raise NoMatch

    return pat1

  def visit_UndefVal(self, pat1, pat2):
    return pat1

  # No other constant expressions can occur in patterns

class BFSPatternMerger(PatternMergeBase):
  '''Queues subtree matches for later examination.'''

  def __init__(self, queue):
    self.queue = queue

  def subtree(self, pat1, pat2):
    self.queue.append((Pattern(pat1), Pattern(pat2)))
    return pat1

# --

class Grafter(CopyBase):
  logger = logger.getChild('Grafter')

  def __init__(self, replace):
    self.replace = replace
    self.ids = collections.OrderedDict()
    self.done = {}
    self.depth = 0

  def operand(self, term, tag):
    new_term = self.subtree(term, tag)
    
    name = new_term.getUniqueName()
    if name not in self.ids:
      self.logger.debug('Adding id %s := %s', name, new_term)
      self.ids[name] = new_term
    
    return new_term

  def subtree(self, term, tag):
    self.logger.debug('(%s) subtree %s |%s|#%s', self.depth, tag.__name__, term, id(term))
    key = tag(term)
    if key in self.done:
      self.logger.debug('(%s) reusing %s', self.depth, self.done[key])
      return self.done[key]
    
    if key in self.replace:
      self.logger.debug('substituting %s -> %s', key, self.replace[key])
      return self.subtree(self.replace[key].val, type(self.replace[key]))
    
    self.depth += 1
    new_term = term.visit(self, tag)
    self.depth -= 1
    
    if isinstance(new_term, Instr) and not hasattr(new_term, 'name'):
      name = term.getName()
      i = 0
      while name in self.ids:
        i += 1
        name = term.getName() + str(i)
      
      new_term.setName(name)

    if not isinstance(new_term, Constant) or isinstance(new_term, ConstantVal):
      self.done[key] = new_term
    return new_term

  def visit_Input(self, term, tag):
    if tag(term) in self.replace:
      raise AliveError('Grafter: unexpected visit_Input({},{})'.format(term,tag.__name__))

    name = term.getName()
    i = 0
    while name in self.ids:
      i += 1
      name = term.getName() + str(i)

    self.logger.debug('new input %s for %s(%s)', name, tag.__name__, term)
    new_term = Input(name, copy_type(term.type))
    self.ids[name] = new_term
    return new_term

# --

def _match_pattern(pat, code):
  '''
  Used by compose to determine whether the provided code matches the pattern.
  '''

  log = logger.getChild('compose.match_pattern')

  subs = subsets.DisjointSubsets()
  pinstr = {} # rep -> merge of all pattern instrs, if any
  cinstr = {} # rep -> code instr, if any

  def add_key(k):
    if k in subs:
      return subs.rep(k)

    log.debug('New key: %s', k)
    subs.add_key(k)

    if isinstance(k, Pattern) and isinstance(k.val, Instr):
      pinstr[k] = k

    if isinstance(k, Code) and isinstance(k.val, Instr):
      cinstr[k] = k

    return k

  worklist = collections.deque()
  worklist.append((Pattern(pat), Code(code)))
  match = BFSMatcher(worklist)
  merge = BFSPatternMerger(worklist)

  while worklist:
    if log.isEnabledFor(logging.DEBUG):
      log.debug('\nworklist:  ' + str(worklist)
        + '\nsubsets:\n  ' + pformat(subs._subset, indent=2)
        + '\npinstr:\n  ' + pformat(pinstr, indent=2)
        + '\ncinstr:\n  ' + pformat(cinstr, indent=2))

    k1,k2 = worklist.popleft()
    r1 = add_key(k1)
    r2 = add_key(k2)

    log.debug('Checking %s %s', r1, r2)

    if subs.unified(r1, r2):
      continue

    subs.unify(r1,r2)

    # make sure r1 is the new rep
    if r2 == subs.rep(r1):
      r1,r2 = r2,r1

    # only one cinstr permitted
    # FIXME: CopyOperand
    if r1 in cinstr and r2 in cinstr:
      log.info('reject: unified code instrs %s, %s', cinstr[r1], cinstr[r2])
      raise NoMatch

    # we need to match if one subset has a cinstr and the other has pinstrs
    # pinstrs and cinstrs in the same subset have already matched
    match_needed = \
      (r1 in cinstr and r2 in pinstr) or (r2 in cinstr and r1 in pinstr)

    # if r2 had a cinstr, move it to r1
    if r2 in cinstr:
      cinstr[r1] = cinstr.pop(r2)

    # if both subsets had pinstrs, merge them
    if r1 in pinstr and r2 in pinstr:
      log.debug('merging %s %s', pinstr[r1], pinstr[r2])
      pinstr[r1] = Pattern(merge(pinstr[r1].val, pinstr.pop(r2).val))

    # if only r2 had a pinstr, move it to r1
    if r2 in pinstr:
      pinstr[r1] = pinstr.pop(r2)

    # by now both the pinstr and cinstr have moved to r1
    if match_needed:
      log.debug('matching %s %s', pinstr[r1], cinstr[r1])
      match(pinstr[r1].val, cinstr[r1].val)

  assert all(r == subs.rep(r) for r in chain(pinstr, cinstr))

  # if a subset has a pinstr and a cinstr, the cinstr will be at
  # least as specific
  pinstr.update(cinstr)

  return subs, pinstr

def _cycle_check(subsets, dependencies, sorted, parents):
  '''
  Used by compose to find cycles. Basic DFS, except the arcs are 
  determined by uses and eqs.
  '''
  
  log = logger.getChild('cycle_check')

  done = {} # False when key is in progress, True when complete

  def search(rep):
    log.info('searching %s', rep)
    log.debug('done: %s', done)

    if rep in done:
      return not done[rep]

    done[rep] = False
    vals = subsets.subset(rep)
    uses = set(subsets.rep(d) for v in vals for d in dependencies[v]
                if d in subsets)

    for k in uses:
      parents[k].add(rep)

    cycle = any(search(k) for k in uses)
    sorted.append(rep)
    done[rep] = True
    return cycle

  return any(search(rep) for rep in subsets.reps() if rep not in done)

def _check_subset(rep, subs, rep_replace, equations, is_starter):
  '''
  Used by compose to determine if a subset is valid, and what its replacement
  should be.
  '''
  log = logger.getChild('compose.check_subset')

  subset = subs.subset(rep)

  log.debug('checking %s: %s', rep, subset)

  symbols = set(k for k in subset
                  if isinstance(k.val, Input) and k.val.name[0] == 'C')
  cexprs = set(k for k in subset
                  if isinstance(k.val, Constant) and
                    not isinstance(k.val, ConstantVal))
  lits = set(k for k in subset
              if isinstance(k.val, ConstantVal))
  lit_vals = set(k.val.val for k in lits)

  # subset cannot contain constants and instrs
  if rep in rep_replace and (symbols or cexprs or lit_vals):
    log.info('reject: subset contains consts and instrs')
    raise NoMatch

  # if this is an instr, we're okay (?)
  if rep in rep_replace:
    return

  if len(lit_vals) > 1:
    log.info('reject: subset unifies distinct literals')
    raise NoMatch

  if lit_vals:
    new_c = lits.pop()
    rep_replace[rep] = new_c # choose a literal at random
    equations.extend((new_c, c) for c in cexprs)
    return

  if cexprs:
    # if any of our users will appear in the pattern, create a new symbol
    if is_starter:
      new_c = symbols.pop() if symbols else Code(Input('C0', IntType()))
    else:
      new_c = cexprs.pop()

    rep_replace[rep] = new_c
    equations.extend((new_c, c) for c in cexprs)
    return

  if symbols:
    rep_replace[rep] = symbols.pop()
    return

  # this subset contains no instrs or constants, so it must be all inputs
  rep_replace[rep] = iter(subset).next()


def _validate(op):
  '''
  Check for common incorrect compositions.
  '''
  log = logger.getChild('validate')
  log.debug('validating\n%s', op)

  df = _DependencyFinder()
  src_uses = df(op.src_root())
  tgt_uses = df(op.tgt_root())
  pre_uses = df(op.pre)

  if log.isEnabledFor(logging.DEBUG):
    log.debug('src_uses\n  '
      + '\n  '.join('<%s>#%s'%(v,id(v)) for v in src_uses)
      + '\ntgt_uses\n  '
      + '\n  '.join('<%s>#%s'%(v,id(v)) for v in tgt_uses)
      + '\npre_uses\n  '
      + '\n  '.join('<%s>#%s'%(v,id(v)) for v in pre_uses))

  # every value in src must have a unique name
  names = collections.Counter()
  for v in src_uses:
    names[v.getUniqueName()] += 1
  for n,c in names.iteritems():
    if c > 2:
      log.error('Non-unique name: %s\n%s', n, op)
      raise AliveError('Non-unique name')

  # every input must occur in the src
  for v in chain(tgt_uses, pre_uses):
    log.debug('Checking <%s>#%s', v, id(v))
    if isinstance(v, Input) and v not in src_uses:
      log.error('Input %s does not occur in source\n%s', v, op)
      raise AliveError('Input %s does not occur in source' % v)

  # src must not contain cexprs
  for v in src_uses:
    if isinstance(v, Constant) and not isinstance(v, ConstantVal) \
      and not isinstance(v, UndefVal):
      log.error('Constant expression in source\n%s', op)
      raise AliveError('Constant expression in source')


def compose(op1, op2, code_at = None, pattern_at = None):
  '''Create a new transformation combining op1 and op2.

  If code_at is not None, then match pattern to the root of op1.tgt.
  If pattern_at is not None, then match code to the root of op2.src.
  At least one of code_at and pattern_at must be None.
  '''
  assert code_at is None or pattern_at is None

  log = logger.getChild('compose')
  log.info('compose(%s, %s, %s, %s)', op1.name, op2.name, code_at, pattern_at)
  log.debug('op1:\n%s', op1)
  log.debug('op2:\n%s', op2)


  # determine matching roots
  code = op1.tgt[code_at] if code_at else op1.tgt_root()
  pat  = op2.src[pattern_at] if pattern_at else op2.src_root()

  try:
    subs, rep_replace = _match_pattern(pat, code)
  except NoMatch:
    log.info('reject: No match')
    return None

  if log.isEnabledFor(logging.DEBUG):
    log.debug('equivalence classes\n  ' + pformat(subs._subset, indent=2))

  # dependency analysis
  # -------------------

  df = _DependencyFinder(tag=Code)
  init_root_deps = df(op1.src_root())
  df(op1.tgt_root())  # possibly just code is okay here?
  dependencies = df.uses

  df = _DependencyFinder(tag=Pattern)
  df(pat)
  dependencies.update(df.uses)

  df = _DependencyFinder(tag=Pattern, exclude=(Pattern(pat),))
  extended_pat_deps = df(op2.src_root())

  if log.isEnabledFor(logging.DEBUG):
    log.debug('\ndependencies:\n  ' + pformat(dependencies, indent=2)
      + '\ninit_root_deps:\n  ' + pformat(init_root_deps, indent=2)
      + '\nextended_pat_deps:\n  ' + pformat(extended_pat_deps, indent=2))

  # these values occur in op1.tgt only
  intermediates = {v for v in dependencies[Code(code)]
    if isinstance(v.val, Instr) and v.val.getName() not in op1.tgt_skip}

  log.debug('intermediates %s', intermediates)

  # cycle check
  # -----------

  toposort = []
  direct_users = collections.defaultdict(set)

  if _cycle_check(subs, dependencies, toposort, direct_users):
    log.info('reject: unifications form a cycle')
    return None

  log.debug('direct_users: %s', direct_users)
  users = get_ancestors(direct_users)
  log.debug('users: %s', users)
  log.debug('topological sort: %s', toposort)

  # check validity of equivalences
  # ------------------------------

  pre3 = []
  replace = {}
  starters = set() # reps present in the initial code

  # test each subset after any subsets which use it
  for rep in reversed(toposort):
    subset = subs.subset(rep)

    if any(k in starters for k in users.get(rep, ())) or \
        any(k in init_root_deps or k in extended_pat_deps for k in subset):
      starters.add(rep)
      log.debug('%s in starters', rep)

    is_starter = rep in starters
    is_intermediate = any(k in intermediates for k in subset)

    if is_starter and is_intermediate:
      log.info('reject: %s is starter and intermediate', rep)
      return None

    try:
      _check_subset(rep, subs, rep_replace, pre3, is_starter)
    except NoMatch:
      return None
    log.debug('  rep_replace[%s] = %s', rep, rep_replace[rep])

  # replace everything with the rep's replacement
  for key,rep in subs.key_reps():
    if key not in replace and key != rep_replace[rep]:
      replace[key] = rep_replace[rep]

  if log.isEnabledFor(logging.DEBUG):
    log.debug('replace\n  ' + pformat(replace))


  # create new transformation 
  # -------------------------
  graft = Grafter(replace)

  # create new source
  if pattern_at:
    #if Pattern(pat) in replace:
    #  raise AliveError('Pattern match point already matched')

    # TODO: see if this should be moved earlier, or is redundant
    if any(replace.get(v, ()) in intermediates for v in extended_pat_deps):
      log.info('reject: Extended pattern requires intermediate value.')
      if log.isEnabledFor(logging.DEBUG):
        x = tuple((v, replace[v]) for v in extended_pat_deps
                    if replace.get(v, ()) in intermediates)
        log.debug('Culprit: ' + pformat(x))
      return None

    replace[Pattern(pat)] = Code(op1.src_root())
    log.debug('replace\n  ' + pformat(replace))
    new_s = graft.operand(op2.src_root(), Pattern)
  else:
    new_s = graft.operand(op1.src_root(), Code)

  src = copy(graft.ids)
  tgt_skip = {r for r,i in src.iteritems() if isinstance(i, Instr)}

  if log.isEnabledFor(logging.DEBUG):
    log.debug('src ids:\n' + '\n'.join('  %s = %s' % it for it in src.iteritems()))

  # make precondition
  pre1 = graft.subtree(op1.pre, Code)
  pre2 = graft.subtree(op2.pre, Pattern)
  pre3 = (BinaryBoolPred(0, graft.subtree(k1.val, type(k1)), 
                            k2.val.visit(graft, type(k2)))
            for k1,k2 in pre3)
  pre = mk_conjoin(un_conjoin(pre1) + un_conjoin(pre2) + tuple(pre3))

  log.debug('pre: %s', pre)

  # forget the new operands
  # (this is okay, because fixupTypes now recurses into operands)
  for k,v in graft.ids.iteritems():
    if k not in src and not isinstance(v, Instr):
      src[k] = v

  graft.ids = copy(src)

  # create new target
  if code_at:
    replace[Code(code)] = Pattern(op2.tgt_root())
    new_t = graft.operand(op1.tgt_root(), Code)
  else:
    new_t = graft.operand(op2.tgt_root(), Pattern)

  # make sure target root has same name as source root
  rname = new_s.getName()
  graft.ids.pop(new_t.getName())
  graft.ids.pop(rname)
  graft.ids[rname] = rename_Instr(new_t, rname)
  tgt_skip.discard(rname)

  tgt = graft.ids
  
  if log.isEnabledFor(logging.DEBUG):
    log.debug('tgt ids:\n' + '\n'.join('  %s = %s' % it for it in tgt.iteritems()))

  src_bb = mk_bb(src)
  tgt_bb = mk_bb(tgt)

  if pattern_at:
    name = '({0};{1}@{2})'.format(op1.name, op2.name, pattern_at)
  elif code_at:
    name = '({0}@{2};{1})'.format(op1.name, op2.name, code_at)
  else:
    name = '({};{})'.format(op1.name, op2.name)

  r = Transformation(name, pre, src_bb, tgt_bb, src, tgt, None, None, tgt_skip)
  _validate(r)
  return r

def get_ancestors(parents):
  ancestors = {}
  def walk(node):
    if node in ancestors:
      return

    direct = parents.get(node, set())
    ancestors[node] = set(direct)
    for p in direct:
      walk(p)
      ancestors[node].update(ancestors[p])

  for node in parents:
    walk(node)

  return ancestors

def mk_bb(ids):
  bb = ((r,i) for r,i in ids.iteritems() if isinstance(i, Instr))
  return {'': collections.OrderedDict(bb)}

def un_conjoin(p):
  if isinstance(p, TruePred):
    return ()
  if isinstance(p, PredAnd):
    return p.args
  return (p,)

def mk_conjoin(ps):
  if len(ps) == 0:
    return TruePred()
  if len(ps) == 1:
    return ps[0]
  return PredAnd(*ps)


def satisfiable(opt):
  '''check whether a transformation's precondition can be satisfied'''
  
  log = logger.getChild('satisfiable')
  log.info('checking %s', opt.name)
  log.debug('\n%s', opt)
  
  try:
    for types in opt.type_models():
      #print 'attempting'
      set_ptr_size(types)
      fixupTypes(opt.src, types)
      fixupTypes(opt.tgt, types)
      opt.pre.fixupTypes(types)

      srcv = toSMT(opt.src_bb, opt.src, True)
      tgtv = toSMT(opt.tgt_bb, opt.tgt, False)
      try:
        pre_d, pre = opt.pre.toSMT(srcv)
        # FIXME: this crashes occasionally. why?
      except Exception:
        log.error('''Threw exception in satisfiable()
  types %s
  srcv %s
  tgtv %s''', types, srcv.vars, tgtv.vars)
        raise
  
      extra_cnstrs = pre_d + pre  # NOTE: not checking allocas
    
      # show satsifiability
      # NOTE: does this need to know about qvars?
      s = alive.tactic.solver()
      s.add(extra_cnstrs)
      #print 'checking', s
      alive.gen_benchmark(s)
      res = s.check()
    
      if res == sat:
        log.info('success: %s', s.model())
        #TODO: make this loggable
        #alive.print_var_vals(s, srcv, tgtv, 'X', types)
        return True
  except AliveTypeError as e:
    log.info('type error: %s', e)

  return False
  

def all_bin_compositions(o1, o2, on_error=None):
  logger.info('all_bin_compositions |%s| |%s|', o1.name, o2.name)
  #assert o1 is not o2

  try:
    o12 = compose(o1, o2)
    if o12: 
      yield o12
  except Exception as e:
    if not on_error or on_error(e, o1, o2):
      raise
    logger.exception('all_bin_compositions %r\n;\n%s\n;\n%s', e, o1, o2)
  
  regs = [r for r,v in o2.src.iteritems() if isinstance(v,Instr)]
  regs.pop()
  for r in regs:
    try:
      o12 = compose(o1, o2, pattern_at = r)
      if o12: yield o12
    except Exception as e:
      if not on_error or on_error(e, o1, o2):
        raise
      logger.exception('all_bin_compositions %r\n;@%s\n%s\n;\n%s', e, r, o1, o2)
  
  regs = [r for r,v in o1.tgt.iteritems()
            if isinstance(v,Instr) and r not in o1.tgt_skip]
  regs.pop()
  for r in regs:
    try:
      o12 = compose(o1, o2, code_at = r)
      if o12: yield o12
    except Exception as e:
      if not on_error or on_error(e, o1, o2):
        raise
      logger.exception('all_bin_compositions %r\n;\n%s\n;@%s\n%s', e, o1, r, o2)


def all_compositions(opts):
  for o1 in opts:
    for o2 in opts:
      # make sure we don't compose the same thing
      if o1 is o2: o2 = o1.copy()
      
      for o12 in all_bin_compositions(o1,o2):
        yield o12


def check_self_loop(opt):
  '''Check all satisfiable self-compositions.'''
  
  opt_src_len = sum(1 for v in opt.src.itervalues() if isinstance(v, Instr))
  
  o2 = opt.copy()
  for oo in all_bin_compositions(opt, o2):    
    print '\n-----\n', oo.name
    
    oo_src_len = sum(1 for v in oo.src.itervalues() if isinstance(v, Instr))

    print opt_src_len, '->', oo_src_len
    
    
    try:
      if oo_src_len <= opt_src_len and satisfiable(oo):
        print
        oo.dump()

        return True
    except Exception, e:
      import traceback
      print 'CAUGHT from satisfiable():', traceback.format_exc(sys.exc_info())
  
  return False

def parse_transforms(input):
  return [Transformation(*o) for o in parse_opt_file(input)]


if __name__ == '__main__':
  sys.stderr.write("[Reading from stdin...]\n")
  opts = parse_transforms(sys.stdin.read())

  for o in opts:
    try:
      check_self_loop(o)
    except Exception, e:
      import traceback
      print o.name, ': CAUGHT', traceback.format_exc(sys.exc_info())
