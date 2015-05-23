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
  def __init__(self, exclude = None):
    self.uses = {}
    self.exclude = exclude or set()

  def default(self, v):
    return set()

  def __call__(self, v):
    if v in self.exclude:
      return set()

    if v in self.uses:
      return self.uses[v]

    r = v.visit(self)
    self.uses[v] = r
    return r

  def visit_BinOp(self, v):
    return set.union(self(v.v1), self(v.v2), [v.v1, v.v2])

  def visit_ConversionOp(self, v):
    return set.union(self(v.v), [v.v])

  def visit_Icmp(self, v):
    return set.union(self(v.v1), self(v.v2), [v.v1, v.v2])

  def visit_Select(self, v):
    return set.union(self(v.c), self(v.v1), self(v.v2), [v.c, v.v1, v.v2])

  def visit_CnstUnaryOp(self, v):
    return set.union(self(v.v), [v.v])

  def visit_CnstBinaryOp(self, v):
    return set.union(self(v.v1), self(v.v2), [v.v1, v.v2])

  def visit_CnstFunction(self, v):
    return set.union(set(v.args), *(self(a) for a in v.args))

  def visit_PredNot(self, t):
    return self(t.v)

  def visit_PredAnd(self, t):
    return set.union(*(self(a) for a in t.args))

  def visit_PredOr(self, t):
    return set.union(*(self(a) for a in t.args))

  def visit_BinaryBoolPred(self, t):
    return set.union(self(t.v1), self(t.v2))

  def visit_LLVMBoolPred(self, t):
    return set.union(*(self(a) for a in t.args))

def all_uses(value):
  '''
  Recursively walk value and its dependencies. Return a map from values to
  sets of subvalues.
  '''
  find = _DependencyFinder()
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

    return 'Name: {0}\nPre: {1}\n{2}\n=>\n{3}'.format(
      self.name, str(self.pre),
      '\n'.join(lines(self.src_bb, set())),
      '\n'.join(lines(self.tgt_bb, self.tgt_skip)))

  def dump(self):
    print 'Name:', self.name
    print 'Pre:', str(self.pre)
    print_prog(self.src_bb, set())
    print '=>'
    print_prog(self.tgt_bb, self.tgt_skip)
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

class _OccursChecker(Visitor):
  def __init__(self, var):
    self.var = var

  def visit_Input(self, t):
    return t == self.var

  def visit_CopyOperand(self, t):
    return t.visit(self)

  def visit_BinOp(self, t):
    return t.v1.visit(self) or t.v2.visit(self)

  def visit_ConversionOp(self, t):
    return t.v.visit(self)

  def visit_Icmp(self, t):
    return t.v1.visit(self) or t.v2.visit(self)

  def visit_Select(self, t):
    return t.c.visit(self) or t.v1.visit(self) or t.v2.visit(self)

  def visit_ConstantVal(self, t):
    return False

  def visit_UndefVal(self, t):
    return False

  def visit_CnstUnaryOp(self, t):
    return t.v.visit(self)

  def visit_CnstBinaryOp(self, t):
    return t.v1.visit(self) or t.v2.visit(self)

  def visit_CnstFunction(self, t):
    return any(a.visit(self) for a in t.args)

def occurs(var, term):
  '''Return true if this variable occurs in the term'''

  return term.visit(_OccursChecker(var))

def is_const(value):
  return isinstance(value, Constant) or (isinstance(value, Input) and value.name[0] == 'C')

class Uncomposable(AliveError):
  pass

# --

PATTERN = 0
CODE = 1

class EquivalenceClass(object):
  '''
  Stores (sort,value) keys in equivalence classes. Uses a disjoint subset structure.
  '''
  #TODO: efficiency
  #TODO: really, this could be generalized to arbitrary keys.
  #      is it worth the trouble of keeping the pattern and code values in different sets?

  logger = logger.getChild('EquivalenceClass')

  def __init__(self):
    # values are stored as (sort, Value) pairs, to keep
    # code and pattern values distinct
    # each input is mapped to an equivalence class by a chain
    # of links in parent. the root is indicated by None
    self._parent = {}
    self._eqs = {}

  def __contains__(self, key):
    return key in self._parent

  def key_reps(self):
    for (sort,value) in self._parent:
      rep = self.rep(sort, value)
      yield ((sort,value),rep)

  def class_items(self):
    return self._eqs.iteritems()

  def reps(self):
    return self._eqs.iterkeys()

  def rep(self, sort, value, ensure=False):
    key = (sort, value)
    
    if key not in self._parent:
      if not ensure:
        raise KeyError(key)

      self._parent[key] = None
      eq = (set(), set())
      eq[sort].add(value)
      self._eqs[key] = eq
      return key

    while self._parent[key] is not None:
      key = self._parent[key]

    return key

  def eqs(self, sort, value):
    rep = self.rep(sort, value)
    return self._eqs[rep]

  def _unify_reps(self, rep1, rep2):
    if self.logger.isEnabledFor(logging.DEBUG):
      self.logger.debug('prep=%s; crep=%s', rep1, rep2)
      self.logger.debug('classes\n' + pformat(self._eqs, indent=2))

    if rep1 == rep2:
      self.logger.info('already unified')
      return

    self.logger.debug('removing %s', rep2)
    self._parent[rep2] = rep1
    eq2 = self._eqs.pop(rep2)
    eq1 = self._eqs[rep1]

    eq1[PATTERN].update(eq2[PATTERN])
    eq1[CODE].update(eq2[CODE])

    self.logger.debug('updated %s to %s', rep1, eq1)

  def unify_keys(self, key1, key2):
    self.logger.info('unify keys %s %s', key1, key2)

    rep1 = self.rep(*key1, ensure=True)
    rep2 = self.rep(*key2, ensure=True)

    self._unify_reps(rep1, rep2)

  def unify(self, pat, code):
    self.logger.info('unify |%s| |%s|', pat, code)

    prep = self.rep(PATTERN, pat, ensure=True)
    crep = self.rep(CODE, code, ensure=True)

    self._unify_reps(prep, crep)

  def keys_unified(self, key1, key2):
    return self.rep(*key1) == self.rep(*key2)

class Matcher(Visitor):
  '''
  Determine if code matches pattern.
  '''

  logger = logger.getChild('Matcher')

  def __init__(self, eqs):
    self.eqs = eqs

  def __call__(self, pattern, code):
    self.logger.info('matching |%s| |%s|', pattern, code)
    if (PATTERN,pattern) in self.eqs and (CODE,code) in self.eqs and \
        self.eqs.keys_unified((PATTERN,pattern),(CODE,code)):
      return True

    if isinstance(pattern, Input) or isinstance(code, Input):
      self.eqs.unify(pattern, code)
      return True

    if pattern.__class__ is not code.__class__:
      return False

    return pattern.visit(self, code)

  def subtree(self, pat, code):
    m = self(pat, code)
    self.eqs.unify(pat, code)
    return m

  def visit_BinOp(self, pat, code):
    return pat.op == code.op and all(f in code.flags for f in pat.flags) \
      and self.subtree(pat.v1, code.v1) and self.subtree(pat.v2, code.v2)

  def visit_ConversionOp(self, pat, code):
    # TODO: handle types?
    return pat.op == code.op and self.subtree(pat.v, code.v)
  
  def visit_Icmp(self, pat, code):
    if pat.op == Icmp.Var or code.op == Icmp.Var:
      raise AliveError('Matcher: general icmp matching unsupported')

    return pat.op == code.op and self.subtree(pat.v1, code.v1) and \
      self.subtree(pat.v2, code.v2)

  def visit_Select(self, pat, code):
    return self.subtree(pat.c, code.c) and self.subtree(pat.v1, code.v1) \
      and self.subtree(pat.v2, code.v2)
  
  # TODO: other instructions

  def visit_ConstantVal(self, pat, code):
    return pat.val == code.val

  # NOTE: pattern should not contain constant expressions

# --

class NotUnifiable(AliveError):
  pass

class PatternUnifier(CopyBase):
  '''
  Given two values, treated as patterns, find their least upper bound, if any.

  May further unify the equality tests.
  '''

  logger = logger.getChild('PatternUnifier')

  def __init__(self, eqs):
    self.eqs = eqs

  def __call__(self, pat1, pat2):
    logger.info('unifying |%s| |%s|', pat1, pat2)

    if pat1 is pat2:
      return pat1

    if isinstance(pat1, Input) or isinstance(pat2, Input):
      self.eqs.unify_keys((PATTERN, pat1), (PATTERN, pat2))
      return pat1  # pick one arbitrarily, since they are equal

    if pat1.__class__ is not pat2.__class__:
      raise NotUnifiable()

    return pat1.visit(self, pat2)

  def visit_BinOp(self, pat1, pat2):
    if pat1.op != pat2.op:
      raise NotUnifiable

    v1 = self(pat1.v1, pat2.v1)
    v2 = self(pat1.v2, pat2.v2)
    flags = copy(pat1.flags)
    flags.extend(f for f in pat2.flags if f not in pat1.flags)

    if v1 is pat1.v1 and v2 is pat1.v2 and flags == pat1.flags:
      return pat1

    pat = BinOp(pat1.op, copy_type(pat1.type), v1, v2, flags)
    pat.setName(pat1.getName())
    return pat

  def visit_ConversionOp(self, pat1, pat2):
    if pat1.op != pat2.op:
      raise NotUnifiable

    v = self(pat1.v, pat2.v)
    logger.warning('unifying <%s> and <%s> without checking types')

    if v is pat1.v:
      return pat1

    pat = ConversionOp(pat1.op, copy_type(pat1.stype), v, copy_type(pat1.type))
    pat.setName(pat1.getName())
    return pat

  def visit_Icmp(self, pat1, pat2):
    if pat1.op != pat2.op:
      raise NotUnifiable

    if pat1.op == Icmp.Var:
      raise AliveError('PatternUnifier: general icmp unifying unsupported')

    v1 = self(pat1.v1, pat2.v1)
    v2 = self(pat1.v2, pat2.v2)

    if v1 == pat1.v1 and v2 == pat2.v2:
      return pat1

    pat = Icmp(pat1.op, copy_type(pat1.stype), v1, v2)
    pat.setName(pat1.getName())
    return pat

  def visit_Select(self, pat1, pat2):
    c  = self(pat1.c,  pat2.c)
    v1 = self(pat1.v1, pat2.v1)
    v2 = self(pat1.v2, pat2.v2)

    if (c,v1,v2) == (pat1.c, pat1.v1, pat1.v2):
      return pat1

    pat = Select(copy_type(pat1.type), c, v1, v2)
    pat.setName(pat1.getName())

  def visit_ConstantVal(self, pat1, pat2):
    if pat1.val != pat2.val:
      raise NotUnifiable

    return pat1

  def visit_UndefVal(self, pat1, pat2):
    return pat1

  # No other constant expressions can occur in patterns

# --

class Grafter(CopyBase):
  logger = logger.getChild('Grafter')

  def __init__(self, replace):
    self.replace = replace
    self.ids = collections.OrderedDict()
    self.done = {}
    self.depth = 0

  def operand(self, term, sort):
    new_term = self.subtree(term, sort)
    
    name = new_term.getUniqueName()
    if name not in self.ids:
      self.logger.debug('Adding id %s := %s', name, new_term)
      self.ids[name] = new_term
    
    return new_term

  def subtree(self, term, sort):
    self.logger.debug('(%s) subtree |%s| %s', self.depth, term, sort)
    key = (sort,term)
    if key in self.done:
      return self.done[key]
    
    if key in self.replace:
      self.logger.debug('substituting %s -> %s', key, self.replace[key])
      return self.subtree(self.replace[key][1], self.replace[key][0])
    
    self.depth += 1
    if self.depth > 20:
      raise AliveError('Grafter: depth exceeded')

    new_term = term.visit(self, sort)
    self.depth -= 1
    
    if isinstance(new_term, Instr) and not hasattr(new_term, 'name'):
      name = term.getName()
      i = 0
      while name in self.ids:
        i += 1
        name = term.getName() + str(i)
      
      new_term.setName(name)
    
    self.done[key] = new_term
    return new_term

  def visit_Input(self, term, sort):
    if (sort,term) in self.replace:
      raise AliveError('Grafter: unexpected visit_Input({},{})'.format(term,sort))

    name = term.getName()
    i = 0
    while name in self.ids:
      i += 1
      name = term.getName() + str(i)

    self.logger.debug('new input %s for (%s, %s)', name, sort, term)
    new_term = Input(name, copy_type(term.type))
    self.ids[name] = new_term
    return new_term

# --

def _cycle_check(eqs, code_uses, pat_uses, sorted, parents):
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
    (pvals,cvals) = eqs.eqs(*rep)

    log.debug('pvals: %s', pvals)
    log.debug('cvals: %s', cvals)

    puses = imap(lambda n: (PATTERN,n), chain.from_iterable(pat_uses[p] for p in pvals))
    cuses = imap(lambda n: (CODE,n), chain.from_iterable(code_uses[p] for p in cvals))
    uses = set(eqs.rep(*k) for k in chain(puses,cuses) if k in eqs)

    for k in uses:
      parents[k].add(rep)

    cycle = any(search(k) for k in uses)
    sorted.append(rep)
    done[rep] = True
    return cycle

  return any(search(rep) for rep in eqs.reps() if rep not in done)

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

def _postunify_patterns(eqs):
  log = logger.getChild('compose.postunify_patterns')

  items = tuple(eqs.class_items())
  rep_pinstrs = {}
  rep_cinstr = set()
  unify = PatternUnifier(eqs)
  match = Matcher(eqs)
  for rep,(pvals,cvals) in items:
    pinstrs = tuple(v for v in pvals if isinstance(v, Instr))
    cinstrs = tuple(v for v in cvals if isinstance(v, Instr))

    if len(cinstrs) > 1:
      log.info('reject: unified distinct code instrs\n%s', cinstrs)
      raise NotUnifiable()

    if not pinstrs:
      continue

    pinstr = reduce(unify, pinstrs)
    rep_pinstrs[rep] = (PATTERN,pinstr)
    log.debug('Unified %s to %s', pinstrs, pinstr)

    if cinstrs:
      rep_cinstr.add(rep)
      if not match(pinstr, cinstrs[0]):
        log.info('reject: failed indirect match\n%s\n%s', pinstr, cinstrs[0])
        raise NotUnifiable()

  # the previous step may have unified some subsets containing pinstrs,
  # so unify their representatives
  did_something = True
  while did_something:
    did_something = False

    # use items() here because we may mutate rep_pinstrs
    for rep,(_,pinstr) in rep_pinstrs.items():
      rep2 = eqs.rep(*rep)
      if rep != rep2:
        if rep in rep_cinstr and rep2 in rep_cinstr:
          log.info('reject: indirectly unified distinct code instrs')
          raise NotUnifiable()

        log.debug('Unifying %s and %s', rep, rep2)
        if rep2 in rep_pinstrs:
          (_,pinstr2) = rep_pinstrs[rep2]
          rep_pinstrs[rep2] = (PATTERN,unify(pinstr2, pinstr))
        else:
          rep_pinstrs[rep2] = (PATTERN,pinstr)

        del rep_pinstrs[rep]
        if rep in rep_cinstr:
          rep_cinstr.add(rep2)

        did_something=True

  log.debug('rep_pinstrs: %s', rep_pinstrs)
  return rep_pinstrs

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

  # obtain all bindings
  eqs = EquivalenceClass()
  match = Matcher(eqs)
  if not match(pat, code):
    log.info('reject: No match')
    return None

  if log.isEnabledFor(logging.DEBUG):
    log.debug('equivalence classes\n  ' + pformat(eqs._eqs, indent=2))

  try:
    rep_replace = _postunify_patterns(eqs)
  except NotUnifiable:
    return None

  if log.isEnabledFor(logging.DEBUG):
    log.debug('equivalence classes after postunify\n  ' + pformat(eqs._eqs, indent=2))

  # check validity of equivalences
  # ------------------------------

  # cycle check
  code_uses = all_uses(code)
  pat_uses = all_uses(op2.src_root())
  extended_pat_uses = _DependencyFinder(set.union(pat_uses[pat], [pat]))(op2.src_root())
  if log.isEnabledFor(logging.DEBUG):
    log.debug('\ncode_uses:\n' + pformat(code_uses, indent=2)
      + '\npat_uses:\n' + pformat(pat_uses, indent=2)
      + '\nextended_pat-uses:\n' + pformat(extended_pat_uses, indent=2))

  # these values occur in op1.tgt only
  intermediates = {(CODE,v) for v in code_uses[code]
    if isinstance(v, Instr) and v.getName() not in op1.tgt_skip}

  log.debug('intermediates %s', intermediates)

  toposort = []
  direct_users = collections.defaultdict(set)

  if _cycle_check(eqs, code_uses, pat_uses, toposort, direct_users):
    log.info('reject: unifications form a cycle')
    return None

  log.debug('topological sort: %s', toposort)
  log.debug('direct_users: %s', direct_users)
  users = get_ancestors(direct_users)
  log.debug('users: %s', users)

  pre3 = []
  replace = {}

  # test each subset after any subsets which use it
  for rep in reversed(toposort):
    pvals, cvals = eqs.eqs(*rep)
    log.debug('checking %s: %s, %s', rep, pvals, cvals)
    log.debug('rep_replace: %s', rep_replace)

    cinstr = tuple(v for v in cvals if isinstance(v, Instr))
    if len(cinstr) > 1:
      log.info('reject: unified distinct code instrs\n%s', cinstr)
      return None

    pinstr = tuple(v for v in pvals if isinstance(v, Instr))
    if len(cinstr) + len(pinstr) > 1:
      assert rep in rep_replace

    const = tuple((CODE,v) for v in cvals if is_const(v)) \
      + tuple((PATTERN,v) for v in pvals if is_const(v))

    if const and len(pinstr) + len(cinstr) > 0:
      log.info('reject: unified constant and instr')
      return None

    # find the replacement
    if cinstr:
      cinstr = cinstr[0]
      rep_replace[rep] = (CODE, cinstr)

      # check whether this instruction is an intermediate value
      if (CODE, cinstr) in intermediates:
        log.debug('%s in intermediates', cinstr)
        if any(isinstance(v, Input) for v in cvals):
          log.info('reject: intermediate value matched with code input')
          return None

      # check whether this instruction unified with a code input
      # or an extended pattern input
      if not any(isinstance(v, Input) for v in cvals) and \
          pvals.isdisjoint(extended_pat_uses):
        log.debug('subset does not include code inputs or intersect extended pattern.')
        continue

      # check whether this instruction uses any cexprs
      cexprs = tuple(v for v in code_uses[cinstr]
                      if (CODE,v) not in eqs and isinstance(v, Constant)
                        and not isinstance(v, ConstantVal))

      if not cexprs:
        continue

      log.debug('code instruction %s uses cexprs %s', cinstr, cexprs)

      sub_cexprs = set.union(*(code_uses[e] for e in cexprs))

      log.debug('sub_cexprs %s', sub_cexprs)

      for cexpr in cexprs:
        if cexpr in sub_cexprs: continue

        log.info('new constant for %s', cexpr)
        new_c = (CODE, Input('C0', IntType()))
        replace[(CODE,cexpr)] = new_c
        pre3.append((new_c, (CODE,cexpr)))

    elif pinstr:
      rep_replace[rep] = (PATTERN, pinstr[0])

      # check whether this instructions dependencies unified with an intermediate value
      for pval in pat_uses[pinstr[0]]:
        log.debug('%s uses %s', pinstr[0], pval)
        if (PATTERN,pval) in eqs:
          if any((CODE,c) in intermediates for c in eqs.eqs(PATTERN,pval)[CODE]):
            log.info('reject: pattern instruction depends on intermediate value')
            return None

    elif const:
      # pvals contains only inputs or literals
      # cvals contains inputs or cexprs

      # 1. make sure all literals agree
      lits = set(v.val for s,v in const if isinstance(v, ConstantVal))
      if len(lits) > 1:
        log.info('reject: unified distinct literals')
        return None

      # 2. constant expressions
      cexprs = tuple(v for v in cvals if isinstance(v, Constant) and not isinstance(v, ConstantVal))
      # 2a. constants and literals
      if lits:
        new_c = (CODE, ConstantVal(lits.pop(), IntType()))
        rep_replace[rep] = new_c

        pre3.extend((new_c,(CODE,c)) for c in cexprs)

        continue

      # 2b. constant expressions
      if cexprs:
        if any(sort == PATTERN and isinstance(r, Instr) for sort,r in
                (rep_replace[r] for r in users.get(rep,()))) or \
            not pvals.isdisjoint(extended_pat_uses) or \
            any(isinstance(v, Input) for v in cvals):
          log.debug('Used by a pattern instruction, extended pattern, or code input')
          new_c = (CODE, Input('C0', IntType()))
          rep_replace[rep] = new_c
          pre3.extend((new_c, (CODE,c)) for c in cexprs)
          continue

        new_c = (CODE, cexprs[0])
        rep_replace[rep] = new_c

        pre3.extend((new_c, (CODE,c)) for c in cexprs[1:])

        continue

      # 3. only symbolic constants
      rep_replace[rep] = const[0]

    else:
      # everything is an input, choose one arbitrarily
      # FIXME: make sure we don't pick an intermediate node?
      rep_replace[rep] = (CODE, iter(cvals).next())

  # replace everything with the rep's replacement
  for key,rep in eqs.key_reps():
    if key not in replace and key != rep_replace[rep]:
      replace[key] = rep_replace[rep]

  if log.isEnabledFor(logging.DEBUG):
    log.debug('replace\n  ' + pformat(replace))


  # create new transformation 
  # -------------------------
  graft = Grafter(replace)

  # create new source
  if pattern_at:
    if (PATTERN,pat) in replace:
      raise AliveError('Pattern match point already matched')

    root_uses = extended_pat_uses
    log.debug('root uses %s', root_uses)

    if any(replace.get((PATTERN,v), ()) in intermediates for v in root_uses):
      log.info('reject: Extended pattern requires intermediate value.')
      if log.isEnabledFor(logging.DEBUG):
        x = tuple((v, replace[(PATTERN,v)]) for v in root_uses
                    if replace.get((PATTERN,v), ()) in intermediates)
        log.debug('Culprit: ' + pformat(x))
      return None

    replace[(PATTERN,pat)] = (CODE, op1.src_root())
    new_s = graft.operand(op2.src_root(), PATTERN)
  else:
    new_s = graft.operand(op1.src_root(), CODE)

  src = copy(graft.ids)
  tgt_skip = {r for r,i in src.iteritems() if isinstance(i, Instr)}

  if log.isEnabledFor(logging.DEBUG):
    log.debug('src ids:\n' + '\n'.join('  %s = %s' % it for it in src.iteritems()))

  # make precondition
  pre1 = graft.subtree(op1.pre, CODE)
  pre2 = graft.subtree(op2.pre, PATTERN)
  pre3 = map(lambda ((s1,v1),(s2,v2)): BinaryBoolPred(0, graft.subtree(v1,s1), v2.visit(graft, s2)), pre3)
  pre = mk_conjoin(un_conjoin(pre1) + un_conjoin(pre2) + tuple(pre3))

  log.debug('pre: %s', pre)

  # forget the new operands
  # (this is okay, because fixupTypes now recurses into operands)
  graft.ids = copy(src)

  # create new target
  if code_at:
    replace[(CODE,code)] = (PATTERN, op2.tgt_root())
    new_t = graft.operand(op1.tgt_root(), CODE)
  else:
    new_t = graft.operand(op2.tgt_root(), PATTERN)

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
  

def all_bin_compositions(o1, o2, immediate=True):
  logger.info('all_bin_compositions |%s| |%s|', o1.name, o2.name)
  #assert o1 is not o2

  try:
    o12 = compose(o1, o2)
    if o12: 
      yield o12
  except Exception as e:
    if immediate: 
      raise
    logger.exception('all_bin_compositions %r\n;\n%s\n;\n%s', e, o1, o2)
  
  regs = [r for r,v in o2.src.iteritems() if isinstance(v,Instr)]
  regs.pop()
  for r in regs:
    try:
      o12 = compose(o1, o2, pattern_at = r)
      if o12: yield o12
    except Exception as e:
      if immediate:
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
      if immediate:
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
