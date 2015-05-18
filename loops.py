#import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
#from codegen import *
from itertools import combinations, izip, count
#from collections import defaultdict
from copy import copy
import alive
from pprint import pprint

NAME, PRE, SRC_BB, TGT_BB, SRC, TGT, SRC_USED, TGT_USED, TGT_SKIP = range(9)


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

def all_identifiers(value):
  class V(Visitor):
    def default(self, v):
      return []

    def visit_Input(self, v):
      return [v]
    
    def visit_BinOp(self, v):
      return v.v1.visit(self) + v.v2.visit(self) + [v]
  
    def visit_CnstBinaryOp(self, v):
      return v.v1.visit(self) + v.v2.visit(self)

  return value.visit(V())

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
  def subtree(self, val):
    return self.default(val)

  def operand(self, val):
    return self.subtree(val)
  
  # -- instructions
  def visit_CopyOperand(self, val):
    return CopyOperand(self.operand(val.v), copy_type(val.type))

  def visit_BinOp(self, val):
    return BinOp(val.op, copy_type(val.type), self.operand(val.v1),
            self.operand(val.v2), copy(val.flags))

  def visit_ConversionOp(self, term):
    return ConversionOp(term.op, copy_type(term.stype), self.operand(term.v),
                        copy_type(term.type))

  def visit_Icmp(self, term):
    op = term.opname if term.op == Icmp.Var else Icmp.opnames[term.op]
    
    return Icmp(op, copy_type(term.stype), self.operand(term.v1),
                self.operand(term.v2))

  def visit_Select(self, term):
    return Select(copy_type(term.type), self.operand(term.c),
                  self.operand(term.v1), self.operand(term.v2))

  # -- constants
  @staticmethod
  def _ensure_constant(val, cls, arg):
    if isinstance(val, Input) and val.name[0] == 'C':
      return val

    if isinstance(val, Constant):
      return val

    raise UnacceptableArgument(cls, arg, val, 'constant')

  def visit_ConstantVal(self, val):
    return ConstantVal(val.val, copy_type(val.type))
  
  def visit_UndefVal(self, val):
    return UndefVal(copy_type(val.type))
  
  def visit_CnstUnaryOp(self, val):
    return CnstUnaryOp(val.op,
      self._ensure_constant(self.subtree(val.v), CnstUnaryOp, 1))

  def visit_CnstBinaryOp(self, val):
    return CnstBinaryOp(val.op,
      self._ensure_constant(self.subtree(val.v1), CnstBinaryOp, 1),
      self._ensure_constant(self.subtree(val.v2), CnstBinaryOp, 2))

  def visit_CnstFunction(self, val):
    #FIXME: Alive currently doesn't check arguments to constant functions
    return CnstFunction(val.op, [self.operand(a) for a in val.args],
      copy_type(val.type))
  
  # -- predicates
  def visit_TruePred(self, term):
    return term # FIXME?
  
  def visit_PredNot(self, term):
    return PredNot(self.subtree(term.v))
  
  def visit_PredAnd(self, term):
    return PredAnd(*(self.subtree(a) for a in term.args))
  
  def visit_PredOr(self, term):
    return PredOr(*(self.subtree(a) for a in term.args))
    
  def visit_BinaryBoolPred(self, term):
    return BinaryBoolPred(term.op, self.subtree(term.v1), self.subtree(term.v2))
  
  def visit_LLVMBoolPred(self, term):
    args = []
    for i,a in izip(count(1), term.args):
      new = self.operand(a)
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

class Transformation(object):
  '''Represents a single Alive transformation (optimization).'''
  
  def __init__(self, name, pre, src_bb, tgt_bb, src, tgt, src_used, tgt_used,
                tgt_skip, aux = None):
    self.name     = name
    self.pre      = pre
    self.src_bb   = src_bb
    self.tgt_bb   = tgt_bb
    self.src      = src
    self.tgt      = tgt
    self.src_used = src_used
    self.tgt_used = tgt_used
    self.tgt_skip = tgt_skip
    self.aux      = aux

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
      raise AliveError(self.name + ': Precondition does not type check')

    # Only one type per variable/expression in the precondition is required.
    for v in s.model().decls():
      register_pick_one_type(v)

    s.add(type_src)
    unregister_pick_one_type(alive.get_smt_vars(type_src))
    if s.check() != sat:
      raise AliveError(self.name + ': Source program does not type check')

    s.add(type_tgt)
    unregister_pick_one_type(alive.get_smt_vars(type_tgt))
    if s.check() != sat:
      raise AliveError(self.name + 
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

class Unifier(Visitor):
  def __init__(self, vars = None):
    if vars == None: vars = {}

    self.vars = vars
    self.t2 = None
  
  def unify(self, var, term):
    #print 'unify', dump(var), dump(term)
    if var in self.vars:
      #FIXME: determine whether any other cases exist
      #return self(self.vars[var], term)
      if isinstance(self.vars[var], Input):
        return self.unify(self.vars[var], term)
      if isinstance(term, Input):
        return self.unify(term, self.vars[var])

      #TODO: allow recursive unification of constant expressions?
      return self.vars[var] is term

    if isinstance(term, Input) and term.name[0] != 'C':
      term, var = var, term

    if var.name[0] == 'C' and isinstance(term, Instr):
      return False

    if term in self.vars:
      raise AliveError('Unifying already unified term!')

    if occurs(var, term):
      return False

    #print '.. {0} := {1}'.format(dump(var),dump(term))
    self.vars[var] = term
    return True
    
  def __call__(self, t1, t2):
    #print 'Unifier({0})({1}, {2})'.format(self.vars, dump(t1), dump(t2))

    if t1 is t2:
      return True

    if isinstance(t1, Input):
      return self.unify(t1, t2)
    
    if isinstance(t2, Input):
      return self.unify(t2, t1)

    # FIXME: CopyOperand!

    if t1.__class__ is not t2.__class__:
      return False
    
    r = t1.visit(self, t2)
    if r:
      #FIXME: no longer sure why this is here
      assert t2 not in self.vars
      self.vars[t2] = t1
      #print '.. {0} := {1}'.format(dump(t2),dump(t1))

    return r
  
  def visit_BinOp(self, t1, t2):
    # FIXME: handle flags
    return t1.op == t2.op and self(t1.v1,t2.v1) and self(t1.v2,t2.v2)

  def visit_ConversionOp(self, t1, t2):
    # FIXME: check for explicit types
    return t1.op == t2.op and self(t1.v, t2.v)

  def visit_Icmp(self, t1, t2):
    if t1.op == Icmp.Var or t2.op == Icmp.Var:
      raise AliveError('Unifier: No support for general icmp matching ' +
        str(t1) + '; ' + str(t2))

    return t1.op == t2.op and self(t1.v1, t2.v1) and self(t1.v2, t2.v2)

  def visit_Select(self, t1, t2):
    return self(t1.c, t2.c) and self(t1.v1, t2.v1) and self(t1.v2, t2.v2)

  def visit_ConstantVal(self, t1, t2):
    return t1.val == t2.val

  #TODO visit_UndefVal

  def visit_CnstUnaryOp(self, t1, t2):
    return t1.op == t2.op and self(t1.v, t2.v)

  def visit_CnstBinaryOp(self, t1, t2):
    return t1.op == t2.op and self(t1.v1, t2.v2) and self(t1.v2, t2.v2)

  def visit_CnstFunction(self, t1, t2):
    return t1.op == t2.op and all(self(a1,a2) for (a1,a2) in izip(t1.args, t2.args))

  #def default(self, t1):
  #  return False
  

class Grafter(CopyBase):
  '''Make a new instruction tree with operand identifier map, substituting
  inputs according to the provided table.'''
  
  def __init__(self, vars = None):
    if vars == None: vars = {}

    self.vars = vars  # old value -> old value
    self.done = {}    # old value -> new value
    self.ids = collections.OrderedDict()  # name -> new value
    self.depth = 0
    self.allow_new_instrs = True
  
  def __call__(self, term):
    return self.operand(term)
  
  def subtree(self, term):
    #print '.' * self.depth,
    #print 'subtree:', dump(term), 'Done', term in self.done, 'Var', term in self.vars
    
    if term in self.done:
      return self.done[term]

    # check whether this term was unified
    if term in self.vars:
      #print '.' * self.depth,
      #print '< substitute', dump(term), ':=', dump(self.vars[term])
      #term = self.vars[term]
      return self.subtree(self.vars[term])
  
    if self.depth > 20:
      raise AliveError('Grafter: depth exceeded')

    self.depth += 1
    new_term = term.visit(self)
    self.depth -= 1
    #print '.. visit <=', dump(new_term)
    
    #if not hasattr(term, 'name'):
    #  print 'NO NAME:', term
    #  assert False
    
    if isinstance(new_term, Instr) and not hasattr(new_term, 'name'):
      name = term.getName()
      while name in self.ids:
        name += '0'

      new_term.setName(name)
    
    self.done[term] = new_term
    
    #print '.' * self.depth,
    #print 'subtree <=', dump(self.done[term])
    
    return self.done[term]
  
  def operand(self, term):
    #print '.' * self.depth, 'operand:', dump(term)
    new_term = self.subtree(term)

    name = new_term.getUniqueName()
    if name not in self.ids and (not isinstance(new_term, Instr) or self.allow_new_instrs):
      #print '.' * self.depth, 'ids[{0}] = {1}'.format(name, dump(new_term))
      self.ids[name] = new_term
    
    return new_term

  def visit_Input(self, term):
    #print 'visit_Input', dump(term), '=>', self.vars.get(term, None)

    if term in self.vars:
      return self.subtree(self.vars[term])
    
    # this is a new input, so we need a fresh name
    name = term.getName()
    while name in self.ids:
      name += '0'
      # TODO: improve name generation

    new_term = Input(name, copy_type(term.type))
    self.ids[name] = new_term
    return new_term


def is_const(value):
  return isinstance(value, Constant) or (isinstance(value, Input) and value.name[0] == 'C')

class Matcher(Visitor):
  def __init__(self):
    self.cvars = {}  # code input -> (isCode, code value or pattern instr))
    self.pvars = {}  # pattern input -> code value
    self.equalities = []  # (code cexpr, code cexpr) list

  def chase(self, var):
    'Recursively look up a code input'
    if var not in self.cvars:
      return (True, var)

    (isCode, term) = self.cvars[var]
    if isCode:
      return self.chase(term)
    
    return (isCode, term)
  
  def unifyCode(self, code1, code2):
    '''If one or both are unbound variables, bind them.
    
    Instructions only unify if identical.
    '''
    #print 'unify', dump(code1), dump(code2)
    if isinstance(code1, Input) and not occurs(code1, code2):
      return self.bindCVar(code1, True, code2)
    
    if isinstance(code2, Input) and not occurs(code2, code1):
      return self.bindCVar(code2, True, code1)
    
    if is_const(code1) and is_const(code2):
      self.equalities.append((code1, code2))
      return True
    
    return code1 is code2
  
  def bindCVar(self, var, isCode, term):
    if not isCode and isinstance(term, Input):
      raise AliveError('Matcher.bindCVar: attempt bind to an input')
  
    if var in self.cvars:
      (isCode1, term1) = self.chase(var)
      
      if isCode and isCode1:
        return self.unifyCode(term1, term)
        
      raise AliveError('Matcher.bindCVar: incomplete')
    
    if var.name[0] == 'C' and not isinstance(term, Constant):
      return False
    
    if var is term:
      raise AliveError('About to create a circular link!')
    
    self.cvars[var] = (isCode, term)
    return True
  
  def bindPVar(self, var, code):
    'Bind a pattern input to a code value'
    
    (isCode, term) = self.chase(code)
    if not isCode:
      raise AliveError('Matcher.bindPVar: unify patterns')

    if var in self.pvars:
      return self.unifyCode(self.pvars[var], term)
    
    if var.name[0] != 'C':
      self.pvars[var] = term
      return True

    if isinstance(term, Constant) or (isinstance(term, Input) and term.name[0] == 'C'):
      self.pvars[var] = term
      return True
    
    if isinstance(term, Input):
      self.cvars[term] = (False, var)

    return False

  
  def __call__(self, pattern, code):
#     print 'match', dump(pattern), dump(code)
    if isinstance(pattern, Input):
      return self.bindPVar(pattern, code)
    if isinstance(code, Input):
      return self.bindCVar(code, False, pattern)
    
    # pattern and code are both instrs or constants
    # note that pattern can not be a constant expression
    if pattern.__class__ != code.__class__:
      return False
    
    return pattern.visit(self, code)

  def visit_BinOp(self, pat, code):
    return pat.op == code.op and all(f in code.flags for f in pat.flags) \
      and self(pat.v1, code.v1) and self(pat.v2, code.v2)

  def visit_ConversionOp(self, pat, code):
    # FIXME: need to handle types
    return pat.op == code.op and self(pat.v, code.v)
  
  def visit_Icmp(self, pat, code):
    if pat.op == Icmp.Var or code.op == Icmp.Var:
      raise AliveError('Matcher: No support for general icmp matching')
    
    return pat.op == code.op and self(pat.v1, code.v1) and self(pat.v2, code.v2)

  def visit_Select(self, pat, code):
    return self(pat.c, code.c) and self(pat.v1, code.v1) and self(pat.v2, code.v2)
  
  def visit_ConstantVal(self, pat, code):
    return pat.val == code.val
  
  def visit_UndefVal(self, pat, code):
    raise AliveError('Matcher: no support for undef')

class PatternGrafter(CopyBase):
  def __init__(self, graft):
    self.graft = graft
  
  def operand(self, term):
    new_term = self.subtree(term)
    
    name = new_term.getUniqueName()
    if name not in self.graft.ids:
      self.graft.ids[name] = new_term
    
    return new_term
  
  def subtree(self, term):
    print '.' * self.graft.depth, 'pat subtree', dump(term),
    print '| done' if term in self.graft.pdone else ('| var' if term in self.graft.pvars else '')

    if term in self.graft.pdone:
      return self.graft.pdone[term]
    
    if term in self.graft.pvars:
      return CodeGrafter(self.graft).subtree(self.graft.pvars[term])

    # make sure we don't put a constant expression in the source
    if self.graft.phase == self.graft.Source and isinstance(term, Constant) \
      and not isinstance(term, ConstantVal):
      #FIXME: undef?
      i = 9
      n = 'C'
      while n in self.graft.ids:
        i += 1
        n = 'C' + str(i)
      
      new_c = Input(n, IntType())
      self.graft.equalities.append(BinaryBoolPred(0, new_c, term))
      self.graft.pdone[term] = new_c
      return new_c

    
    self.graft.depth += 1
    if self.graft.depth > 20:
      raise AliveError('Grafter: depth exceeded')
    
    new_term = term.visit(self)
    self.graft.depth -= 1
    
    if isinstance(new_term, Instr) and not hasattr(new_term, 'name'):
      name = term.getName()
      while name in self.graft.ids:
        name += '0'
      
      new_term.setName(name)
    
    self.graft.pdone[term] = new_term
    return new_term

  def visit_Input(self, term):
    if term in self.graft.pvars:
      # can this ever happen?
      return CodeGrafter(self.graft).subtree(term)
    
    name = term.getName()
    while name in self.graft.ids:
      name += '0'
    new_term = Input(name, copy_type(term.type))
    self.graft.ids[name] = new_term
    return new_term

class Uncomposable(AliveError):
  pass

class CodeGrafter(CopyBase):
  def __init__(self, graft):
    self.graft = graft
  
  def operand(self, term):
    new_term = self.subtree(term)
    
    name = new_term.getUniqueName()
    if name not in self.graft.ids:
      self.graft.ids[name] = new_term
    
    return new_term
  
  def subtree(self, term):
    print '.' * self.graft.depth, 'code subtree', dump(term),
    print '| done' if term in self.graft.cdone else ('| var' if term in self.graft.cvars else ''),
    print '| unavailable' if term in self.graft.unavailable else ''
    
    if term in self.graft.unavailable:
      raise Uncomposable()

    if term in self.graft.cdone:
      return self.graft.cdone[term]
    
    if term in self.graft.cvars:
      (isCode, term) = self.graft.cvars[term]
      while isCode and term in self.graft.cvars:
        (isCode, term) = self.graft.cvars[term]
      if isCode:
        return self.subtree(term)
      
      return PatternGrafter(self.graft).subtree(term)
    
    # make sure we don't put a constant expression in the source
    if self.graft.phase == self.graft.Source and isinstance(term, Constant) \
      and not isinstance(term, ConstantVal):
      #FIXME: undef?
      i = 9
      n = 'C'
      while n in self.graft.ids:
        i += 1
        n = 'C' + str(i)
      
      new_c = Input(n, IntType())
      self.graft.equalities.append(BinaryBoolPred(0, new_c, term))
      self.graft.cdone[term] = new_c
      return new_c
      
    
    self.graft.depth += 1
    if self.graft.depth > 20:
      raise AliveError('Grafter: depth exceeded')
    
    new_term = term.visit(self)
    self.graft.depth -= 1
    
    if isinstance(new_term, Instr) and not hasattr(new_term, 'name'):
      name = term.getName()
      while name in self.graft.ids:
        name += '0'
      
      new_term.setName(name)
    
    self.graft.cdone[term] = new_term
    return new_term

  def visit_Input(self, term):
    if term in self.graft.cvars:
      # can this ever happen?
      raise AliveError('Grafter: unexpected visit_Input({})'.format(term.name)) 

    name = term.getName()
    while name in self.graft.ids:
      name += '0'
    new_term = Input(name, copy_type(term.type))
    self.graft.ids[name] = new_term
    return new_term


class NewGrafter(object):
  '''Make a new instruction tree with operand identifier map, substituting
  inputs according to the provided table.'''
  
  Source = 0
  Target = 1
  Precondition = 2

  def __init__(self, pvars, cvars, unavailable):
    self.pvars = pvars  # pat var -> code value
    self.cvars = cvars  # code var -> (True, code var) | (False, pat instr)
    self.unavailable = unavailable  # code values which don't exist yet

    self.pdone = {} # pat value -> new value
    self.cdone = {} # code value -> new value
    self.ids = collections.OrderedDict()
    self.depth = 0
    self.phase = NewGrafter.Source
    self.equalities = []
  
  def with_pattern(self, term):
    return PatternGrafter(self).operand(term)
  
  def with_code(self, term):
    return CodeGrafter(self).operand(term)

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

def mk_PredAnd(p1,p2):
  if isinstance(p1, TruePred):
    return p2
  if isinstance(p2, TruePred):
    return p1
  return PredAnd(p1,p2)

def compose(op1, op2, code_at = None, pattern_at = None):
  '''Create a new transformation combining op1 and op2.

  If tgt1_at is not None, then match it to the root of op2.src.
  If src2_at is not None, then match it to the root of op1.tgt.
  At least one of tgt1_at and src2_at must be None.
  '''
  assert code_at is None or pattern_at is None
  
  code = op1.tgt_root() if code_at is None else op1.tgt[code_at]
  pat = op2.src_root() if pattern_at is None else op2.src[pattern_at]
  
#   print '\n\nComposing:'
#   op1.dump()
#   op2.dump()
  
  match = Matcher()
  
  if not match(pat, code):
#     print 'No match'
    return None
  
  print 'pvars:',
  pprint({dump(k):dump(v) for k,v in match.pvars.iteritems()})
  print 'cvars:',
  pprint({dump(k):(c,dump(v)) for k,(c,v) in match.cvars.iteritems()})
  print 'equalities:', match.equalities
  
  intermediates = {v for k,v in op1.tgt.iteritems() if k not in op1.tgt_skip and isinstance(v, Instr)}
  
#   print 'intermediates:',
#   pprint({dump(v) for v in intermediates})
    
  graft = NewGrafter(match.pvars, match.cvars, intermediates)
  
  try:
    if pattern_at:
      graft.pvars[pat] = op1.src_root()
      new_s = graft.with_pattern(op2.src_root())
    else:
      new_s = graft.with_code(op1.src_root())
  except Uncomposable:
    return None
  
  src = copy(graft.ids)
  tgt_skip = {r for r,i in src.iteritems() if isinstance(i, Instr)}

  # once the pattern has been matched, all code is available
  graft.unavailable = set()
  graft.phase = graft.Precondition
  
  pre1 = CodeGrafter(graft).subtree(op1.pre)
  pre2 = PatternGrafter(graft).subtree(op2.pre)
  pre3 = tuple(BinaryBoolPred(0, x, y) for x,y in match.equalities)
  #pre = mk_PredAnd(pre1, pre2)
  pre = mk_conjoin(un_conjoin(pre1) + un_conjoin(pre2) + pre3 + tuple(graft.equalities))
  
  aux = []
  
  # backward compatibility: add any new operands back to src, except for instrs
  for r,i in graft.ids.iteritems():
    if r not in src:
      if isinstance(i, Instr):
        aux.append(i)
      else:
        src[r] = i
  
#   print 'src:'
#   pprint({k:dump(v) for k,v in src.iteritems()})
#   print 'aux',
#   pprint([dump(v) for v in aux])
  
  rname = new_s.getName()
  graft.ids = copy(src)
  graft.ids.pop(rname)
  tgt_skip.discard(rname)
  graft.phase = graft.Target
  if code_at:
    graft.cvars[code] = (False, op2.tgt_root())
    old_t = rename_Instr(op1.tgt_root(), rname)
    new_t = graft.with_code(old_t)
  else:
    old_t = rename_Instr(op2.tgt_root(), rname)
    new_t = graft.with_pattern(old_t)
    
  tgt = graft.ids

#   print 'tgt:'
#   pprint({k:dump(v) for k,v in tgt.iteritems()})
  
  def mk_bb(ids):
    bb = ((r,i) for r,i in ids.iteritems() if isinstance(i, Instr))
    return {'': collections.OrderedDict(bb)}

  src_bb = mk_bb(src)
  tgt_bb = mk_bb(tgt)
  
  if pattern_at:
    name = '({0};{1}@{2})'.format(op1.name, op2.name, pattern_at)
  elif code_at:
    name = '({0}@{2};{1})'.format(op1.name, op2.name, code_at)
  else:
    name = '({};{})'.format(op1.name, op2.name)
  
  return Transformation(name, pre, src_bb, tgt_bb, src, tgt, None, None, tgt_skip, aux)
  

def old_compose_2(op1, op2, tgt1_at = None, src2_at = None):
  '''Create a new transformation combining op1 and op2.

  If tgt1_at is not None, then match it to the root of op2.src.
  If src2_at is not None, then match it to the root of op1.tgt.
  At least one of tgt1_at and src2_at must be None.
  '''
  assert tgt1_at is None or src2_at is None

  mroot1 = op1.tgt[op1.src_root().getName()] if tgt1_at is None else op1.tgt[tgt1_at]
  mroot2 = op2.src_root() if src2_at is None else op2.src[src2_at]

  # unify the specified sub-graphs
  unify = Unifier()
  match = unify(mroot1, mroot2)

  if not match:
    return None

  #print 'compose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}

  graft = Grafter(unify.vars)

  # copy op1.src, making the replacements found in unify
  new_s = graft(op1.src_root())

  if src2_at is not None:
    # if we didn't match op1.tgt against the root of op2.src,
    # then add the rest of op2.src

    graft.done[mroot1] = new_s
    new_s = graft(op2.src_root())

  graft.allow_new_instrs = False
  #FIXME: this is a temporary patch to avoid having the precondition
  # add new instructions to the source. This should probably be changed
  # to have a separate list, though, to avoid name duplication

  # make a new precondition
  pre1 = graft.subtree(op1.pre)
  pre2 = graft.subtree(op2.pre)
  #FIXME: make sure this does not add new instructions
  
  graft.allow_new_instrs = True

  # gather all the operands defined when creating the src and pre
  src = copy(graft.ids)
  tgt_skip = { r for r,i in src.iteritems() if not isinstance(i, Input) }

  src_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in src.iteritems() if isinstance(i, Instr)])}

  if tgt1_at is not None:
    # if we matched op2.src against a sub-value of op1.tgt,
    # then we will need to graft the modified op2.tgt into op1.tgt
    new_t = graft(op2.tgt[op2.src_root().getName()])
    graft.done[mroot1] = new_t

  # remove the root from graft's list of identifiers, 
  # in order to graft the new tgt
  rname = new_s.getName()
  graft.ids.pop(rname)
  tgt_skip.discard(rname)

  # copy op2.tgt with the root matching the root of new_s
  if tgt1_at is None:
    old_tgt_root = rename_Instr(op2.tgt[op2.src_root().getName()], rname)
  else:
    old_tgt_root = rename_Instr(op1.tgt[op1.src_root().getName()], rname)

  new_t = graft(old_tgt_root)

  tgt = graft.ids
  tgt_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in tgt.iteritems() if isinstance(i, Instr)])}

  if tgt1_at is not None:
    name = '({0}@{2};{1})'.format(op1.name, op2.name, tgt1_at)
  elif src2_at is not None:
    name = '({0};{1}@{2})'.format(op1.name, op2.name, src2_at)
  else:
    name = '({0};{1})'.format(op1.name, op2.name)

  return Transformation(name, mk_PredAnd(pre1,pre2), src_bb, tgt_bb,
    src, tgt, None, None, tgt_skip)

# TODO: remove
def old_compose(op1, op2):
  '''Create a new transformation combining op1 and op2'''
  
  t1 = op1.tgt[op1.src_root().getName()]
  t2 = op2.src_root()
  
  unify = Unifier()
  match = unify(t1,t2)
  
  if not match:
    return None
  
  #print '\ncompose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}
  
  #print '\n-----\nsrc'
  graft = Grafter(unify.vars)
  new_s = graft(op1.src_root())
  
  try:
    #print '\n-----\npre1'
    pre1 = graft.subtree(op1.pre)
  
    #print '\n-----\npre2'
    pre2 = graft.subtree(op2.pre)
  except UnacceptableArgument, e:
    #sys.stderr.write('\nWARNING: caught ' + str(e) + '\n')
    raise

  src = copy(graft.ids)
  tgt_skip = { r for r,i in src.iteritems() if not isinstance(i, Input) }
  
  src_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in src.iteritems() if isinstance(i, Instr)])}
  
  #graft.ids = collections.OrderedDict()
  
  #print '\n-----\ntgt'
  rname = new_s.getName()
  graft.ids.pop(rname)
  tgt_skip.discard(rname)
  
  old_tgt_root = op2.tgt[op2.src_root().getName()]
  
  if old_tgt_root.getName() != op1.src_root().getName():
    old_tgt_root = rename_Instr(old_tgt_root, op1.src_root().getName())
  
  new_t = graft(old_tgt_root)
  tgt = graft.ids
  tgt_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in tgt.iteritems() if isinstance(i, Instr)])}
  
  comp = Transformation(op1.name + ';' + op2.name, mk_PredAnd(pre1,pre2),
    src_bb, tgt_bb, src, tgt, None, None, tgt_skip)
  
  assert comp.src_root() is new_s
  
  
  #print '\n-----'
  #comp.dump()
  
  return comp

def compose_off_first(op1, k, op2):
  '''Attempts to match the root of op1.tgt against register k in op2.src.'''
  
  t1 = op1.tgt[op1.src_root().getName()]
  t2 = op2.src[k]
  
  unify = Unifier()
  match = unify(t1,t2)
  
  if not match:
    return None
    
  #print '\ncompose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}
  
  graft = Grafter(unify.vars)
  new_s = graft(op1.src_root())
  
  graft.done[t2] = new_s
  
  newer_s = graft(op2.src_root())
  
  try:
    # precondition
    pre1 = graft.subtree(op1.pre)
    pre2 = graft.subtree(op2.pre)
  except UnacceptableArgument, e:
    #sys.stderr.write('\nWARNING: caught ' + str(e) + '\n')
    #return None
    raise
  
  src = copy(graft.ids)
  tgt_skip = { r for r,i in src.iteritems() if not isinstance(i, Input) }
  
  src_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in src.iteritems() if isinstance(i, Instr)])}
  
  rname = newer_s.getName()
  graft.ids.pop(rname)
  tgt_skip.discard(rname)
  
  old_tgt_root = rename_Instr(op2.tgt[op2.src_root().getName()], rname)
  
  new_t = graft(old_tgt_root)
  tgt = graft.ids
  tgt_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in tgt.iteritems() if isinstance(i, Instr)])}
  

  comp = Transformation('{0}({1});{2}'.format(op1.name, k, op2.name),
    mk_PredAnd(pre1,pre2), src_bb, tgt_bb, src, tgt, None, None, tgt_skip)
  
  #comp.dump()
  return comp


def compose_off_second(k, op1, op2):
  '''Attempts to match register k of op1.tgt against the root of op2.src.'''
  
  t1 = op1.tgt[k]
  t2 = op2.src_root()
  
  unify = Unifier()
  match = unify(t1,t2)
  
  if not match:
    return None
    
  #print '\ncompose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}
  
  graft = Grafter(unify.vars)
  new_s = graft(op1.src_root())
  
  try:
    # precondition
    pre1 = graft.subtree(op1.pre)
    pre2 = graft.subtree(op2.pre)
  except UnacceptableArgument, e:
    #sys.stderr.write('\nWARNING: caught ' + str(e) + '\n')
    #return None
    raise
  
  src = copy(graft.ids)
  tgt_skip = { r for r,i in src.iteritems() if not isinstance(i, Input) }
  
  src_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in src.iteritems() if isinstance(i, Instr)])}
  
  new_t = graft(op2.tgt[t2.getName()])
  
  #print_prog({'': graft.ids}, set())
  
  rname = new_s.getName()
  graft.ids.pop(rname)
  tgt_skip.discard(rname)
  #tgt_skip = set()
  
  old_src_root = rename_Instr(op1.tgt[op1.src_root().getName()], rname)
  #old_src_root = op1.tgt[op1.src_root().getName()]
  
  graft.done[t1] = new_t  
  
  new_t = graft(old_src_root)
  tgt = graft.ids
  tgt_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in tgt.iteritems() if isinstance(i, Instr)])}
  

  comp = Transformation('{0};({1}){2}'.format(op1.name, k, op2.name),
    mk_PredAnd(pre1,pre2), src_bb, tgt_bb, src, tgt, None, None, tgt_skip)
  
  #comp.dump()
  return comp


def satisfiable(opt):
  '''check whether a transformation's precondition can be satisfied'''
  
  #print '-----'
  #print opt.dump()
  
  for types in opt.type_models():
    #print 'attempting'
    set_ptr_size(types)
    fixupTypes(opt.src, types)
    fixupTypes(opt.tgt, types)
    opt.pre.fixupTypes(types)
    for v in opt.aux: v.fixupTypes(types)
    
    srcv = toSMT(opt.src_bb, opt.src, True)
    tgtv = toSMT(opt.tgt_bb, opt.tgt, False)
    try:
      pre_d, pre = opt.pre.toSMT(srcv)
      # FIXME: this crashes occasionally. why?
    except Exception:
      print 'Threw exception in satisfiable()'
      print 'types', types
      print 'srcv', srcv.vars
      print 'tgtv', tgtv.vars
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
      print 'success:', s.model()
      alive.print_var_vals(s, srcv, tgtv, 'X', types)
      return True
    
  return False
  

def all_bin_compositions(o1, o2, immediate=True):
  #assert o1 is not o2

  try:
    o12 = compose(o1, o2)
    if o12: 
      yield o12
  except Exception, e:
    if immediate: 
      raise
    yield e
  
  regs = [r for r,v in o2.src.iteritems() if isinstance(v,Instr)]
  regs.pop()
  for r in regs:
    try:
      o12 = compose(o1, o2, pattern_at = r)
      if o12: yield o12
    except Exception, e:
      if immediate:
        raise
      yield e
  
  regs = [r for r,v in o1.tgt.iteritems()
            if isinstance(v,Instr) and r not in o1.tgt_skip]
  regs.pop()
  for r in regs:
    try:
      o12 = compose(o1, o2, code_at = r)
      if o12: yield o12
    except Exception, e:
      if immediate:
        raise
      yield e

def old_all_bin_compositions(o1, o2, immediate=True):
  assert o1 is not o2

  try:
    o12 = compose(o1, o2)
    if o12: 
      yield o12
  except Exception, e:
    if immediate: 
      raise
    yield e
  
  regs = [r for r,v in o2.src.iteritems() if isinstance(v,Instr)]
  regs.pop()
  for r in regs:
    try:
      #o12 = compose_off_first(o1, r, o2)
      o12 = compose(o1, o2, src2_at = r)
      if o12: yield o12
    except Exception, e:
      if immediate:
        raise
      yield e
  
  regs = [r for r,v in o1.tgt.iteritems()
            if isinstance(v,Instr) and r not in o1.tgt_skip]
  regs.pop()
  for r in regs:
    try:
      #o12 = compose_off_second(r, o1, o2)
      o12 = compose(o1, o2, tgt1_at = r)
      if o12: yield o12
    except Exception, e:
      if immediate:
        raise
      yield e



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
