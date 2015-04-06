#import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
#from codegen import *
from itertools import combinations, izip, count
#from collections import defaultdict
from copy import copy

NAME, PRE, SRC_BB, TGT_BB, SRC, TGT, SRC_USED, TGT_USED, TGT_SKIP = range(9)


def dump(instr):
  if isinstance(instr, Instr) and hasattr(instr, 'name'):
    return '<{0}|{1}>#{2}'.format(instr.getName(), instr, id(instr))

  return '<{0}>#{1}'.format(instr, id(instr))

class Visitor(object):
  def default(self, v):
    raise AliveError('{1}: No default behavior for <{0}>'.format(v,
      type(self).__name__))
    
  def __getattr__(self, name):
    if name.startswith('visit_'):
      return lambda v: self.default(v)
    
    raise AttributeError


def base_visit(obj, visitor):
  return getattr(visitor, 'visit_' + obj.__class__.__name__)(obj)

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
    return Icmp(term.op, copy_type(term.type), self.operand(term.v1),
                self.operand(term.v2))

  def visit_Select(self, term):
    return Select(copy_type(term.type), self.operand(term.c),
                  self.operand(term.v1), self.operand(term.v2))

  # -- constants
  def visit_ConstantVal(self, val):
    return ConstantVal(val.val, copy_type(val.type))
  
  def visit_UndefVal(self, val):
    return UndefVal(copy_type(val.type))
  
  def visit_CnstUnaryOp(self, val):
    return CnstUnaryOp(val.op, self.subtree(val.v))
  
  def visit_CnstBinaryOp(self, val):
    return CnstBinaryOp(val.op, self.subtree(val.v1), self.subtree(val.v2))
  
  def visit_CnstFunction(self, val):
    return CnstFunction(val.op, [self.subtree(a) for a in val.args], 
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
    return LLVMBoolPred(term.op, [self.operand(a) for a in term.args])



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
    sys.stderr.write('WARNING: not copying array type {0}\n'.format(ty))
    # FIXME: handle ArrayType better
    return ArrayType()
  
  assert False

# ----

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

  def dump(self):
    print 'Name:', self.name
    print 'Pre:', str(self.pre)
    print_prog(self.src_bb, set())
    print '=>'
    print_prog(self.tgt_bb, self.tgt_skip)
    print
    print 'src', self.src
    print 'tgt', self.tgt
    print 'src_used', self.src_used
    print 'tgt_used', self.tgt_used
    print 'tgt_skip', self.tgt_skip
  
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

# ----

class Unifier(Visitor):
  def __init__(self, vars = None):
    if vars == None: vars = {}

    self.vars = vars
    self.t2 = None
  
  def unify(self, var, term):
    print 'unify', var, term
    if var in self.vars:
      return self(self.vars[var], term)
    
    print '.. {0} := {1}'.format(dump(var),dump(term))
    self.vars[var] = term
    return True
    
  def __call__(self, t1, t2):
    print 'Unifier({0})({1}, {2})'.format(self.vars, dump(t1), dump(t2))
    if isinstance(t1, Input):
      return self.unify(t1, t2)
    
    if isinstance(t2, Input):
      return self.unify(t2, t1)
    
    if t1.__class__ is not t2.__class__:
      return False
    
    old_t2 = self.t2
    self.t2 = t2
    r = t1.visit(self)
    if r:
      self.vars[t2] = t1
      print '.. {0} := {1}'.format(dump(t2),dump(t1))
    self.t2 = old_t2
    return r
  
  def visit_BinOp(self, t1):
    # FIXME: handle flags
    t2 = self.t2
    return t1.op == t2.op and self(t1.v1,t2.v1) and self(t1.v2,t2.v2)

  def default(self, t1):
    return False


class Grafter(CopyBase):
  '''Make a new instruction tree with operand identifier map, substituting
  inputs according to the provided table.'''
  
  def __init__(self, vars = None):
    if vars == None: vars = {}

    self.vars = vars  # old value -> old value
    self.done = {}    # old value -> new value
    self.ids = collections.OrderedDict()  # name -> new value
    self.depth = 0
  
  def __call__(self, term):
    return self.operand(term)
  
  def subtree(self, term):
    print '.' * self.depth,
    print 'subtree:', dump(term), 'Done', term in self.done, 'Var', term in self.vars
    
    if term in self.done:
      return self.done[term]

    # check whether this term was unified
    if term in self.vars:
      print '.' * self.depth,
      print '.. substitute', dump(term), ':=', dump(self.vars[term])
      #term = self.vars[term]
      return self.subtree(self.vars[term])
  
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
    
    print '.' * self.depth,
    print 'subtree <=', dump(self.done[term])
    
    return self.done[term]
  
  def operand(self, term):
    #print 'operand:', dump(term)
    new_term = self.subtree(term)

    name = new_term.getUniqueName()
    if name not in self.ids:
      #print '.. ids[{0}] = {1}'.format(name, dump(new_term))
      self.ids[name] = new_term
    
    return new_term

  def visit_Input(self, term):
    print 'visit_Input', dump(term), '=>', self.vars.get(term, None)

    if term in self.vars:
      return self.subtree(self.vars[term])
    
    # this is a new input, so we need a fresh name
    name = term.getName()
    while name in self.ids:
      name += '0'
      # TODO: improve

    new_term = Input(name, copy_type(term.type))
    self.ids[name] = new_term
    return new_term


def mk_PredAnd(p1,p2):
  if isinstance(p1, TruePred):
    return p2
  if isinstance(p2, TruePred):
    return p1
  return PredAnd(p1,p2)

def compose(op1, op2):
  '''Create a new transformation combining op1 and op2'''
  
  t1 = op1.tgt[op1.src_root().getName()]
  t2 = op2.src_root()
  
  unify = Unifier()
  match = unify(t1,t2)
  
  if not match:
    return None
  
  print '\ncompose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}
  
  print '\n-----\nsrc'
  graft = Grafter(unify.vars)
  new_s = graft(op1.src_root())
  
  print '\n-----\npre1'
  pre1 = graft.subtree(op1.pre)
  
  print '\n-----\npre2'
  pre2 = graft.subtree(op2.pre)

  src = copy(graft.ids)
  tgt_skip = { r for r,i in src.iteritems() if not isinstance(i, Input) }
  
  src_bb = {'': collections.OrderedDict(
    [(r,i) for r,i in src.iteritems() if isinstance(i, Instr)])}
  
  #graft.ids = collections.OrderedDict()
  
  print '\n-----\ntgt'
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
    
  print '\ncompose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}
  
  graft = Grafter(unify.vars)
  new_s = graft(op1.src_root())
  
  graft.done[t2] = new_s
  
  newer_s = graft(op2.src_root())
  
  # precondition
  pre1 = graft.subtree(op1.pre)
  pre2 = graft.subtree(op2.pre)
  
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
    
  print '\ncompose: matched', {dump(k):dump(v) for k,v in unify.vars.iteritems()}
  
  graft = Grafter(unify.vars)
  new_s = graft(op1.src_root())
  
  # precondition
  pre1 = graft.subtree(op1.pre)
  pre2 = graft.subtree(op2.pre)
  
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
  
  pre = opt.pre
  
  s = SolverFor('QF_LIA')
  s.add(pre.getTypeConstraints())
  if s.check() != sat:
    raise Exception("Cannot satisfy precondition type constraints")
  
  types = s.model()
  pre.fixupTypes(types)
  
  # check whether precondition can be satisfied
  pre_d, pre_b = pre.toSMT(None) # FIXME
  
  ps = SolverFor('QF_LIA')
  ps.add(pre_d)
  ps.add(pre_b)
  
  print 'ps', ps
  
  ch = ps.check()
  print 'ch', ch
  
  if ch == sat:
    print 'model', ps.model()
  
  return ch == sat


def all_bin_compositions(o1, o2):
  assert o1 is not o2

  o12 = compose(o1, o2)
  if o12: 
    yield o12
  
  regs = [r for r,v in o2.src.iteritems() if isinstance(v,Instr)]
  regs.pop()
  for r in regs:
    o12 = compose_off_first(o1, r, o2)
    if o12: yield o12
  
  regs = [r for r,v in o1.tgt.iteritems()
            if isinstance(v,Instr) and r not in o1.tgt_skip]
  regs.pop()
  for r in regs:
    o12 = compose_off_second(r, o1, o2)
    if o12: yield o12



def all_compositions(opts):
  for o1 in opts:
    for o2 in opts:
      # make sure we don't compose the same thing
      if o1 is o2: o2 = o1.copy()
      
      for o12 in all_bin_compositions(o1,o2):
        yield o12


def check_self_loop(opt):
  '''Check all satisfiable self-compositions.'''
  
  o2 = opt.copy()
  for oo in all_bin_compositions(opt, o2):
    print '\n-----\n', oo.name
    try:
      if satisfiable(oo):
        oo.dump()
    except Exception, e:
      print 'Caught', e


# -----

sample = '''
Pre: C1&C2 != C1
%op = or %X, C1
%r = and %op, C2
  =>
%o = or %X, C1&C2
%r = and %o, C2
'''

sample_add = '''
%y = add %b,%c
%z = add %a,%y
=>
%x = add %a,%b
%z = add %x,%c
'''

sample_cadd = '''
%a = add %x, C1
%z = add %a, C2
=>
%z = add %x, C1+C2
'''

sample_nonlinear = '''
Name: commute add
%y = add %b, %c
%z = add %a, %y
=>
%x = add %a, %b
%z = add %x, %c

Name: add->shl
%x = add %a, %a
=>
%x = shl %a, 1
'''

sample_selfloop = '''
Pre: isPowerOf2(%A) && hasOneUse(%Y)
%Y = lshr %A, %B
%r = udiv %X, %Y
  =>
%Y = lshr exact %A, %B
%r = udiv %X, %Y
'''

def parse_transforms(input):
  return [Transformation(*o) for o in parse_opt_file(input)]

def test_is_composable(input):
  opts = [Transformation(*o) for o in parse_opt_file(input)]
  print
  print 'TEST is_composable'
  print '------------------'
  print

  for o1, o2 in combinations(opts, 2):
    print '----------'
    print 'checking {0} and {1}'.format(o1.name, o2.name)
    r = is_composable(o1, o2)
    print '=>', r
  
def test_copy(input = sample):
  print
  print 'TEST copy'
  print '---------'
  print
  opts = [Transformation(*o) for o in parse_opt_file(input)]
  
  for o in opts:
    print
    print '----------'
    o.copy(lambda n: n + '.1').dump()
  
def test_compose_self(input = sample_add):
  print
  print 'TEST compose_self'
  print '-----------------'
  print

  opts = [Transformation(*o) for o in parse_opt_file(input)]
  
  o1 = opts[0]
  #o2 = o1.copy(lambda n: n + '.1')
  o2 = o1.copy()
  
  print '\nOriginal'
  o1.dump()
  print '\nCopy'
  o2.dump()
  
  compose(o1, o2)
  
def test_unify(input = sample_nonlinear):
  print
  print 'TEST unify'
  print '-----------------'
  print

  opts = [Transformation(*o) for o in parse_opt_file(input)]
  if len(opts) == 1:
    opts.append(opts[0].copy()) #lambda n: n + '._1'))
  
  t1 = opts[0].tgt[opts[0].src_root().getName()]
  t2 = opts[1].src_root()

  unify = Unifier({})
  print 'Unifies:', unify(t1,t2)
  print 'Vars:', unify.vars

def test_new_compose(input = sample_nonlinear):
  print
  print 'TEST new_compose'
  print '----------------'
  print

  opts = [Transformation(*o) for o in parse_opt_file(input)]
  if len(opts) == 1:
    #opts.append(opts[0].copy(lambda n: n + '_1'))
    opts.append(opts[0].copy())

  c = compose(opts[0], opts[1])
  if c: 
    c.dump()

def test_compose_off_first(input = sample_add):
  print
  print 'TEST compose_off_first'
  print '----------------------'
  print
  opts = parse_transforms(input)
  
  if len(opts) == 1:
    opts.append(opts[0].copy()) #lambda n: n + '.1'))
  
  o1 = opts[0]
  o2 = opts[1]
  
  regs = [k for k,v in o2.src.iteritems() if isinstance(v, Instr)]
  
  print 'composing', o1.name, o2.name
  o1.dump()
  o2.dump()
  
  for r in regs:
    print '\n-----\ncompose at', r
    compose_off_first(o1, r, o2)

def test_compose_off_second(input = sample_add):
  print
  print 'TEST compose_off_second'
  print '----------------------'
  print
  opts = parse_transforms(input)
  
  if len(opts) == 1:
    opts.append(opts[0].copy()) #lambda n: n + '.1'))
  
  o1 = opts[0]
  o2 = opts[1]
  
  regs = [k for k,v in o1.tgt.iteritems() 
            if isinstance(v, Instr) and k not in o1.tgt_skip]
  
  regs.pop()
  
  print 'composing', o1.name, o2.name
  o1.dump()
  o2.dump()
  
  for r in regs:
    print '\n-----\ncompose at', r
    compose_off_second(r, o1, o2)

def test_all_comps(input = sample_nonlinear):
  print
  print 'TEST all_comps'
  print '----------------------'
  print
  opts = parse_transforms(input)
  
  for c in all_compositions(opts):
    print '\n-----'
    c.dump()

def test_satisfiable(input = sample):
  print
  print 'TEST satisfiable'
  print '----------------------'
  print
  opts = parse_transforms(input)

  for c in all_compositions(opts):
    print '\n-----'
    if satisfiable(c):
      c.dump()

def test_self_loops(input = sample):
  print
  print 'TEST self_loops'
  print '----------------------'
  print
  opts = parse_transforms(input)

  for o in opts:
    check_self_loop(o)

if __name__ == '__main__':
  #sys.stderr.write("[Reading from stdin...]\n")
  #test_is_composable(sys.stdin.read())
  
  #test_is_composable(sample_nonlinear)
  
  #test_copy(sys.stdin.read())
  #test_compose_self(sample_cadd)
  #test_unify(sample)

  #test_new_compose(sample)
  #test_new_compose(sample_add)
  #test_new_compose(sample_cadd)
  #test_new_compose(sample_nonlinear)
  test_all_comps(sample_selfloop)
  #test_self_loops(sample_selfloop)