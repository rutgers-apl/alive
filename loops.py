#import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
#from codegen import *
from itertools import combinations, izip, count
#from collections import defaultdict

NAME, PRE, SRC_BB, TGT_BB, SRC, TGT, SRC_USED, TGT_USED, TGT_SKIP = range(9)

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
    else:
      nty = UnknownType()

    nty.types = {}
    nty.myType = ty.myType
    for kind, subtype in ty.types.iteritems():
      nty.types[kind] = copy_type(ty.types[kind])
    
    return nty
  
  assert False

def copy_instr(instr, vars = {}):
  '''Copy the instruction into a new anonymous instruction.
  
  operands will be substituted based on vars
  '''
  from copy import copy
  
  print "copy_instr:", instr
  
  if isinstance(instr, CopyOperand):
    return CopyOperand(vars[instr.v], copy_type(instr.type))
  
  if isinstance(instr, BinOp):
    return BinOp(instr.op, 
      copy_type(instr.type),
      vars[instr.v1],
      vars[instr.v2],
      copy(instr.flags))

  assert False

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
    for k,v in self.src.iteritems():
      new_k = rename(k)
      print 'copy: Value {0} => {1}'.format(k, new_k)
      print '      vars', vars

      if isinstance(v, Input):
        # create a new input
        new_v = Input(new_k, copy_type(v.type))
      
      elif isinstance(v, Instr):
        new_v = copy_instr(v, vars)
        new_v.setName(new_k)
      
      else:
        assert False # no cexprs in source

      vars[v] = new_v
      src[new_k] = new_v
    
    # precondition
    pre = substitute(vars, self.pre)
    
    # target
    tgt = collections.OrderedDict()
    for k,v in self.tgt.iteritems():
      new_k = rename(k)
      print 'copy: Value {0} => {1}'.format(k, new_k)
      if v in vars:
        tgt[new_k] = vars[v]
        continue
        
      if isinstance(v, Input):
        new_v = Input(new_k, copy_type(v.type))
      elif isinstance(v, Instr):
        new_v = copy_instr(v, vars)
        new_v.setName(new_k)
      else:
        new_v = substitute(vars, v)
      
      vars[v] = new_v
      tgt[new_k] = new_v

    
    # source basic blocks
    src_bb = collections.OrderedDict()
    for lab,bb in self.src_bb.iteritems():
      new_bb = collections.OrderedDict()
      for v in bb.itervalues():
        new_v = vars[v]
        new_bb[new_v.getName()] = new_v
      src_bb[lab] = new_bb
    
    # target basic blocks
    tgt_bb = collections.OrderedDict()
    for lab,bb in self.tgt_bb.iteritems():
      new_bb = collections.OrderedDict()
      for v in bb.itervalues():
        new_v = vars[v]
        new_bb[new_v.getName()] = new_v
      tgt_bb[lab] = new_bb

    # target skip list
    tgt_skip = set(rename(k) for k in self.tgt_skip)

    new = Transformation(self.name, pre, src_bb, tgt_bb, src, tgt, None, None, tgt_skip)

    print '----\nOriginal'
    self.dump()
    
    print '----\nNew'
    new.dump()
#     print_prog(src_bb, set())
#     print '=>'
#     print_prog({'': tgt}, set())

    return new

def get_root(src):
  values = src.values()
  root = values.pop()
  while not isinstance(root, Instr):
    root = values.pop()

  return root


def substitute(vars, term):
  '''Replace any instances of the given variables in the provided term.
  
  Returns a tuple saying whether a substitution was made and the new term.
  
  vars is a mapping of Input objects to values
  term is an Input, Constant, or BoolPred
  '''
  # TODO: make sure this is a resonable thing to do
  # NB. should only substitute named constants?
  
  print 'substitute', vars, term
  
  if isinstance(term, Input):
    return vars.get(term, term)
    
  # -- predicates
  if isinstance(term, TruePred):
    return term
  
  if isinstance(term, PredNot):
    return PredNot(substitute(vars, term.v))
    
  if isinstance(term, PredAnd):
    vs = (substitute(vars, v) for v in term.args)
    return PredAnd(*vs)
  
  if isinstance(term, PredOr):
    vs = (substitute(vars, v) for v in term.args)
    return PredOr(*vs)
  
  if isinstance(term, BinaryBoolPred):
    return BinaryBoolPred(term.op, substitute(vars, term.v1), substitute(vars, term.v2))
  
  if isinstance(term, LLVMBoolPred):
    return LLVMBoolPred(term.op, [substitute(vars, v) for v in term.args])
    
  # -- constant exprs
  if isinstance(term, ConstantVal):
    return term
  
  if isinstance(term, UndefVal):
    return term
  
  if isinstance(term, CnstUnaryOp):
    return CnstUnaryOp(term.op, substitute(vars, term.v))
  
  if isinstance(term, CnstBinaryOp):
    return CnstBinaryOp(term.op, substitute(vars, term.v1), substitute(vars, term.v2))
  
  if isinstance(term, CnstFunction):
    return CnstFunction(term.op, [substitute(vars, v) for v in term.args], term.type)
    #TODO: is this correct?
  
  assert False # should not be called on instructions

def unify_inputs(vars, var, inst):
  '''Notes that the var refers to the inst in the supplied vars.

  Returns false if the var already refers to something else.
  '''
  #NB. assumes 1-1 mapping of objects to identifiers
  #TODO. don't match constant inputs to instructions
  assert isinstance(var, Input)

  if var not in vars:
    # FIXME: come up with a better way to recursively replace
    if var.name[0] == 'C':
      new = {var: inst}
      for k,v in vars.iteritems():
        vars[k] = substitute(new, v)
    
    vars[var] = inst

    return True
  
  return vars[var] is inst


def unify_inst_tree(vars, i1, i2):
  '''Returns whether i1 and i2 have compatible (the same) shapes. 
  
  Modifies vars to indicate matched input values.
  '''
  # TODO: collect type info?
  
  print "unify_inst_tree", vars, i1, i2
  
  if isinstance(i1, Input):
    return unify_inputs(vars, i1, i2)
  
  if isinstance(i2, Input):
    return unify_inputs(vars, i2, i1)
  
  if i1.__class__ != i2.__class__:
    return False
  
  if isinstance(i1, BinOp):
    return (i1.op == i2.op) and \
      unify_inst_tree(vars, i1.v1, i2.v1) and \
      unify_inst_tree(vars, i1.v2, i2.v2)
  
  assert False # other opcodes not yet supported

def substitute_instr_tree(val, subst, ids, done = {}):
  '''Recursively create a copy of val, with substitution of inputs according
  to subst. Returns new value and modifies ids.
  
  ids: name => value (i.e., the new src or tgt). includes all subvalues
  done: old_value => new_value
  '''
  from copy import copy
  
  #print 'substitute_instr_tree:', val, subst, ids, done
  
  if val in done:
    if done[val].getName() not in ids:
      ids[done[val].getName()] = done[val]
    return done[val]
  
  if isinstance(val, Input):
    if val in subst:
      new_val = substitute_instr_tree(subst[val], subst, ids, done)
    else:
      new_val = Input(val.name + '_new', copy_type(val.type))
  
  elif isinstance(val, BinOp):
    v1 = substitute_instr_tree(val.v1, subst, ids, done)
    v2 = substitute_instr_tree(val.v2, subst, ids, done)
    new_val = BinOp(val.op, copy_type(val.type), v1, v2, copy(val.flags))
    new_val.setName(val.getName() + '_new')
  
  else:
    assert False
  
  done[val] = new_val
  ids[new_val.getName()] = new_val    
  return new_val
  


def compose(op1, op2, k):
  '''Create a new transformation combining op1 and op2, matching k in op1
  to the root of op2. Return None if not possible.
  '''
  from copy import copy
  
  if isinstance(k, Value): k = k.getName()
  
  #FIXME: this only works if k is the root of o2
  
  r1 = op1.tgt[k]
  r2 = op2.src_root()
  
  print 'matching {0} <= {1}'.format(r1.getName(), r2)
  
  vars = {}
  if not unify_inst_tree(vars, r1, r2):
    return None

  print 'compose: found match', vars
  
  # at this point, vars maps original src/tgt inputs to src/tgt values
  # it should have these invariants
  #   1. no key occurs anywhere in the values (ie., this is a trans. closure)
  #   2. named constants (C?) should map to constant exprs
  # FIXME: make sure inv. 2 actually holds

  #for k,v in op1.src.iteritems():
  #  print '{0} = {1}; {2}'.format(k,v,vars.get(v,None))
  
  src = collections.OrderedDict()
  done = {}
  new_src_root = substitute_instr_tree(op1.src_root(), vars, src, done)
  
  tgt = collections.OrderedDict()
  # copy src values not in target...?
  
  # FIXME: rename the tgt root to match the src root
  tgt_root = op2.tgt[op2.src_root().getName()]
  graft = substitute_instr_tree(tgt_root, vars, tgt, done)
  
  assert r1 not in done
  done[r1] = graft
  
  tgt1_root = op1.tgt[op1.src_root().getName()]
  if tgt1_root in done:
    new_tgt_root = copy_instr(tgt_root, done)
    new_tgt_root.setName(new_src_root.getName())
    del tgt[graft.getName()]
    tgt[new_tgt_root.getName()] = new_tgt_root
    
  else:
    new_tgt_root = substitute_instr_tree(tgt1_root, vars, tgt, done)

  assert new_tgt_root.getName() == new_src_root.getName()
  

  '''
  print 'bad: ', bad.getName(), '=', bad
  
  good = copy_instr(op1.tgt[k], done)
  good.setName(new_src_root.getName())
  print 'good: ', good.getName(), '=', good

  del tgt[bad.getName()]
  tgt[good.getName()] = good
  done[tgt_root] = good
  '''

  '''
  assert r1 not in done
  good = copy_instr(r2, done)
  good.setName(done[op1.src_root()].getName())
  del tgt[bad.getName()]
  done[r1] = good
  tgt[good.getName()] = good
  '''
  
  
  print 'new_src:'
  print_prog({'': src}, set())
  print '=>:'
  print_prog({'': tgt}, set())
  print
  from pprint import pprint
  #pprint({k:hash(v) for k,v in src.iteritems()})
  #pprint({k:hash(v) for k,v in tgt.iteritems()})
  pprint(vars)
  pprint(done)
  


'''
  # create a new mapping from original src/tgt to new values
  vals = {}
  for k,v in vars:
    if isinstance(v, Input):
      vals[k] = Input(v.name, copy_type(v.type)) 
      # FIXME: handle multiple occurrences of same input
    elif isinstance(v, Constant):
      vals[k] = substitute(v, vals)


  src = collections.OrderedDict()
  vals = 
  for k,v in op1.src:
    v = vars[v]

    elif isinstance(v, Input):
      new_v = Input(v.name, copy_type(v.type))
    elif isinstance(v, Instr):
      new_v = copy_instr(v, vals)
    else:
      assert False # no cexprs in source
    
    vals[v] = 
'''

def is_composable(op1, op2):
  #tgt1 = op1[TGT]
  #src2 = op2[SRC]
  
  r1 = op1.src_root()
  r2 = op2.tgt[op2.src_root().getName()]

  vars = {}
  b = unify_inst_tree(vars, r1, r2)
  print 'vars:', vars

  # quick exit if the patterns don't match
  if not b:
    return False
  
  p1 = substitute(vars, op1.pre)
  p2 = substitute(vars, op2.pre)
  
  pre = PredAnd(p1, p2)
  
  print pre

  # pick a good type
  # NB. this only tests at one typing
  #     should it actually try every possible typing?

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

  


if __name__ == '__main__':
  sys.stderr.write("[Reading from stdin...]\n")
  #input = sys.stdin.read()
  input = '''
Pre: C1&C2 != C1
%op = or %X, C1
%r = and %op, C2
  =>
%o = or %X, C1&C2
%r = and %o, C2
'''
  input = '''
%y = add %b,%c
%z = add %a,%y
=>
%x = add %a,%b
%z = add %x,%c
'''

  opts = [Transformation(*o) for o in parse_opt_file(input)]
  
  
  print "read {0} opt(s)".format(len(opts))
  
  compose(opts[0], opts[0].copy(lambda n: n + '.1'), '%x')
  
''' 
  print '-----'
  r = is_composable(opts[0], opts[0].copy(lambda n: n + '.1'))
  print '=>', r
'''
'''  
  for o1, o2 in combinations(opts, 2):
    print '----------'
    print 'checking {0} and {1}'.format(o1.name, o2.name)
    r = is_composable(o1, o2)
    print '=>', r
'''