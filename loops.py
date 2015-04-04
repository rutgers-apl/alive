#import argparse, glob, re, sys
from language import *
from precondition import *
from parser import parse_opt_file
#from codegen import *
from itertools import combinations, izip, count
#from collections import defaultdict

NAME, PRE, SRC_BB, TGT_BB, SRC, TGT, SRC_USED, TGT_USED, TGT_SKIP = range(9)

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
  term is an Instr or BoolPred
  '''
  # TODO: make sure this is a resonable thing to do
  # NB. should only substitute named constants?
  
  print 'substitute', vars, term
  
  if isinstance(term, Input):
    return vars.get(term, term)
  
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



def is_composable(op1, op2):
  #tgt1 = op1[TGT]
  #src2 = op2[SRC]
  
  r1 = get_root(op1[TGT])
  r2 = get_root(op2[SRC])
  vars = {}
  b = unify_inst_tree(vars, r1, r2)
  print 'vars:', vars

  # quick exit if the patterns don't match
  if not b:
    return False
  
  p1 = substitute(vars, op1[PRE])
  p2 = substitute(vars, op2[PRE])
  
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
  input = sys.stdin.read()
  opts = parse_opt_file(input)
  
  print "read {0} opt(s)".format(len(opts))
  
  #r = is_composable(opts[0], opts[1])
  #print "is_composable:", r
  
  for o1, o2 in combinations(opts, 2):
    print '----------'
    print 'checking {0} and {1}'.format(o1[NAME], o2[NAME])
    r = is_composable(o1, o2)
    print '=>', r
