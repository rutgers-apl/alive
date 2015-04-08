from loops import *
import alive
import sys

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

sample_icmp = '''Name: icmp + zext
%1 = icmp %n, %a
%2 = zext %1 to i32
%3 = icmp %n, %b
%4 = zext %3 to i32
%5 = or %2, %4
%6 = icmp eq %5, 0
  =>
%. = or %1, %3
%6 = icmp eq %., 0
'''

sample_nsw = '''Name: AddSub:1334
Pre: WillNotOverflowSignedAdd(%lhs, %rhs)
%r = add %lhs, %rhs
  =>
%r = add nsw %lhs, %rhs
'''

sample_cnst = '''Name: commute
%r = add C, %a
=>
%r = add %a, C

Name: assoc
%x = add %b, %c
%z = add %a, %x
=>
%y = add %a, %b
%z = add %y, %c
'''

def check_opt(opt):
  opt.dump()
  print

  users_count = alive.countUsers(opt.src_bb)
  users = {}
  for k in opt.src.iterkeys():
    n_users = users_count.get(k)
    users[k] = [alive.get_users_var(k) != n_users] if n_users else []

  proofs = 0
  for types in opt.type_models():
    set_ptr_size(types)
    fixupTypes(opt.src, types)
    fixupTypes(opt.tgt, types)
    opt.pre.fixupTypes(types)

    alive.check_typed_opt(opt.pre, opt.src_bb, opt.src, opt.tgt_bb, opt.tgt, 
      types, users)
    proofs += 1
    sys.stdout.write('\rDone: ' + str(proofs))
    sys.stdout.flush()
  
  print

def test_check_opt(input = sample_nsw):
  opts = parse_transforms(input)
  
  for o in opts:
    o2 = o.copy()
    for oo in all_bin_compositions(o, o2):
      print '\n-----'
      check_opt(oo)

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
    try:
      check_self_loop(o)
    except Exception, e:
      print o.name, ': CAUGHT', e

def test_type_models(input = sample):
  print
  print 'TEST type_models'
  print '----------------------'
  print
  opts = parse_transforms(input)
  
  for m in opts[0].type_models():
    print '-----'
    print m


if __name__ == '__main__':
  #test_check_opt()
  test_all_comps(sample_cnst)