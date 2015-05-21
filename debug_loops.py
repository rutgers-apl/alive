from loops import *
import alive
import sys
from pprint import pprint

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

sample_cnst = '''
Name: commute
%r = add C, %v
=>
%r = add %v, C

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
    sys.stderr.write('\rDone: ' + str(proofs))
    #sys.stderr.flush()

  sys.stderr.write('\n')

def test_check_opt(input = sample_nsw):
  opts = parse_transforms(input)
  
  for o in opts:
    o2 = o.copy()
    for oo in all_bin_compositions(o, o2):
      print '\n-----'
      check_opt(oo)

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

  opts = parse_transforms(input)
  if len(opts) == 1:
    opts.append(opts[0].copy(lambda n: n + '99'))
    #opts.append(opts[0].copy())

  c = compose(opts[0], opts[1])
  if c: 
    c.dump()
    

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

def test_matcher(input):
  print
  print 'TEST matcher'
  print '------------'
  print
  opts = parse_transforms(input)
  
  for o1 in opts:
    for o2 in opts:
      if o2 is o1: o2 = o1.copy()
      
      print '======'
      o1.dump()
      o2.dump()
      match = Matcher()
      r = match(o2.src_root(), o1.tgt[o1.src_root().getName()])
      
      print 'matched:', r
      print 'pvars:',
      pprint({dump(k):dump(v) for k,v in match.pvars.iteritems()})
      print 'cvars:',
      pprint({dump(k):dump(v) for k,v in match.cvars.iteritems()})
      print 'equalities:', match.equalities

def test_new_compose_self(sample = None, check_opts = False):
  if sample is None: sample = open('master.opt').read()
  opts = parse_transforms(sample)
  if len(opts) == 1:
    opts.append(opts[0])

  for c in all_bin_compositions(opts[0],opts[1], True):
    c.dump()
    b = satisfiable(c)
    print 'sat:', b
    if check_opts:
      check_opt(c)

    for cc in all_bin_compositions(c,c, True):
      cc.dump()
      b = satisfiable(cc)
      print 'sat:', b
      if check_opts:
        check_opt(cc)


def test_all_uses(input = sample_icmp):
  opts = parse_transforms(input)
  
  print 'Read', len(opts), 'optimizations'
  
  for o in opts:
    print '\n-----'
    o.dump()
    print
    pprint(all_uses(o.src_root()))
    print
    pprint(all_uses(o.tgt_root()))

def main():
  import argparse
  logging.basicConfig(filename='debug_loops.log', filemode='w')
  logging.getLogger('loops.compose').setLevel(logging.DEBUG)
  #logging.getLogger('loops.Grafter').setLevel(logging.INFO)
  parser = argparse.ArgumentParser()
  parser.add_argument('-x', '--compose', action='store_true',
    help='compose the first two transformations')
  parser.add_argument('-s', '--self', action='store_true',
    help='test each transformation for a self-loop')
  parser.add_argument('-c', '--cycle', action='store_true',
    help='test whether the transformations compose into a cycle')
  parser.add_argument('file', type=argparse.FileType('r'), nargs='*',
    default=[sys.stdin], help='optimization file')
  
  args = parser.parse_args()
  
  opts = []
  for f in args.file:
    if f.isatty():
      sys.stderr.write('[Reading from terminal...]\n')
    
    opts += parse_transforms(f.read())
  
  sys.stderr.write('read {} transforms\n'.format(len(opts)))
  
  if args.compose:
    if len(opts) < 2:
      opts.append(opts[0])

    for c in all_bin_compositions(opts[0], opts[1]):
      print '-----'
      c.dump()

  if args.self:
    loops = 0
    for o in opts:
      loop = check_self_loop(o)
      if loop:
        loops += 1
        print 'Loop\n----\n'
        o.dump()
    print 'Loops:', loops

  if args.cycle:
    import debug_sequence
    debug_sequence.compose_sequence(opts)

if __name__ == '__main__':
  main()
