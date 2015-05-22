#!/usr/bin/env python
import loops, alive
import os, sys, re, logging, argparse, itertools

def compose_sequence(opts, up_to=None):
  'Yield all compositions of the sequence opts[0:up_to].'
  up_to = len(opts) if up_to is None else up_to

  if up_to < 1:
    raise AliveError('compose_sequence: index out of range')

  if up_to == 1:
    yield opts[0]
  else:
    n = up_to - 1
    for o in compose_sequence(opts, up_to=n):
      for o2 in loops.all_bin_compositions(o, opts[n], immediate=False):
        yield o2

def verify_opt(opt, quiet=True):
  logger = logging.getLogger('test_loops.verify')
  logger.info('checking %s', opt.name)

  if not quiet:
    opt.dump()

  users_count = alive.countUsers(opt.src_bb)
  users = {}
  for k in opt.src.iterkeys():
    n_users = users_count.get(k)
    users[k] = [alive.get_users_var(k) != n_users] if n_users else []

  proofs = 0
  for types in opt.type_models():
    alive.set_ptr_size(types)
    alive.fixupTypes(opt.src, types)
    alive.fixupTypes(opt.tgt, types)
    opt.pre.fixupTypes(types)

    alive.check_typed_opt(opt.pre, opt.src_bb, opt.src, opt.tgt_bb, opt.tgt,
      types, users)
    proofs += 1
    if not quiet:
      sys.stderr.write('\rDone: ' + str(proofs))

  if not quiet:
    sys.stderr.write('\n')


def test_composition(opts, name='anon', verify=False, quiet=True):
  '''
  Attempt to merge the sequence of optimizations into a single one.
  '''
  logger = logging.getLogger('test_loops.test_composition')
  logger.info('%s: composing %s opts', name, len(opts))
  count = 0
  
  for o in compose_sequence(opts):
    if verify:
      verify_opt(o, quiet)

    count += 1
    logger.info('%s: Successful composition\n%s', name, o)
  
  logger.info('%s: %s compositions', name, count)
  return count

def count_src(o):
  return sum(1 for v in o.src.itervalues() if isinstance(v, loops.Instr))

def test_loop(opts, name='anon', verify=False, quiet=True):
  '''
  Determine whether this sequence of optimizations loops.
  '''
  logger = logging.getLogger('test_loops.test_loop')
  logger.info('%s: checking for %s-cycle', name, len(opts))
  
  for o in compose_sequence(opts):
    if verify:
      verify_opt(o, quiet)

    o_src = count_src(o)
    for oo in loops.all_bin_compositions(o, o, immediate=False):
      if verify:
        verify_opt(oo, quiet)

      oo_src = count_src(oo)

      if oo_src > o_src:
        logger.info('%s increases: %s -> %s', o.name, o_src, oo_src)
        continue

      if loops.satisfiable(oo):
        logger.info('%s satisfiable')
        return True

    return False

def run_tests(verify=False):
  logger = logging.getLogger('test_loops')

  complete = 0
  failed = 0
  errors = 0
  test_names = filter(lambda f: not f.startswith('unknown'),
                      os.listdir('looptests'))
  tests = len(test_names)
  sys.stderr.write(str(tests) + ' tests\n')

  label = re.compile(r'^; expect (\d+) (comp|loop)')

  def statusmsg():
    sys.stderr.write(
      '\r{}% complete, {} failed, {} errors'.format(
        complete*100/tests, failed, errors))

  for f in test_names:
    logger.info('reading looptests/%s', f)
    statusmsg()
    complete += 1

    text = open('looptests/' + f).read()
    expects = label.match(text)

    if not expects:
      logger.warning('%s: no expectations', f)
      errors += 1
      continue

    expected = int(expects.group(1))
    expecting = expects.group(2)

    opts = loops.parse_transforms(text)

    try:
      if expecting == 'comp':
        if test_composition(opts, f, verify=verify) != expected:
          logger.warning('%s: Got %r comps, expected %r',
                         f, comps, expected_comps)
          failed += 1
        continue

      if expecting == 'loop':
        got = test_loop(opts, f, verify=verify)
        if got and not expected:
          logger.warning('%s: Unexpected loop', f)
          failed += 1
        elif not got and expected:
          logger.warning('%s: Expected loop', f)
          failed += 1

    except Exception as e:
      logger.exception('Got %r while testing %s', e, f)
      errors += 1

  statusmsg()
  return not failed and not errors



def main():
  logging.basicConfig(filename='test_loops.log', filemode='w')
  logger = logging.getLogger('test_loops')
  logger.setLevel(logging.INFO)
  logging.getLogger('loops.compose').setLevel(logging.INFO)

  parser = argparse.ArgumentParser()
  parser.add_argument('-t', '--tests', action='store_true',
    help='run the test suite')
  parser.add_argument('-c', '--compose', action='append',
    type=argparse.FileType('r'), default=[], nargs='*',
    metavar='file',
    help='count how many ways this file can be composed into a single opt')
  parser.add_argument('-l', '--loop', action='append', 
    type=argparse.FileType('r'), default=[], nargs='*',
    metavar='file',
    help='check whether each file describes a cycle')
  parser.add_argument('-v', '--verify', action='store_true',
    help='if present, verify all composed optimizations')
  parser.add_argument('--log', action='append', nargs=2,
    metavar=('logger', 'level'),
    help='set the logging threshold for a logging subtree')

  args = parser.parse_args()

  if args.log:
    for tree,level in args.log:
      level = level.upper()
      try:
        logging.getLogger(tree).setLevel(getattr(logging, level))
        logger.info('logging %s at %s', tree, level)
      except AttributeError:
        sys.stderr.write('{} is not a valid logging level\n'.format(level))
        sys.stderr.write('Use: DEBUG, INFO, WARNING, ERROR, CRITICAL\n')
        exit(-1)

  for f in itertools.chain.from_iterable(args.compose):
    opts = loops.parse_transforms(f.read())
    comps = test_composition(opts, f, verify=args.verify, quiet=False)
    print '{}: got {} composition{}'.format(f.name, comps,
      '' if comps == 1 else 's')
  
  for f in itertools.chain.from_iterable(args.loop):
    opts = loops.parse_transforms(f.read())
    loop =  test_loop(opts, f.name, verify=args.verify, quiet=False)
    print '{}: {}loop'.format(f.name, '' if loop else 'no ')

  if args.tests or not (args.compose or args.loop):
    if not run_tests(verify=args.verify):
      exit(1)

if __name__ == '__main__':
  main()
