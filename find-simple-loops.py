#!/usr/bin/env python
import loops
import argparse, logging, itertools, sys, os, json
import gc
import logging.config

def _search_after(opts, n, i, o, oz, on_error=None):
  if n < 1:
    yield (o,tuple(opts[j] for j in oz))
    return

  for j in range(i,len(opts)):
    if j in oz:
      continue

    os = oz + (j,)
    for c in loops.all_bin_compositions(o, opts[j], on_error):
      for r in _search_after(opts, n-1, i, c, os, on_error):
        yield r


def search_after_prefix(opts, n, prefix_idxs, on_error=None):
  prefix = tuple(opts[p] for p in prefix_idxs)
  i = prefix_idxs[0]

  if n == 0:
    for p in loops.all_compositions(prefix):
      yield (p, prefix)
    return

  for p in loops.all_compositions(prefix):
    for r in _search_after(opts, n, i, p, prefix_idxs, on_error):
      yield r


def search(opts, n, on_error=None):
  'Generate candidate n-cycles'
  if n == 1:
    for i1,o in itertools.izip(itertools.count(), opts):
      yield (o,(o,))
    return

  for i in range(0, len(opts)):
    os = (i,)
    for r in _search_after(opts, n-1, i+1, opts[i], os, on_error):
      yield r

status = '\rTested: {} SatChecks: {} Loops: {}'

def count_src(o):
  return sum(1 for v in o.src.itervalues() if isinstance(v, loops.Instr))

def main():
  logging.basicConfig(filename='find-simple-loops.log', #filemode='w',
    format='%(asctime)s - %(levelname)s - %(name)s - %(message)s')
  logger = logging.getLogger('find-simple-loops')
  logger.setLevel(logging.INFO)

  parser = argparse.ArgumentParser()
  parser.add_argument('length', type=int,
    help='Length of cycles to search for')
  parser.add_argument('file', type=argparse.FileType('r'),
    help='optimization suite to analyze')
  parser.add_argument('-q', '--quiet', action='store_true',
    help='Suppress status updates')
  parser.add_argument('--prefix', type=str,
    help='Common prefix as comma-separated list of indices')

  args = parser.parse_args()

  if args.length < 1:
    sys.stderr.write('cycle length must be positive\n')
    exit(1)

  logger.info('Searching %s for %s-cycles', args.file.name, args.length)
  if not args.quiet:
    sys.stderr.write('Reading ' + args.file.name + '\n')
  
  opts = loops.parse_transforms(args.file.read())
  
  logger.info('%s optimizations', len(opts))
  if not args.quiet:
    sys.stderr.write('{} optimizations'.format(len(opts)))

  count = 0
  sat_checks = 0
  cycles = 0
  errors = [0]
  
  def count_error(e,o1,o2):
    errors[0] += 1
  
  if args.prefix:
    prefix_idxs = tuple(int(i) for i in args.prefix.split(','))
    logger.info('Using prefix %s', prefix_idxs)
    candidates = search_after_prefix(opts, args.length, prefix_idxs, count_error)
  else:
    candidates = search(opts, args.length, count_error)

  for o,os in candidates:
    o_src = count_src(o)
    for oo in loops.all_bin_compositions(o, o, count_error):
      if count % 1000 == 0:
        logger.info('Tested %s SatChecks %s Loops %s Errors %s',
          count, sat_checks, cycles, errors[0])
      
      if count % 10000 == 0 and logger.isEnabledFor(logging.INFO):
        gc.collect()
        logger.info('Live objects %s; Uncollectable %s', len(gc.get_objects()), len(gc.garbage))

      if not args.quiet:
        sys.stderr.write(status.format(count, sat_checks, cycles))
      count += 1

      oo_src = count_src(oo)

      if o_src < oo_src:
        continue

      sat_checks += 1
      if not loops.satisfiable(oo):
        continue

      cycles += 1
      print '\n-----\nLoop: ', o.name
      for opt in os:
        opt.dump()
        print
      o.dump()
  
  if not args.quiet:
    sys.stderr.write(status.format(count, sat_checks, cycles))
    sys.stderr.write('\n')

  print
  print 'final count', count
  print 'loops', cycles
  print 'sat_checks', sat_checks
  print 'errors', errors[0]
  
  if logger.isEnabledFor(logging.INFO):
    logger.info('Finished: Tested %s SatChecks %s Loops %s Errors %s',
      count, sat_checks, cycles, errors[0])
    logger.info('Live objects %s; Uncollectable %s', len(gc.get_objects()), len(gc.garbage))


if __name__ == '__main__':
  main()
