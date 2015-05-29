#!/usr/bin/env python
import loops
import argparse, logging, itertools, sys

def search(opts, n, on_error=None):
  'Generate candidate n-cycles'
  if n == 1:
    for i1,o in itertools.izip(itertools.count(), opts):
      yield (o,i1,(o,))
    return

  for (o1,i1,oz) in search(opts, n-1, on_error):
    for i2 in range(i1, len(opts)):
      o2 = opts[i2]
      os = oz + (o2,)
      for c in loops.all_bin_compositions(o1, o2, on_error):
        yield (c,i2, os)

status = '\rTested: {} SatChecks: {} Loops: {}'

def count_src(o):
  return sum(1 for v in o.src.itervalues() if isinstance(v, loops.Instr))

def main():
  logging.basicConfig(filename='find-loops.log', filemode='w')

  parser = argparse.ArgumentParser()
  parser.add_argument('length', type=int,
    help='Length of cycles to search for')
  parser.add_argument('file', type=argparse.FileType('r'),
    help='optimization suite to analyze')

  args = parser.parse_args()

  if args.length < 1:
    sys.stderr.write('cycle length must be positive\n')
    exit(1)

  sys.stderr.write('Reading ' + args.file.name + '\n')
  opts = loops.parse_transforms(args.file.read())
  sys.stderr.write('{} optimizations'.format(len(opts)))

  count = 0
  sat_checks = 0
  cycles = 0
  errors = [0]
  
  def count_error(e,o1,o2):
    errors[0] += 1

  for o,_,os in search(opts, args.length):
    o_src = count_src(o)
    for oo in loops.all_bin_compositions(o,o,count_error):
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
  
  sys.stderr.write(status.format(count, sat_checks, cycles))
  sys.stderr.write('\n')
  print
  print 'final count', count
  print 'loops', cycles
  print 'sat_checks', sat_checks
  print 'errors', errors[0]

if __name__ == '__main__':
  main()