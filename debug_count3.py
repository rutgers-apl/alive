'''Find all 3-cycles.
'''
from loops import *
import traceback
import logging

logging.basicConfig(filename='debug_count3.log', filemode='w', level=logging.WARNING)

sys.stderr.write('reading master.opt\n')

opts = parse_transforms(open('master.opt').read())

#opts = opts[0:1]
#opts = opts[0:20]



sys.stderr.write('%s optimizations\n' % len(opts))

count = 0
increasing = 0
unsat = 0
loops = 0
errors = [0]
sat_checks = 0

def count_error(*a):
  errors[0] += 1

def count_src(o):
  return sum(1 for v in o.src.itervalues() if isinstance(v, Instr))

for i1 in range(0,len(opts)):
  o1 = opts[i1]
  for i2 in range(i1,len(opts)):
    o2 = opts[i2]
    for o12 in all_bin_compositions(o1,o2,count_error):
#       sat_checks += 1
#       if not satisfiable(o12):
#         unsat += 0
#         continue

      for i3 in range(i2, len(opts)):
        o3 = opts[i3]

        for o123 in all_bin_compositions(o12, o3, count_error):
#           sat_checks += 1
#           try:
#             if not satisfiable(o123):
#               unsat += 1
#               continue
#           except Exception as e:
#             logging.exception('satisfiable threw: %r\n\n%s\n\n%s\n\n%s\n\n%s\n', e, o1, o2, o3, o123)
#             continue

          o_src = count_src(o123)

          for oo in all_bin_compositions(o123,o123,count_error):

            count += 1
            sys.stderr.write('\rTested: %s SatChecks: %s Loops: %s' % (count, sat_checks, loops))
            sys.stderr.flush()

            oo_src = count_src(oo)

            if o_src < oo_src:
              increasing += 1
              continue

            sat_checks += 1
            if not satisfiable(oo):
              continue

            print '\n-----\nLoop: ', o123.name
            o1.dump()
            print
            o2.dump()
            print
            o3.dump()
            print
            o123.dump()
            loops += 1

sys.stderr.write('\n')
print
print 'final count', count
print 'loops', loops
print 'increasing', increasing
print
print 'sat_checks', sat_checks
print 'unsat', unsat
print 'errors', errors[0]