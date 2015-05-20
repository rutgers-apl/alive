'''Find all 3-cycles.
'''
from loops import *
import traceback
import logging

logging.basicConfig(filename='debug_count3.log', filemode='w', level=logging.WARNING)

sys.stderr.write('reading master.opt\n')

opts = parse_transforms(open('master.opt').read())

#opts = opts[0:1]
opts = opts[0:40]



sys.stderr.write('%s optimizations\n' % len(opts))

count = 0
increasing = 0
unsat = 0
loops = 0
errors = 0
sat_checks = 0

def count_src(o):
  return sum(1 for v in o.src.itervalues() if isinstance(v, Instr))

for o1 in opts:
  for o2 in opts:
    for o12 in all_bin_compositions(o1,o2,False):
#       sat_checks += 1
#       if not satisfiable(o12):
#         unsat += 0
#         continue

      for o3 in opts:
        if o3 is o1 or o3 is o2:
          continue

        for o123 in all_bin_compositions(o12, o3, False):
#           sat_checks += 1
#           try:
#             if not satisfiable(o123):
#               unsat += 1
#               continue
#           except Exception as e:
#             logging.exception('satisfiable threw: %r\n\n%s\n\n%s\n\n%s\n\n%s\n', e, o1, o2, o3, o123)
#             continue

          o_src = count_src(o123)

          for oo in all_bin_compositions(o123,o123,False):

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
print 'errors', errors