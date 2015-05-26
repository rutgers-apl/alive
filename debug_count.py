'''Find all 2-cycles.
'''
from loops import *
import traceback
import logging

logging.basicConfig(filename='debug_count.log', filemode='w', level=logging.WARNING)

sys.stderr.write('reading master.opt\n')

opts = parse_transforms(open('master.opt').read())

#opts = opts[0:1]
#opts = opts[0:40]



sys.stderr.write('%s optimizations\n' % len(opts))

count = 0
increasing = 0
unsat = 0
loops = 0
errors = 0

for i1 in range(0,len(opts)):
  o1 = opts[i1]
  for i1 in range(i1+1,len(opts)):
    try:
      for o3 in all_bin_compositions(o1,o2, False):
        
        o3_src = sum(1 for v in o3.src.itervalues() if isinstance(v, Instr))
        
        #o3c = o3.copy()
        
        for oo in all_bin_compositions(o3, o3, False):

          count += 1
          oo_src = sum(1 for v in oo.src.itervalues() if isinstance(v, Instr))
          
          sys.stderr.write('\rTested: ' + str(count))
          sys.stdout.flush()

          if o3_src < oo_src:
            increasing += 1
            continue

          if satisfiable(oo):
            print '\n-----\nLoop: ', o3.name
            o1.dump()
            print
            o2.dump()
            print
            o3.dump()
            loops += 1
          else:
            unsat += 1

    except Exception, e:
      logging.exception('combining <%s> <%s>', o1.name, o2.name)
      errors += 1

sys.stderr.write('\n')
print
print '----'
print 'final count', count
print 'loops', loops
print 'unsat', unsat
print 'increasing', increasing
print 'errors', errors