'''Find all 2-cycles.
'''
from loops import *
import traceback

print 'reading master.opt'

opts = parse_transforms(open('master.opt').read())

#opts = opts[0:1]
#opts = opts[0:40]



print 'optimizations', len(opts)

count = 0
increasing = 0
unsat = 0
loops = 0
errors = 0

for o1 in opts:
  for o2 in opts:
    if o1 is o2:
      continue
    
    try:
      for o3 in all_bin_compositions(o1,o2, False):
        if isinstance(o3, Exception):
          errors += 1
          print '\n----- Exception', o1.name, o2.name, '\n', str(o3)
          continue

        sys.stdout.write('\r' + o3.name)
        sys.stdout.flush()
        
        o3_src = sum(1 for v in o3.src.itervalues() if isinstance(v, Instr))
        
        #o3c = o3.copy()
        
        for oo in all_bin_compositions(o3, o3, False):
          if isinstance(oo, Exception):
            errors += 1
            print '\n----- Exception\n', str(oo)
            continue

          count += 1
          oo_src = sum(1 for v in oo.src.itervalues() if isinstance(v, Instr))
          
          if o3_src < oo_src:
            increasing += 1
            continue
          
          if satisfiable(oo):
            print '\n-----\nLoop: ', o3.name
            o3.dump()
            loops += 1
          else:
            unsat += 1
                
    except Exception, e:
      print '\n-----\ndebug_count: Caught exception doing', o1.name, '::', o2.name
      print traceback.format_exc(sys.exc_info())
      errors += 1

print
print 'final count', count
print 'loops', loops
print 'unsat', unsat
print 'increasing', increasing
print 'errors', errors