#!/usr/bin/env python
import loops
import argparse, itertools, sys, os, json
import gc
import logging, logging.config
import logutils.queue, Queue
import threading, multiprocessing

logger = logging.getLogger(__name__)

def prefixes(length, max):
  'Generate tuples of given length corresponding to unique prefixes of cycles'

  if length < 1:
    return

  def _prefixes_after(length, max, min, prev):
    if length < 1:
      yield prev
      return

    for i in range(min,max):
      if i in prev:
        continue
      prev2 = prev + (i,)
      for p in _prefixes_after(length-1, max, min, prev2):
        yield p

  for i in range(0, max - length + 1):
    for p in _prefixes_after(length-1, max, i+1, (i,)):
      yield p

def prefix_generator(length, max, procs, prefix_queue, finished):
  'Thread worker which generates prefixes and sends them to a queue'
  
  log = logger.getChild('prefix_generator')
  log.debug('Prefix generator started')
  
  for p in prefixes(length, max):
    log.debug('Generated %s', p)
    prefix_queue.put(p)
  
  log.debug('Prefixes generated')
  prefix_queue.join() # wait until all the prefixes have been handled
  
  log.debug('Prefixes handled')
  finished.set() # tell main thread to stop spawning workers
  
  # terminate workers
  for i in range(procs):
    prefix_queue.put(None)
  
  log.debug('Generator complete')


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

COUNT, SAT_CHECKS, CYCLES, ERRORS = range(4)
MAX_TESTS = 50000

def search_process(suite, length, prefix_queue, result_queue, status_queue, log_config):
  logging.config.dictConfig(log_config)
  log = logger.getChild('search_process')
  log.info('Worker thread started')
  opts = loops.parse_transforms(open(suite).read())

  log.debug('%s optimizations', len(opts))

  info = [0,0,0,0]
  
  def count_error(e,o1,o2):
    info[ERRORS] += 1
  
  while info[COUNT] < MAX_TESTS:
    p = prefix_queue.get()
    if p is None:
      prefix_queue.task_done()
      break
    
    log.info('Checking prefix %s', p)
    
    for o,os in search_after_prefix(opts, length, p, count_error):
      o_src = count_src(o)
      
      for oo in loops.all_bin_compositions(o, o, count_error):
        if info[COUNT] % 1000 == 0:
          log.info('Tested %s SatChecks %s Loops %s Errors %s', *info)
  
        info[COUNT] += 1
        
        oo_src = count_src(oo)
        
        if o_src < oo_src:
          continue
        
        info[SAT_CHECKS] += 1
        if not loops.satisfiable(oo):
          continue
        
        info[CYCLES] += 1

        # TODO: put found loops into a queue
        result = 'Loop: {}\n{}\n\n{}'.format(o.name, '\n\n'.join(str(op) for op in os), o)
        result_queue.put(result)
        log.info(result)

    prefix_queue.task_done()

  log.info('Worker exiting')
  status_queue.put(info)
  

def queue_printer(result_queue):
  'Read strings from the queue. Terminate when we get None'
  while True:
    result = result_queue.get()
    if result is None:
      return

    print '\n-----'
    print result

# TODO: track child processes so we can handle exceptions gracefully
def search_manager(suite, prefix_length, length, max, log_config):
  log = logger.getChild('search_manager')
  log.info('Starting manager')
  
  prefix_queue = multiprocessing.JoinableQueue()
  status_queue = multiprocessing.Queue()
  result_queue = multiprocessing.Queue()
  finished = threading.Event()
  procs = 1
  
  prefix_thread = threading.Thread(
    target=prefix_generator,
    args=(prefix_length, max, procs, prefix_queue, finished))
  prefix_thread.daemon = True # no cleanup needed if we get a KeyboardInterrupt

  result_thread = threading.Thread(
    target=queue_printer,
    args=(result_queue,))
  
  for i in range(procs):
    p = multiprocessing.Process(
      target=search_process,
      args=(suite, length, prefix_queue, result_queue, status_queue, log_config))
    p.start()
  
  total_info = [0,0,0,0]
  try:
    prefix_thread.start()
    result_thread.start()
    # read from the result queue until the prefix generator completes
    while True:
      r = status_queue.get(block=True)
      log.debug('Got result %s', r)

      for i in range(4):
        total_info[i] += r[i]

      log.info('Current totals %s', total_info)

      if finished.is_set():
        break
      else:
        p = multiprocessing.Process(
          target=search_process,
          args=(suite, length, prefix_queue, status_queue, log_config))
        p.start()

    # wait until all the sentinels have been received
    prefix_queue.join()

    # drain the leftovers
    while True:
      try:
        r = status_queue.get(block=False)
        log.debug('Got result %s', r)

        for i in range(4):
          total_info[i] += r[i]

        log.info('Current totals %s', total_info)
      except Queue.Empty:
        break

    log.info('Final: Candidates %s Sat_Checks %s Cycles %s Errors %s', *total_info)
  finally:
    log.debug('Closing result queue reader')
    result_queue.put(None)

def count_opts(suite):
  opts = loops.parse_transforms(open(suite).read())
  return len(opts)

def main():
  log_queue = multiprocessing.Queue()
  log_config = {
    'version': 1,
    'disable_existing_handlers': True,
    'handlers': {
      'queue': {
        'class': 'logutils.queue.QueueHandler',
        'queue': log_queue
      }
    },
    'loggers': {
      __name__: { 'level': 'INFO' }
    },
    'root': {
      'level': 'WARNING',
      'handlers': ['queue']
    }
  }

  h = logging.FileHandler(filename='find-simple-loops.log', mode='w')
  #h = logging.StreamHandler()
  f = logging.Formatter('%(asctime)s - %(levelname)-8s - %(name)s - %(message)s')
  h.setFormatter(f)
  ql = logutils.queue.QueueListener(log_queue, h)
  ql.start()
  logging.config.dictConfig(log_config)
  
  parser = argparse.ArgumentParser()
  parser.add_argument('prefix_length', type=int,
    help='Length of prefix to spawn into worker processes')
  parser.add_argument('suffix_length', type=int,
    help='Length of cycles following the prefix')
  parser.add_argument('file', type=str,
    help='optimization suite to analyze')
  
  args = parser.parse_args()
  
  
  # FIXME: Need to make sure zero-length prefixes work
  if args.prefix_length < 1 or args.suffix_length < 1:
    sys.stderr.write('cycle length must be positive\n')
    exit(1)
  
  if not os.path.exists(args.file):
    sys.stderr.write(args.file + ': not found\n')
    exit(1)
  
  logger.info('Starting')
  
  max = count_opts(args.file)
  
  logger.info('Counted %s opts', max)
  #exit(0)
  
  try:
    search_manager(args.file, args.prefix_length, args.suffix_length, max, log_config)
  finally:
    logger.debug('Closing queue listener')
    ql.stop()

def old_main():
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
