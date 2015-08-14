#!/usr/bin/env python
import loops
import argparse, itertools, sys, os, json
import gc
import logging, logging.config
import logutils.queue, Queue
import threading, multiprocessing
import random
from math import factorial

logger = logging.getLogger(__name__)

def simple_sequence(length, max):
  'Randomly generate a non-repeating sequence'
  assert length <= max

  taken = set()
  while length > 0:
    x = random.randrange(0,max)
    if x not in taken:
      yield x
      taken.add(x)
      length -= 1

def sequences(length, max):
  'Randomly generate sequences of integers in [0,max) of a given length'
  
  assert length <= max
  count = reduce(lambda x,y: x*y, (max-i for i in range(length)))


  picked = set()
  while count > 0:
    sequence = tuple(simple_sequence(length, max))
    if sequence not in picked:
      picked.add(sequence)
      count -= 1
      yield sequence    
  
def sequence_generator(length, max, procs, queue, finished):
  'Thread worker which generates sequences and sends them to a queue'
  
  log = logger.getChild('sequence_generator')
  log.debug('Sequence generator started')

  for s in sequences(length, max):
    log.debug('Generated %s', s)
    queue.put(s)
  
  finished.set()
  log.debug('Sequence generator complete')

status = '\rTested: {} SatChecks: {} Loops: {}'

def count_src(o):
  return sum(1 for v in o.src.itervalues() if isinstance(v, loops.Instr))

COUNT, SAT_CHECKS, CYCLES, ERRORS = range(4)
MAX_TESTS = 50000

def search_process(suite, limit, sequence_queue, result_queue, status_queue, log_config):
  logging.config.dictConfig(log_config)
  log = logger.getChild('search_process')
  log.info('Worker thread started, limit %s', limit)
  opts = loops.parse_transforms(open(suite).read())

  log.debug('%s optimizations', len(opts))

  info = [0,0,0,0]
  
  def count_error(e,o1,o2):
    info[ERRORS] += 1
  
  while info[COUNT] < limit:
    s = sequence_queue.get()
    if s is None:
      log.info('Worker exiting %s', info)
      status_queue.put(info)
      return
    
    log.debug('Checking sequence %s', s)
    
    os = tuple(opts[i] for i in s)
    for o in loops.all_compositions(os):
      if info[COUNT] >= limit:
        break

      o_src = count_src(o)
      
      for oo in loops.all_bin_compositions(o, o, count_error):
        if info[COUNT] >= limit:
          break

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

  log.info('Worker exiting %s', info)
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
def search_manager(suite, length, tests, seed, max, procs, log_config):
  log = logger.getChild('search_manager')
  log.info('Starting manager')
  
  sequence_queue = multiprocessing.Queue(procs)
  status_queue = multiprocessing.Queue()
  result_queue = multiprocessing.Queue()
  finished = threading.Event()

  prefix_thread = threading.Thread(
    target=sequence_generator,
    args=(length, max, procs, sequence_queue, finished))
  prefix_thread.daemon = True # no cleanup needed if we get a KeyboardInterrupt

  result_thread = threading.Thread(
    target=queue_printer,
    args=(result_queue,))

  limit = MAX_TESTS if tests > MAX_TESTS * procs else tests // procs

  for i in range(procs):
    p = multiprocessing.Process(
      target=search_process,
      args=(suite, limit, sequence_queue, result_queue, status_queue, log_config))
    p.start()
    tests -= limit

  active = procs
  total_info = [0,0,0,0]
  try:
    prefix_thread.start()
    result_thread.start()
    # read from the result queue until the prefix generator completes
    while active > 0:
      r = status_queue.get(block=True)
      log.debug('Got result %s; %s tests remain', r, tests)

      for i in range(4):
        total_info[i] += r[i]

      log.info('Current totals %s', total_info)

      if finished.is_set() or tests <= 0:
        active -= 1
        log.debug('%s workers active', active)
      else:
        limit = min(MAX_TESTS, tests)
        tests -= limit
        p = multiprocessing.Process(
          target=search_process,
          args=(suite, limit, sequence_queue, result_queue, status_queue, log_config))
        p.start()

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

  h = logging.FileHandler(filename='find-random-loops.log', mode='w')
  #h = logging.StreamHandler()
  f = logging.Formatter('%(asctime)s - %(levelname)-8s - %(name)s - %(message)s')
  h.setFormatter(f)
  ql = logutils.queue.QueueListener(log_queue, h)
  ql.start()
  logging.config.dictConfig(log_config)
  
  parser = argparse.ArgumentParser()
  parser.add_argument('length', type=int,
    help='length of sequences to test')
  parser.add_argument('file', type=str,
    help='optimization suite to analyze')
  parser.add_argument('-t', '--tests', type=int, default=1000000,
    help='Number of sequences to test')
  parser.add_argument('-p', '--procs', type=int, default=1,
    help='Number of sub-processes')
  parser.add_argument('--seed', type=str,
    help='Seed for random number generator')


  args = parser.parse_args()


  # FIXME: Need to make sure zero-length prefixes work
  if args.length < 1:
    sys.stderr.write('cycle length must be positive\n')
    exit(1)

  if args.tests < 1:
    sys.stderr.write('Must have at least one test\n')
    exit(1)

  if args.procs < 1:
    sys.stderr.write('Must use at least one process')
    exit(1)

  if not os.path.exists(args.file):
    sys.stderr.write(args.file + ': not found\n')
    exit(1)

  if args.seed:
    random.seed(args.seed)

  logger.info('Starting')
  
  max = count_opts(args.file)
  
  logger.info('Counted %s opts', max)
  
  try:
    search_manager(args.file, args.length, args.tests, args.seed, max, 
      args.procs, log_config)
  finally:
    logger.debug('Closing queue listener')
    ql.stop()

if __name__ == '__main__':
  main()
