'''
Front-end to find-simple-loops to avoid memory leak in Z3.

Calls find-simple-loops repeatedly with different possible prefixes for an n-cycle.
'''
import subprocess, argparse

def _prefix_after(length, max, min, prev):
  if length < 1:
    yield prev
    return

  for i in range(min,max):
    if i in prev:
      continue
    prev2 = prev + (i,)
    for p in _prefix_after(length-1, max, min, prev2):
      yield p

def prefix(length, max):
  'Generate tuples of given length corresponding to unique prefixes of cycles'

  if length < 1:
    return
  
  for i in range(0, max - length + 1):
    for p in _prefix_after(length-1, max, i+1, (i,)):
      yield p


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument('length', type=int,
    help='Length of cycles to search for')
  parser.add_argument('prefix_len', type=int,
    help='Length of prefix')
  parser.add_argument('count', type=int,
    help='Number of optimizations in file')
  parser.add_argument('file', type=str,
    help='optimization suite to analyze')

  args = parser.parse_args()

  for p in prefix(args.prefix_len, args.count):
    prefix_idxs = ','.join(str(i) for i in p)
    print 'trying', prefix_idxs
    subprocess.call(['python', 'find-simple-loops.py', '--prefix', prefix_idxs, 
      str(args.length - args.prefix_len), args.file])

if __name__ == '__main__':
  main()