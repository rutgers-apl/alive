#!env python
'''
Find the compositions of a sequence of optimizations, and check whether it
is a loop.
'''
import sys
from loops import *

def all_sequences_after(n, opts):
  if n >= len(opts)-1:
    yield opts[-1].copy()
    return

  for o2 in all_sequences_after(n+1, opts):
    for c in all_bin_compositions(opts[n], o2):
      yield c

def compose_sequence(opts):
  for c in all_sequences_after(0, opts):
    print '\n-----'
    c.dump()

def test_sequence(input):
  compose_sequence(parse_transforms(input))

sample = '''Name: commute
%r = add C, %a
=>
%r = add %a, C

Name: assoc
%x = add %b, %c
%z = add %a, %x
=>
%y = add %a, %b
%z = add %y, %c
'''

if __name__ == '__main__':
  test_sequence(sys.stdin.read())
  #test_sequence(sample)