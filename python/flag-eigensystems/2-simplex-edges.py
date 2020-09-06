from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation
import math
from collections import Counter

n = 4
nfac = math.factorial(n)

# a flag is a permutation of 0, 1, 2, 3

# σ0 swaps the first two, σ1 swaps the second 2, σ2 swaps the last 2.

# takes number 0..23, returns permutation
def decomp(x):
    return Permutation.from_lehmer(x, 4)

# inverse of decomp, takes permutation, returns number
def comp(x):
    return x.lehmer(4)

def σ0(x):
    return comp(decomp(x) * Permutation(2, 1, 3, 4))

def σ1(x):
    return comp(decomp(x) * Permutation(1, 3, 2, 4))

def σ2(x):
    return comp(decomp(x) * Permutation(1, 2, 4, 3))

def entry(i, j):
  if i in [σ0(j)]:
    return 1
  if i in [σ1(j)]:
    return 1
  if i in [σ2(j)]:
    return 3
  else:
    return 0

def go():
  mat = [[entry(i,j) for i in range(nfac)] for j in range(nfac) ]
  (x,y) = (linalg.eigh(mat))

  count = Counter([ round(v, 9) for v in x ])
  for key in count.keys():
    if (count[key] == 3 and key > 0):
        print(f"eig: {key}")

go()
