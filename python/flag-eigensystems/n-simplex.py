import re
import numpy as np
from numpy import linalg, dot, transpose, add, subtract
from scipy.interpolate import lagrange
from permutation import Permutation
import math
from collections import Counter
import pickle
import os
import time

# analyze the flags of the N-simplex
N = 3

# degree of polynomial / multiplicity of root
DEG = 6

n = N + 2
nfac = math.factorial(n)

# takes number in range(nfac), returns permutation
def decomp(x):
    return Permutation.from_lehmer(x, n)

# inverse of decomp, takes permutation, returns number
def comp(x):
    return x.lehmer(n)

def pi(m):
  def entry(i):
    if i == m+1:
      return m+2
    elif i == m+2:
      return m+1
    else:
      return i
  return Permutation(*[entry(i) for i in range(1,n+1)])

def σ(m, x):
    return comp(decomp(x) * pi(m))

σs = [[σ(m, x) for m in range(n-1)] for x in range(nfac)]

ccc = [1,1,4,1]

def coef(dim):
  return ccc[dim]

def mkmat():
  mat = np.zeros([nfac, nfac])
  for (row, vec) in enumerate(σs):
    for (dim, col) in enumerate(vec):
      mat[row][col] = coef(dim)
  return mat

def p2s(p, v="x"):
    c = p.coeffs
    s = " " + " + ".join([f"{round(x,3)} * x^{len(c)-ix-1}" for (ix,x) in enumerate(c) if round(x,5) != 0])
    s = re.sub(r'\+ -', '- ',  s)
    s = re.sub(r' \* x\^0', '',  s)
    s = re.sub(r'x\^1', 'x',  s)
    s = re.sub(r'\.0 ', ' ',  s)
    s = re.sub(r'\.0$', '',  s)
    s = re.sub(r' 1 \* ', ' ',  s)
    s = re.sub(r' \* ', '',  s)
    s = re.sub(r'-1x', '-x',  s)
    s = re.sub('x', v, s)
    return s

def go():
  before = time.perf_counter()
  cacheFile = f"/tmp/matrix-{n}.pickle"
  if os.path.exists(cacheFile) and False:
      with open(cacheFile, 'rb') as cache:
          mat = pickle.load(cache)
  else:
      mat = mkmat()
      with open(cacheFile, 'wb') as cache:
          pickle.dump(mat, cache)
  # print (f"constructing matrix: {time.perf_counter() - before}")

  before = time.perf_counter()
  (eigval,y) = (linalg.eigh(mat))
  # print (f"solving eigensystem: {time.perf_counter() - before}")

  eigval = [round(x, 11) for x in eigval]

  count = Counter(eigval)

  accum = np.poly1d([1])
  for i in reversed([i for i in count.keys()]):
    if (count[i] == DEG):
      accum *= np.poly1d([1,-i])
  print(p2s(accum))
  return accum

polys = []
for d in range(2,30):
    ccc[3] = d
    polys.append(go())

for coe in [2,4,6]:
  xs = range(2, 2+DEG+1)
  ys = [ round(polys[x-1].coeffs[coe], 3) for x in xs]
  print (f"x^{6-coe} ( {p2s( lagrange(xs,ys), 'd')} ) +")

exit(0)
print ("""
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|""")
for i in reversed([i for i in count.keys()]):
    print(f"| {count[i]} | {i} |")
print("|--------------+------------|")

keycounts = Counter([count[k] for k in count.keys()])
print(keycounts)
