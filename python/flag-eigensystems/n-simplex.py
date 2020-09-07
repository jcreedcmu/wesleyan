import numpy as np
from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation
import math
from collections import Counter
import pickle
import os
import time

# this number below is actually n+2 to get the n-simplex
n = 6
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

def coef(dim):
#  return 1
  return [1.001,1.0015,1.0001,1.001,1.0012,1.03][dim]

def mkmat():
  mat = np.zeros([nfac, nfac])
  for (row, vec) in enumerate(σs):
    for (dim, col) in enumerate(vec):
      mat[row][col] = coef(dim)
  return mat

before = time.perf_counter()
cacheFile = f"/tmp/matrix-{n}.pickle"
if os.path.exists(cacheFile) and False:
    with open(cacheFile, 'rb') as cache:
        mat = pickle.load(cache)
else:
    mat = mkmat()
    with open(cacheFile, 'wb') as cache:
        pickle.dump(mat, cache)
print (f"constructing matrix: {time.perf_counter() - before}")

# for row in mat:
#     print (row)

before = time.perf_counter()
(eigval,y) = (linalg.eigh(mat))
print (f"solving eigensystem: {time.perf_counter() - before}")

# y = transpose(y)

eigval = [round(x, 11) for x in eigval]
count = Counter(eigval)

print ("""
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|""")
for i in reversed([i for i in count.keys()]):
    print(f"| {count[i]} | {i} |")
print("|--------------+------------|")
