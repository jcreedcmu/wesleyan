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

# given a list of coefficients for σ0, σ1, ... σn flips,
# output the corresponding matrix.
def mkmat(params):
  n = len(params) + 1
  nfac = math.factorial(n)

  def pi(m):
    def entry(i):
      if i == m+1:
        return m+2
      elif i == m+2:
        return m+1
      else:
        return i
    return Permutation(*[entry(i) for i in range(1,n+1)])

  σs = [[ (Permutation.from_lehmer(x, n) * pi(m)).lehmer(n)
          for m in range(n-1) ] for x in range(nfac) ]

  mat = np.zeros([nfac, nfac])
  for (row, vec) in enumerate(σs):
    for (dim, col) in enumerate(vec):
      mat[row][col] = params[dim]
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

def getEigvals(params, debug=False):
  before = time.perf_counter()
  mat = mkmat(params)
  if debug:
    print (f"constructing matrix: {time.perf_counter() - before}")

  before = time.perf_counter()
  (eigval,y) = (linalg.eigh(mat))
  if debug:
    print (f"solving eigensystem: {time.perf_counter() - before}")

  return [round(x, 11) for x in eigval]

def getPoly(params, mult, indices=None, debug=False):
  count = Counter(getEigvals(params, debug))

  accum = np.poly1d([1])
  eigs = [ i for i in count.keys() if count[i] == mult ]
  if debug:
    print(eigs)
  if indices == None:
    indices = range(len(eigs))
  for i in indices:
    accum *= np.poly1d([1,-eigs[i]])
  return accum

def showPolys(debug=False):
  polys = []
  for d in range(1,30):
      param = [  1.00, 1.000, 0.001, d]
      DEG = 5
      indices = [0,1,3,5,7]
      poly = getPoly(param, mult=DEG, indices=indices, debug=debug)
      print([d, p2s(poly)])
      polys.append([d, poly])

  polys = polys[2:2+DEG+1]
  for coe in range(DEG+1):
    xs = [poly[0] for poly in polys]
    ys = [ round(poly[1].coeffs[coe], 3) for poly in polys]

    print (f"x^{DEG-coe} ( {p2s( lagrange(xs,ys), 'd')} ) +")

def showEigs():
  count = Counter(getEigvals([1,0.1,0.01,1]))
  print ("""
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|""")
  for i in reversed([i for i in count.keys()]):
      print(f"| {count[i]} | {i} |")
  print("|--------------+------------|")

  keycounts = Counter([count[k] for k in count.keys()])
  print(keycounts)

showEigs()
# showPolys()
