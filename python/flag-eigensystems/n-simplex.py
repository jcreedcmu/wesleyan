import sys
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
  for d in range(1,15):
      param = [1,1,1,2,2 + d]
      DEG = 5
      indices = [0,2,3,4,10]
      poly = getPoly(param, mult=DEG, indices=indices, debug=debug)
      print([d, p2s(poly)])
      polys.append([d, poly])

  START=3
  polys = polys[START:START+DEG+1]
  for coe in range(DEG+1):
    xs = [poly[0] for poly in polys]
    noisyys = [ round(poly[1].coeffs[coe], 3) for poly in polys]
    print('noisy', xs,noisyys)

  for coe in range(DEG+1):
    xs = [poly[0] for poly in polys]
#    ys = [ round(poly[1].coeffs[coe], 0) for poly in polys]
    ys = [ poly[1].coeffs[coe] for poly in polys]
    print (f"x^{DEG-coe} ( {p2s( lagrange(xs,ys), 'e')} ) +")


import inspect
def showPolysCustom(vname, paramf, DEG, indices):
  print("\n" + inspect.getsource(paramf), end="")
  polys = []
  for d in range(0,DEG+DEG):
      param = paramf(d)
      if param == None:
        continue
      poly = getPoly(param, mult=DEG, indices=indices)
      print([param[-1], p2s(poly)], file=sys.stderr)
      polys.append([param[-1], poly])
      if len(polys) == DEG+1:
        break

  for coe in range(DEG+1):
    xs = [poly[0] for poly in polys]
    ys = [ poly[1].coeffs[coe] for poly in polys]
    print (f"x^{DEG-coe} ( {p2s( lagrange(xs,ys), vname)} ) +")


# params are coefficients for σ0, σ1, ... σn
def showEigs(params):
  count = Counter(getEigvals(params))
  print ("""
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|""")
  for i in reversed([i for i in count.keys()]):
      print(f"| {count[i]} | {i} |")
  print("|--------------+------------|")

  keycounts = Counter([count[k] for k in count.keys()])
  print(keycounts)


def renderEigs():

  for d in range(0,500):
    print(d, file=sys.stderr)
    x =  d / 500
    param = [1,1,1,1+x, 3]
    count = Counter(getEigvals(param))
    for i in count.keys():
      print(f"{x} {i} {count[i]}")

# gnuplot:
# plot '/tmp/data'  using 1:2:3 lc variable with dots
# plot '/tmp/data'  using 1:2:3 lc variable pt 7


#showEigs([1,1,1,1,3])
#showPolysCustom('e', (lambda e: None if e == 4 else [1,1,1,3,3+e]), 5, [0,2,3,4,10])
showPolysCustom('e', (lambda e: [1,1,1,1,4+e]), 5, [0,2,3,6,10])
showPolysCustom('e', (lambda e: [1,1,1,2,4+e]), 5, [0,2,3,4,10])
showPolysCustom('e', (lambda e: None if e == 3 else [1,1,1,3,4+e]), 5, [0,2,3,4,10])
showPolysCustom('e', (lambda e: [1,2,1,1,5+e]), 5, [0,2,3,6,10])
showPolysCustom('e', (lambda e: [1,3,1,1,6+e]), 5, [0,2,3,6,10])
#renderEigs()
