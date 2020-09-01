from numpy import linalg, dot, transpose
from permutation import Permutation

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
  if i in [σ0(j), σ1(j), σ2(j)]:
      return 1
  else:
      return 0
mat = [[entry(i,j) for i in range(24)] for j in range(24) ]

for row in mat:
    print (row)

(x,y) = (linalg.eigh(mat))

y = transpose(y)

for i in range(24):
    print(f"eigenvalue {x[i]}")

for i in range(24):
    print(f"eigenvalue {x[i]}")
    print(f"eigenvector {y[i] / y[i][1]}")
