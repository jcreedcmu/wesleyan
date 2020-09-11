from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation
import math

n = 3
nfac = math.factorial(n)

# a flag is a permutation of 0, 1, 2

# σ0 swaps the first two, σ1 swaps the second 2

# takes number 0..23, returns permutation
def decomp(x):
    return Permutation.from_lehmer(x, 3)

# inverse of decomp, takes permutation, returns number
def comp(x):
    return x.lehmer(3)

def σ0(x):
    return comp(decomp(x) * Permutation(2, 1, 3))

def σ1(x):
    return comp(decomp(x) * Permutation(1, 3, 2))

b = 4
a = 3

def entry(i, j):
  if (i == (j + 1) % 6):
    return b if i % 2 else a
  if (i == (j - 1) % 6):
    return b if j % 2 else a
  else:
    return 0

mat = [[entry(i,j) for i in range(nfac)] for j in range(nfac) ]

for row in mat:
    print (row)


(x,y) = (linalg.eigh(mat))

y = transpose(y)

for i in range(nfac):
    print(f"eigenvalue {x[i]}")

for i in range(nfac):
    print(f"eigenvalue {x[i]}")
    print(f"eigenvector {y[i] / y[i][1]}")

v1 = y[3]
v2 = y[4]

w = [v1[i] * v2[0] - v1[0] * v2[i] for i in range(6)]
w = [w[i] / w[1] for i in range(6)]

print(w)
