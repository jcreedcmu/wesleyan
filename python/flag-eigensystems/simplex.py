from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation
import math

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
  if i in [σ0(j), σ1(j), σ2(j)]:
      return 1
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

n0 = [1, 0, -1, 0,  0,  0,  0, -1,  0,  0,  1, 0,  0,  1,  0,  0, -1, 0,  0,  0,  0, -1,  0, 1]
e0 = [1, 0,  1, 0,  0,  0,  0, -1,  0,  0, -1, 0,  0, -1,  0,  0, -1, 0,  0,  0,  0,  1,  0, 1]
n1 = [0, 0,  0, 1,  0, -1,  0,  0,  0, -1,  0, 1, -1,  0,  1,  0,  0, 0,  1,  0, -1,  0,  0, 0]
e1 = [0, 0,  0, 1,  0,  1,  0,  0,  0,  1,  0, 1, -1,  0, -1,  0,  0, 0, -1,  0, -1,  0,  0, 0]
n2 = [0, 1,  0, 0, -1,  0, -1,  0,  1,  0,  0, 0,  0,  0,  0, -1,  0, 1,  0,  1,  0,  0, -1, 0]
e2 = [0, 1,  0, 0,  1,  0, -1,  0, -1,  0,  0, 0,  0,  0,  0,  1,  0, 1,  0, -1,  0,  0, -1, 0]

# sqrt(3) eigenvalue
t0 = [0, 1, -2, -1.732, 1.732, 1, 1, 0, 1.732, 1, -2, -1.732, -1.732, -2, 1, 1.732, 0, 1, 1, 1.732, -1.732, -2, 1, 0]

# 1 + sqrt(2) eigenvalue
u0 = [0, 0, 1, 1.707, 1, 1.707, -1, -1, -1.414, -1.707, -1.414, -1.707, 0.707, 1.414, -0.707, -1, 1, 0, 0.707, 1.414, -0.707, -1, 1, 0]

# These are all zero; ni are eigenvalue -1 and ei are eigenvalue 1.
print(add(dot(mat, n0), n0))
print(add(dot(mat, n1), n1))
print(add(dot(mat, n2), n2))
print(subtract(dot(mat, e0), e0))
print(subtract(dot(mat, e1), e1))
print(subtract(dot(mat, e2), e2))
print ("---")
print (t0)
print (dot(mat, t0))

for i in range(nfac):
  if u0[i] != 0:
    print (f"{u0[i]} * {[Permutation.from_lehmer(i, 4)(j) for j in [1,2,3,4]]}")
