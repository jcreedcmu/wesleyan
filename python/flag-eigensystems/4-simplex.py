from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation

# a flag is a permutation of 0, 1, 2, 3, 4

# σ0 swaps the first two, σ1 swaps the second 2, σ2 swaps the second-last 2, σ3 swaps the last 2

n = 6

# takes number 0..119, returns permutation
def decomp(x):
    return Permutation.from_lehmer(x, n)

# inverse of decomp, takes permutation, returns number
def comp(x):
    return x.lehmer(n)

def σ0(x):
    return comp(decomp(x) * Permutation(2, 1, 3, 4, 5))

def σ1(x):
    return comp(decomp(x) * Permutation(1, 3, 2, 4, 5))

def σ2(x):
    return comp(decomp(x) * Permutation(1, 2, 4, 3, 5))

def σ3(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 5, 4))

def σ4(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 4, 6, 5))

def entry(i, j):
    if i in [σ0(j), σ1(j), σ2(j), σ3(j), σ4(j)]:
        return 1
    else:
        return 0

nfac = 720

print (decomp(0))

mat = [[entry(i,j) for i in range(nfac)] for j in range(nfac) ]

# for row in mat:
#     print (row)

(x,y) = (linalg.eigh(mat))

y = transpose(y)

for i in range(nfac):
    print(f"eigenvalue {x[i]}")
