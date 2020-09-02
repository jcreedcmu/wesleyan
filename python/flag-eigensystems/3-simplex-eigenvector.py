import math
from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation

# a flag is a permutation of 0, 1, 2, 3, 4

# σ0 swaps the first two, σ1 swaps the second 2, σ2 swaps the second-last 2, σ3 swaps the last 2

# takes number 0..119, returns permutation
def decomp(x):
    return Permutation.from_lehmer(x, 5)

# inverse of decomp, takes permutation, returns number
def comp(x):
    return x.lehmer(5)

def σ0(x):
    return comp(decomp(x) * Permutation(2, 1, 3, 4, 5))

def σ1(x):
    return comp(decomp(x) * Permutation(1, 3, 2, 4, 5))

def σ2(x):
    return comp(decomp(x) * Permutation(1, 2, 4, 3, 5))

def σ3(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 5, 4))

def entry(i, j):
    if i in [σ0(j), σ1(j), σ2(j), σ3(j)]:
        return 1
    else:
        return 0

nfac = 120


mat = [[entry(i,j) for i in range(nfac)] for j in range(nfac) ]

# for row in mat:
#     print (row)

(x,y) = (linalg.eigh(mat))

y = transpose(y)

vecs = []
for i in range(nfac):
    # finding eigenvectors of second-largest eigenvalue
    if (abs(x[i] - 3.618) < 0.001):
        vecs.append([t  for t in y[i]])

vecs = [
    vecs[0], vecs[2], vecs[3]
    ]

vecs = [
    [ vecs[0][i] * vecs[1][2] -  vecs[1][i] * vecs[0][2] for i in range(len(vecs[0]))],
    [ vecs[0][i] * vecs[2][2] -  vecs[2][i] * vecs[0][2] for i in range(len(vecs[0]))]
]

vecs = [
    [ vecs[0][i] * vecs[1][4] -  vecs[1][i] * vecs[0][4] for i in range(len(vecs[0]))],
]

vecs = [[ x / vecs[0][6] for x in vecs[0]]]

# this prints a mostly √5-based eigenvector
for vec in vecs:
    print ([round(x, 9) for x in vec])
