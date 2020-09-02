from scipy import sparse
from scipy.sparse.linalg import eigsh
from permutation import Permutation
import math

n = 8
nfac = math.factorial(n)

# takes number 0..119, returns permutation
def decomp(x):
    return Permutation.from_lehmer(x, n)

# inverse of decomp, takes permutation, returns number
def comp(x):
    return x.lehmer(n)

def σ0(x):
    return comp(decomp(x) * Permutation(2, 1))

def σ1(x):
    return comp(decomp(x) * Permutation(1, 3, 2))

def σ2(x):
    return comp(decomp(x) * Permutation(1, 2, 4, 3))

def σ3(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 5, 4))

def σ4(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 4, 6, 5))

def σ5(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 4, 5, 7, 6))

def σ6(x):
    return comp(decomp(x) * Permutation(1, 2, 3, 4, 5, 6, 8, 7))



def mkmat():
    row = []
    col = []
    data = []
    for j in range(nfac):
      for i in [σ0(j), σ1(j), σ2(j), σ3(j), σ4(j), σ5(j), σ6(j)]:
          row.append(i)
          col.append(j)
          data.append(1)
    return sparse.coo_matrix((data, (row, col)), shape=(nfac, nfac))

print ("constructing")
mat = mkmat()
print ("constructed")
(evals, evecs) = eigsh(mat.asfptype(), 60)

for e in evals:
      print (e)
