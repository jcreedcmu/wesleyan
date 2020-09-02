from scipy import sparse
from scipy.sparse.linalg import eigsh
from permutation import Permutation

# a flag is a permutation of 0, 1, 2, 3, 4

# σ0 swaps the first two, σ1 swaps the second 2, σ2 swaps the second-last 2, σ3 swaps the last 2

n = 7

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

nfac = 5040

def mkmat():
    row = []
    col = []
    data = []
    for j in range(nfac):
      for i in [σ0(j), σ1(j), σ2(j), σ3(j), σ4(j), σ5(j)]:
          row.append(i)
          col.append(j)
          data.append(1)
    return sparse.coo_matrix((data, (row, col)), shape=(nfac, nfac))

print ("constructing")
mat = mkmat()
print ("constructed")
(evals, evecs) = eigsh(mat.asfptype(), 200)

for e in evals:
      print (e)
