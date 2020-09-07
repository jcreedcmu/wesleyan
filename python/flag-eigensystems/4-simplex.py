from numpy import linalg, dot, transpose, add, subtract
from permutation import Permutation
import math
from collections import Counter

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

def σ(m):
    return (lambda x: comp(decomp(x) * pi(m)))

σs = [σ(m) for m in range(n-1)]

def entry(i, j):
    if i in [σ(j) for σ in σs]:
        return 1
    else:
        return 0

mat = [[entry(i,j) for i in range(nfac)] for j in range(nfac) ]

# for row in mat:
#     print (row)

(eigval,y) = (linalg.eigh(mat))

# y = transpose(y)

eigval = [round(x, 9) for x in eigval]
count = Counter(eigval)

print ("""
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|""")
for i in reversed([i for i in count.keys()]):
    print(f"| {count[i]} | {i} |")
