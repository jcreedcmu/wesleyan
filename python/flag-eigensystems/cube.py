from numpy import linalg, dot, transpose

# faces are ±x ±y ±z
# edges of +x are ±y and ±z
# vertices of (+x, +y) are ±z

# so a flag is a permutation and a vector in 2^3.
# σ0 flips the sign of the first elt of the perm in the bitvector
# σ1 does a swap of the first two elts of the perm
# σ2 does a swap of the second two elts of the perm

# So if we divide 48 into 6 × 8, how do σ1 and σ2 act on the 6 part.

# Let's have
# 0 = 021
# 1 = 012
# 2 = 102
# 3 = 120
# 4 = 210
# 5 = 201

# so that which bit σ0 affects is just (x div 2).
# σ2 toggles the parity
# σ1 adds one (mod 6) toggles the parity, then subtracts one (mod 6).

# decomposes a number in [48] into a permutation
# code in [6] and a vertex code in [8].
def decomp(x):
    return (x // 8, x % 8)

# inverse of decomp
def comp(p, v):
    return (p * 8 + v)

def σ0(x):
    (p, v) = decomp(x)
    return comp(p, v ^ (1 << (p // 2)))

def σ1(x):
    (p, v) = decomp(x)
    return comp((((p + 1) ^ 1) - 1) % 6, v)

def σ2(x):
    (p, v) = decomp(x)
    return comp(p ^ 1, v)

def entry(i, j):
  if i == j:
      return -3
  elif i == σ0(j):
      return 1
  elif i == σ1(j):
      return 1
  elif i == σ2(j):
      return 1
  else:
      return 0

def centry(i, j):
  if i in [σ0(j), σ1(j), σ2(j)]:
      return 1
  else:
      return 0
mat = [[centry(i,j) for i in range(48)] for j in range(48) ]
for row in mat:
    print (row)


(x,y) = (linalg.eigh(mat))

y = transpose(y)

for i in range(48):
    print(f"eigenvalue {x[i]}")
    print(f"eigenvector {y[i]}")


# vec = [1 for i in range(48)]

# print (dot(mat, vec))
