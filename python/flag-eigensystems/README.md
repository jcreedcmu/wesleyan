
The point of this code is to try to find and understand the
eigensystems of the following sorts of matrices.

The basis of the linear space is the flags of some cartographic
complex.

There is a coeffcient c_k (depending on k) in the i,j entry if the
flags i,j are related by σ_k --- the matrix entry is zero otherwise.

By default I investigate below the case where c_k are all set to 1,
but the general case is interesting.

---


Multiplicity of nth biggest eigenvalue goes
1 1 1 1 1  1
  2 3 4 5  6
    2 5 9  14
    3 4 5  14
    3 5 5  6
      6 9  14
      5 10 15

Number of distinct eigenvalues of n-simplex
0 1 2  3  4  5
2 4 10 25 67 222

Number of distinct eigenvalues of n-simplex
when I count 0 as two separate eigenvalues:

0 1 2  3  4  5
2 4 10 26 68 222
1 2 5  13 34 111

can't find any of these in oeis :(
