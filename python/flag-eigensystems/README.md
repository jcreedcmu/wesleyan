
The point of this code is to try to find and understand the
eigensystems of the following sorts of matrices.

The basis of the linear space is the flags of some cartographic
complex.

There is a 1 in the i,j entry of the matrix if flags i and j are
related by *some* σk flip.

I'm not really sure I've got cube.py right at time of writing. I see,
as I expect, one eigenvector each of eigenvalue -3 and 3,
corresponding to the alternating and uniform vectors on the cube, but
surprisingly I see three eigenvectors at eigenvalue 1+√3, and they are
so asymmetric that I'd expect to see more.
