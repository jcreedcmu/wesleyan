
The point of this code is to try to find and understand the
eigensystems of the following sorts of matrices.

The basis of the linear space is the flags of some cartographic
complex.

There is a 1 in the i,j entry of the matrix if flags i and j are
related by *some* σk flip.

---

spectra of:

0-simplex
[0 1]
[1 0]
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 |          1 |
|            1 |         -1 |
|--------------+------------|
= 2 distinct eigenvalues

1-simplex
[0 1 0 0 0 1]
[1 0 1 0 0 0]
[0 1 0 1 0 0]
[0 0 1 0 1 0]
[0 0 0 1 0 1]
[1 0 0 0 1 0]
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 |          2 |
|            2 |          1 |
|            2 |         -1 |
|            1 |         -2 |
|--------------+------------|

eigenbasis
|--------------------+------------|
| vector             | eigenvalue |
|--------------------+------------|
| [1  1  1  1  1  1] |          2 |
| [1  1  0 -1 -1  0] |          1 |
| [0  1  1  0 -1 -1] |          1 |
| [0 -1  1  0 -1  1] |         -1 |
| [1 -1  0  1 -1  0] |         -1 |
| [1 -1  1 -1  1 -1] |          2 |
|--------------------+------------|

= 4 distinct eigenvalues

2-simplex
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 | 3          |
|            3 | 1 + √2     |
|            2 | √3         |
|            3 | 1          |
|            3 | -1 + √2    |
|--------------+------------|
(plus negatives of all these roots)
= 10 distinct eigenvalues

3-simplex
|--------------+-----------------------|
| multiplicity | eigenvalue            |
|--------------+-----------------------|
|            1 | 4                     |
|            4 | (5 + √5)/2            |
|            5 | r1[x³ + 2x² - 5x - 4] |
|            4 | (3 + √5)/2            |
|            5 | 1 + √2                |
|            6 | √5                    |
|            5 | r2[x³ + 2x² - 5x - 4] |
|            4 | (5 - √5)/2            |
|            6 | 1                     |
|            5 | r3[x³ + 2x² - 5x - 4] |
|            5 | -1 + √2               |
|            4 | (-3 + √5)/2           |
|--------------+-----------------------|
|           12 | 0                     |
|--------------+-----------------------|
(plus negatives of all the nonzero values)
= 25 distinct eigenvalues

4-simplex
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 |          5 |
|            5 |     4.7321 |
|            9 |     4.4273 |
|            5 |     4.0698 |
|            5 |          4 |
|            9 |     3.8136 |
|           10 |     3.7321 |
|           16 |     3.4543 |
|            9 |     3.2647 |
|            5 |          3 |
|           16 |     2.8987 |
|           10 |     2.7321 |
|            9 |      2.586 |
|            5 |     2.4872 |
|           16 |     2.3655 |
|            5 |     2.2878 |
|           15 |          2 |
|           16 |     1.8744 |
|           20 |     1.7321 |
|            9 |     1.5293 |
|            9 |      1.504 |
|           16 |     1.3207 |
|            5 |     1.2679 |
|           25 |          1 |
|            9 |     0.7544 |
|           10 |     0.7321 |
|           16 |      0.696 |
|           16 |     0.5573 |
|            9 |     0.4716 |
|            9 |     0.3429 |
|           10 |     0.2679 |
|           16 |     0.1319 |
|            5 |     0.1295 |
|--------------+------------|
|           20 |          0 |
|--------------+------------|
(plus negatives of all the nonzero values)
= 67 distinct eigenvalues

1 2 4 10 25 67
