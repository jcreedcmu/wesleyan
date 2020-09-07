
The point of this code is to try to find and understand the
eigensystems of the following sorts of matrices.

The basis of the linear space is the flags of some cartographic
complex.

There is a coeffcient c_k (depending on k) in the i,j entry if the
flags i,j are related by σ_k --- the matrix entry is zero otherwise.

By default I investigate below the case where c_k are all set to 1,
but the general case is interesting.

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

edge in the 2-simplex (σ0,σ1,σ2 coefficients 1,0,1)
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            6 |          2 |
|           12 |          0 |
|            6 |         -2 |
|--------------+------------|
= 3 distinct eigenvalues

edge variant in the 2-simplex (σ0,σ1,σ2 coefficients 1,1/2,1)
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 | 2.5        |
|            3 | 1+ √5/2    |
|            2 | √13 / 2    |
|            3 | 1/2        |
|            3 | -1 + √5/2  |
|--------------+------------|
(plus negatives)

edge variant in the 2-simplex (σ0,σ1,σ2 coefficients 1,1/3,1)
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 | 2 1/3      |
|            3 | 1+ √10/3   |
|            2 | √31 / 3    |
|            3 | 1/3        |
|            3 | -1 + √10/2 |
|--------------+------------|
(plus negatives)

edge variant in the 2-simplex (σ0,σ1,σ2 coefficients 1,1/4,1)
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 | 2.25       |
|            3 | 1+ √17/4   |
|            2 | √57 / 4    |
|            3 | 1/4        |
|            3 | -1 + √17/4 |
|--------------+------------|
(plus negatives)

vertex variant in the 2-simplex (σ0,σ1,σ2 coefficients 1,1,2)
|--------------+----------------------|
| multiplicity | eigenvalue           |
|--------------+----------------------|
|            1 | 3                    |
|            3 | [x^3 - 4x^2 + x + 4] |
|            2 | √7                   |
|            3 | [x^3 - 4x^2 + x + 4] |
|            3 | [x^3 - 4x^2 + x + 4] |
|              |                      |
|--------------+----------------------|
(plus negatives)


That multiplicity-2 root for σ0=1,σ1=s,σ2=s+t is the square root of

|   | t |  0 |  1 |  2 |  3 |  4 |
| s |   |    |    |    |    |    |
|---+---+----+----+----+----+----|
| 1 |   |  3 |  7 | 13 | 21 | 31 |
| 2 |   |  7 | 12 | 19 | 28 | 39 |
| 3 |   | 13 | 19 | 27 | 37 | 49 |
| 4 |   | 21 | 28 | 37 | 48 | 61 |

when t = 0 => s^2 + s + 1
when t = 1 => s^2 + 2s + 4
when t = 2 => s^2 + 3s + 9

so s^2 + s(t+1) + (t + 1)^2
so s^2 + st + s + t^2 + 2t + 1

so if u = t + s, then t = u - s and we get
s^2 + su - s^2 + s + u^2 - 2us + s^2 + 2u - 2s + 1
s^2 + u^2 - s - us + 2u + 1

so if we want to hit σ0=a, σ1=b, σ2=c, we start with
setting s=b/a and u=c/a and then multiply by a^2, so

a^2 + b^2 + c^2 - ab - cb + 2ac

is the square of that eigenvalue.


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

numerically:
|--------------+-------------|
| multiplicity |  eigenvalue |
|--------------+-------------|
|            1 |         4.0 |
|            4 | 3.618033989 |
|            5 | 3.177409681 |
|            4 | 2.618033989 |
|            5 | 2.414213562 |
|            6 | 2.236067977 |
|            5 | 1.855772507 |
|            4 | 1.381966011 |
|            6 |         1.0 |
|            5 | 0.678362826 |
|            5 | 0.414213562 |
|            4 | 0.381966011 |
|--------------+-------------|
|           12 |           0 |
|--------------+-------------|
(plus negatives of all the nonzero values)
= 25 distinct eigenvalues
requires ~1.5s to compute

4-simplex
|--------------+-------------|
| multiplicity |  eigenvalue |
|--------------+-------------|
|            1 |         5.0 |
|            5 | 4.732050808 |
|            9 | 4.427270194 |
|            5 | 4.069784139 |
|            5 |         4.0 |
|            9 | 3.813606503 |
|           10 | 3.732050808 |
|           16 | 3.454255591 |
|            9 | 3.264714295 |
|            5 |         3.0 |
|           16 | 2.898729153 |
|           10 | 2.732050808 |
|            9 | 2.585997781 |
|            5 | 2.487154268 |
|           16 | 2.365452191 |
|            5 | 2.287823967 |
|           15 |         2.0 |
|           16 | 1.874395027 |
|           20 | 1.732050808 |
|            9 |  1.52931658 |
|            9 | 1.503990714 |
|           16 | 1.320744251 |
|            5 | 1.267949192 |
|           25 |         1.0 |
|            9 | 0.754422499 |
|           10 | 0.732050808 |
|           16 |  0.69597049 |
|           16 |  0.55734028 |
|            9 | 0.471585945 |
|            9 | 0.342923083 |
|           10 | 0.267949192 |
|           16 | 0.131902754 |
|            5 | 0.129546162 |
|--------------+-------------|
|           20 |           0 |
|--------------+-------------|
(plus negatives of all the nonzero values)
= 67 distinct eigenvalues
requires ~63s to compute

5-simplex can't compute the whole spectrum yet, but the top of it
looks like
|--------------+------------|
| multiplicity | eigenvalue |
|--------------+------------|
|            1 |    6.00000 |
|            6 |    5.80193 |
|           14 |    5.57954 |
|           14 |    5.32375 |
|            6 |    5.24697 |
|           14 |    5.09182 |
|           15 |    5.04891 |
|           14 |    4.92432 |
|          ... |        ... |
|--------------+------------|

Multiplicity of nth biggest eigenvalue goes
1 1 1 1 1  1
  2 3 4 5  6
    2 5 9  14
    3 4 5  14
    3 5 5  6
      6 9  14
      5 10 15

Number of distinct eigenvalues goes
1 2 4 10 25 67 ???

---

Characteristic polynomial of the 1-simplex with σ0=a,σ1=b

(x - a - b)
(x + a + b)
(x^2 - (a^2 + b^2 - ab))^2

Characteristic polynomial of the 2-simplex:

(x - a - b - c)
(x + a + b + c)
(x^2 - (a^2 + b^2 + c^2 - ab - cb + 2ac))^2
(x^3 + (a + b + c)x^2 - (a^2 + b^2 + c^2 - ab - bc - 2ac)x - (a^3 + b^3 + c^3 - ac^2 - a^2c))^3
(x^3 - (a + b + c)x^2 - (a^2 + b^2 + c^2 - ab - bc - 2ac)x + (a^3 + b^3 + c^3 - ac^2 - a^2c))^3
