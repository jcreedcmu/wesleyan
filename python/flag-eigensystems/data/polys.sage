
{{{id=0|
R.<x,a,b,c,d,e> = ZZ['x,a,b,c,d,e']; R
///
Multivariate Polynomial Ring in x, a, b, c, d, e over Integer Ring
}}}

{{{id=50|
poly1 = x

poly11 = x - a
poly2 = x + a

poly21 = x^2 - a^2 - b^2 + a * b
poly3 = x + a + b
poly111 = x - a - b

poly4 = x + a + b + c
poly1111 = x - a - b - c
poly31 = x^3 + x^2 * (a+b+c) - x * (a^2 + b^2 + c^2 - a*b - b*c - 2*a*c) - (a^3 + b^3 + c^3 - a*c^2 - a^2*c)
poly211 = -poly31.subs(x=-x)
poly22 = x^2 - a^2 - b^2 - c^2 + a * b + b * c - 2 * a * c

poly5 = x + a + b + c + d
///
}}}

{{{id=39|
poly41 = (1 * x^4 * (1) +
 2 * x^3 * (a + b + c + d) +
 3 * x^2 * (a*b + b*c + c*d) +
 4 * x^2 * (a*c + a*d + b*d) +
 -2 * x * (a^3 + b^3 + c^3 + d^3) +
 2 * x * (a^2*c + a^2*d + a*c^2 + a*d^2 + b^2*d + b*d^2) +
 4 * x * (a*b*d + a*c*d) +
 4 * x * (a*b*c + b*c*d) +
 -1 * (a^4 + b^4 + c^4 + d^4) +
 -1 * (a^3*b + a*b^3 + b^3*c + b*c^3 + c^3*d + c*d^3) +
 1 * (a^2*c*d + a*b*d^2) +
 1 * (a^2*b*c + a*b*c^2 + b^2*c*d + b*c*d^2) +
 3 * (a*b*c*d) +
 2 * (a^2*c^2 + a^2*d^2 + b^2*d^2))
///
}}}

{{{id=105|
poly32 = (-2 * x * (a^2*b*c + a*b*c^2 + b^2*c*d + b*c*d^2) +
 1 * x^5 * (1) +
 1 * (a^5 + b^5 + c^5 + d^5) +
 1 * x^4 * (a + b + c + d) +
 1 * x * (a^4 + b^4 + c^4 + d^4) +
 1 * (a^4*c + a^4*d + a*c^4 + a*d^4 + b^4*d + b*d^4) +
 -2 * (a^3*c^2 + a^3*d^2 + a^2*c^3 + a^2*d^3 + b^3*d^2 + b^2*d^3) +
 -2 * x^3 * (a^2 + b^2 + c^2 + d^2) +
 -2 * x^2 * (a^3 + b^3 + c^3 + d^3) +
 2 * (a^3*c*d + a*b*d^3) +
 2 * x^3 * (a*b + b*c + c*d) +
 -2 * x^2 * (a^2*c + a^2*d + a*c^2 + a*d^2 + b^2*d + b*d^2) +
 -2 * x * (a^2*c^2 + a^2*d^2 + b^2*d^2) +
 2 * x^2 * (a*b*d + a*c*d) +
 2 * x * (a^2*c*d + a*b*d^2) +
 -2 * (a^3*b*d + a*b^3*d + a*c^3*d + a*c*d^3) +
 -2 * x * (a^3*b + a*b^3 + b^3*c + b*c^3 + c^3*d + c*d^3) +
 3 * (a^2*b^2*d + a*c^2*d^2) +
 3 * x * (a^2*b^2 + b^2*c^2 + c^2*d^2) +
 2 * x * (a*b^2*c + b*c^2*d) +
 2 * x * (a*b*c*d) +
 -1 * (a^4*b + a*b^4 + b^4*c + b*c^4 + c^4*d + c*d^4) +
 1 * (a^3*b^2 + a^2*b^3 + b^3*c^2 + b^2*c^3 + c^3*d^2 + c^2*d^3) +
 -1 * (a^2*b^2*c + a*b^2*c^2 + b^2*c^2*d + b*c^2*d^2) +
 2 * (a^2*b*c^2 + b^2*c*d^2) +
 2 * (a*b^3*c + b*c^3*d) +
 -2 * (a^2*b*c*d + a*b*c*d^2) +
 2 * (a*b^2*c*d + a*b*c^2*d))
///
}}}

{{{id=44|
poly41.subs(d=0) == poly4 * poly31
///
True
}}}

{{{id=45|
poly41.subs(c=0) == (x + a + b - d) * (x + a + b + d) * poly21.subs(x=x+d)
///
True
}}}

{{{id=51|
poly31.subs(c=0) == poly3 * poly21
///
True
}}}

{{{id=52|
poly31.subs(b=0) == (x + a + c) * (x - a + c) * (x + a - c)
///
True
}}}

{{{id=57|
poly22.subs(c=0) == poly21
///
True
}}}

{{{id=75|
poly32.subs(d=0) == poly31 * poly22
///
True
}}}

{{{id=115|
poly32.subs(c=0) == poly3.subs(x=x+d) * poly21.subs(x=x+d) * poly21.subs(x=x-d)
///
True
}}}
