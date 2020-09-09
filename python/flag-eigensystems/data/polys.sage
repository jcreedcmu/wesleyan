
{{{id=31|
R.<x,a,b,c,d> = ZZ['x,a,b,c,d']; R
///
Multivariate Polynomial Ring in x, a, b, c, d over Integer Ring
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
///
}}}

{{{id=39|
poly41 = (x^4 + 2 * x^3 * (a+b+c+d) + x^2 * (3*a*b + 3*b*c + 3*c*d + 4*a*c + 4*b*d + 4*a*d) + x * (4 * (a*b*d + a*c*d + a*b*c + b*c*d)
 + 2 * (a^2 * c + a * c^2 + b^2 * d + b * d^2 + a^2 * d + a * d^2)
 - 2 * (a^3 + b^3 + c^3 + d^3))
 - (a^4 + b^4 + c^4 + d^4)
 + (a^2 * b * c + a * b * c^2 + b^2 * c * d + b * c * d^2 + a^2 * c * d + a * b * d^2)
 - (a^3 * b + a * b^3 + b^3 * c + b * c^3 + c^3 * d + c * d^3)
 + 2 * (a^2 * c^2 + b^2 * d^2 + a^2 * d^2))
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

{{{id=58|
p = poly31.polynomial(x).subs(a=0.1,b=0.22,c=0.35,d=0.9)
///
}}}

{{{id=62|
p.coefficients()
///
[-0.0387730000000000, -0.0119000000000000, 0.670000000000000, 1.00000000000000]
}}}

{{{id=64|
R.<t> = RR['t']; R
///
Univariate Polynomial Ring in t over Real Field with 53 bits of precision
}}}

{{{id=65|
ps = sum((c.constant_coefficient())*t^j for (j,c) in enumerate(p.coefficients()))
///
}}}

{{{id=66|
ps
///
t^3 + 0.670000000000000*t^2 - 0.0119000000000000*t - 0.0387730000000000
}}}

{{{id=67|
ps.real_roots()
///
[-0.572480334665219, -0.313534476334505, 0.216014810999724]
}}}

{{{id=68|

///
}}}