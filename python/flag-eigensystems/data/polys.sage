
{{{id=31|
R.<x,a,b,c,d> = ZZ['x,a,b,c,d']; R
///
Multivariate Polynomial Ring in x, a, b, c, d over Integer Ring
}}}

{{{id=42|
poly21 = x^2 - a^2 - b^2 + a * b
///
}}}

{{{id=36|
poly31 = (x^3 + x^2 * (a+b+c) - x * (a^2 + b^2 + c^2 - a*b - b*c - 2*a*c) - (a^3 + b^3 + c^3 - a*c^2 - a^2*c))
///
}}}

{{{id=43|
poly211 = -poly31(-x, a, b, c, d)
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

{{{id=46|
poly2111 = poly41(-x, a, b, c, d)
///
}}}

{{{id=47|
poly2111(x, a, 0, c, d) == (x - a - c - d) * (x + a - c - d) * poly21(x - a, c, d, 0, 0)
///
True
}}}

{{{id=40|
poly41(x,a,0,c,d) ==  (x + a + c + d) * (x - a + c + d) * poly21(x+a, c,d,0,0)
///
True
}}}

{{{id=44|
poly41(x,a,b,c,0) == (x + a + b + c) * poly31
///
True
}}}

{{{id=45|
poly41(x,a,b,0,d) == (x + a + b - d) * (x + a + b + d) * poly21(x + d, b, a, 0, 0)
///
True
}}}

{{{id=48|
poly41.polynomial(x)
///
x^4 + (2*a + 2*b + 2*c + 2*d)*x^3 + (3*a*b + 4*a*c + 3*b*c + 4*a*d + 4*b*d + 3*c*d)*x^2 + (-2*a^3 - 2*b^3 + 2*a^2*c + 4*a*b*c + 2*a*c^2 - 2*c^3 + 2*a^2*d + 4*a*b*d + 2*b^2*d + 4*a*c*d + 4*b*c*d + 2*a*d^2 + 2*b*d^2 - 2*d^3)*x - a^4 - a^3*b - a*b^3 - b^4 + a^2*b*c - b^3*c + 2*a^2*c^2 + a*b*c^2 - b*c^3 - c^4 + a^2*c*d + b^2*c*d - c^3*d + 2*a^2*d^2 + a*b*d^2 + 2*b^2*d^2 + b*c*d^2 - c*d^3 - d^4
}}}

{{{id=49|

///
}}}