
{{{id=0|
R.<x,a,b,c,d,e> = ZZ['x,a,b,c,d,e']; R
R.<t> = RR['t']; R
///
Univariate Polynomial Ring in t over Real Field with 53 bits of precision
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
poly11111 = x - a - b - c - d
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

{{{id=133|
poly311 = (-2 * (a^3*b^3 + b^3*c^3 + c^3*d^3) +
 -2 * (a^4*b*d + a*b^4*d + a*c^4*d + a*c*d^4) +
 -3 * x^4 * (a^2 + b^2 + c^2 + d^2) +
 -4 * x^2 * (a^3*c + a^3*d + a*c^3 + a*d^3 + b^3*d + b*d^3) +
 -1 * (a^6 + b^6 + c^6 + d^6) +
 2 * x^4 * (a*c + a*d + b*d) +
 2 * x^2 * (a^2*c^2 + a^2*d^2 + b^2*d^2) +
 2 * (a^3*b^2*d + a^2*b^3*d + a*c^3*d^2 + a*c^2*d^3) +
 2 * (a^5*c + a^5*d + a*c^5 + a*d^5 + b^5*d + b*d^5) +
 3 * x^2 * (a^2*b^2 + b^2*c^2 + c^2*d^2) +
 3 * x^2 * (a^4 + b^4 + c^4 + d^4) +
 1 * (a^4*c^2 + a^4*d^2 + a^2*c^4 + a^2*d^4 + b^4*d^2 + b^2*d^4) +
 1 * x^6 * (1) +
 4 * x^2 * (a^2*c*d + a*b*d^2) +
 4 * (a^3*b*d^2 + a^2*c^3*d + a^2*c*d^3 + a*b^3*d^2) +
 -3 * (a^2*b^2*d^2 + a^2*c^2*d^2) +
 -4 * (a^3*c^3 + a^3*d^3 + b^3*d^3) +
 -4 * (a^4*c*d + a*b*d^4) +
 -2 * x^2 * (a*b^2*c + b*c^2*d) +
 2 * (a^2*b^3*c + a*b^3*c^2 + b^2*c^3*d + b*c^3*d^2) +
 -2 * x^2 * (a*b*c*d) +
 2 * (a^3*b*c*d + a*b*c*d^3) +
 -4 * (a^2*b*c*d^2) +
 2 * (a^2*b*c^2*d + a*b^2*c*d^2) +
 -2 * (a^2*b^2*c*d + a*b*c^2*d^2) +
 -2 * (a*b^2*c^2*d) +
 -2 * (a*b^3*c*d + a*b*c^3*d))
///
}}}

{{{id=127|
poly2111 = poly41.subs(x=-x)
poly221 = -poly32.subs(x=-x)
///
}}}

{{{id=138|
poly51 = (1 * x^5 * (1) +
 14 * x^2 * (a*b*c + b*c*d + c*d*e) +
 15 * x^2 * (a*b*d + a*b*e + a*c*d + a*d*e + b*c*e + b*d*e) +
 16 * x^2 * (a*c*e) +
 19 * x * (a*b*c*d + b*c*d*e) +
 1 * (a^2*b^2*c + a*b^2*c^2 + b^2*c^2*d + b*c^2*d^2 + c^2*d^2*e + c*d^2*e^2) +
 1 * (a^3*c*d + a^3*d*e + a*b*d^3 + a*b*e^3 + b^3*d*e + b*c*e^3) +
 20 * x * (a*b*c*e + a*c*d*e) +
 2 * (a^2*c^2*e + a^2*c*e^2 + a*c^2*e^2) +
 2 * x^3 * (a^2 + b^2 + c^2 + d^2 + e^2) +
 2 * (a^3*c^2 + a^3*d^2 + a^3*e^2 + a^2*c^3 + a^2*d^3 + a^2*e^3 + b^3*d^2 + b^3*e^2 + b^2*d^3 + b^2*e^3 + c^3*e^2 + c^2*e^3) +
 3 * x^4 * (a + b + c + d + e) +
 3 * (a^2*b*d^2 + a^2*b*e^2 + a^2*c^2*d + a^2*c*d^2 + a^2*d^2*e + a^2*d*e^2 + a*b^2*d^2 + a*b^2*e^2 + b^2*c*e^2 + b^2*d^2*e + b^2*d*e^2 + b*c^2*e^2) +
 3 * x^2 * (a^2*b + a*b^2 + b^2*c + b*c^2 + c^2*d + c*d^2 + d^2*e + d*e^2) +
 4 * (a*b^2*c*d + a*b*c^2*d + b*c^2*d*e + b*c*d^2*e) +
 4 * (a*b^2*c*e + a*c*d^2*e) +
 4 * x * (a*b^2*c + b*c^2*d + c*d^2*e) +
 4 * (a^2*b*c^2 + b^2*c*d^2 + c^2*d*e^2) +
 5 * (a^2*b*c*e + a*b*c^2*e + a*c^2*d*e + a*c*d*e^2) +
 5 * (a^2*b*c*d + a*b*c*d^2 + b^2*c*d*e + b*c*d*e^2) +
 6 * x^2 * (a^2*c + a^2*d + a^2*e + a*c^2 + a*d^2 + a*e^2 + b^2*d + b^2*e + b*d^2 + b*e^2 + c^2*e + c*e^2) +
 6 * x * (a^2*c^2 + a^2*d^2 + a^2*e^2 + b^2*d^2 + b^2*e^2 + c^2*e^2) +
 6 * x * (a^2*b*d + a^2*b*e + a*b^2*d + a*b^2*e + a*c^2*d + a*c*d^2 + a*d^2*e + a*d*e^2 + b^2*c*e + b*c^2*e + b*d^2*e + b*d*e^2) +
 6 * (a^2*c*d*e + a*b*c*e^2) +
 7 * x^3 * (a*b + b*c + c*d + d*e) +
 7 * x * (a^2*b*c + a*b*c^2 + b^2*c*d + b*c*d^2 + c^2*d*e + c*d*e^2) +
 8 * x^3 * (a*c + a*d + a*e + b*d + b*e + c*e) +
 8 * x * (a^2*c*e + a*c^2*e + a*c*e^2) +
 9 * x * (a^2*c*d + a^2*d*e + a*b*d^2 + a*b*e^2 + b^2*d*e + b*c*e^2) +
 -2 * (a*b^3*c + b*c^3*d + c*d^3*e) +
 -2 * x^2 * (a^3 + b^3 + c^3 + d^3 + e^3) +
 -2 * (a^4*b + a*b^4 + b^4*c + b*c^4 + c^4*d + c*d^4 + d^4*e + d*e^4) +
 -3 * x * (a^3*b + a*b^3 + b^3*c + b*c^3 + c^3*d + c*d^3 + d^3*e + d*e^3) +
 -3 * x * (a^4 + b^4 + c^4 + d^4 + e^4) +
 -1 * (a^3*b*d + a^3*b*e + a*b^3*d + a*b^3*e + a*c^3*d + a*c*d^3 + a*d^3*e + a*d*e^3 + b^3*c*e + b*c^3*e + b*d^3*e + b*d*e^3) +
 -1 * (a^3*b^2 + a^2*b^3 + b^3*c^2 + b^2*c^3 + c^3*d^2 + c^2*d^3 + d^3*e^2 + d^2*e^3) +
 -1 * (a^4*c + a^4*d + a^4*e + a*c^4 + a*d^4 + a*e^4 + b^4*d + b^4*e + b*d^4 + b*e^4 + c^4*e + c*e^4) +
 -1 * (a^5 + b^5 + c^5 + d^5 + e^5) +
 6 * (a^2*b*d*e + a*b^2*d*e + a*b*d^2*e + a*b*d*e^2) +
 21 * x * (a*b*d*e) +
 13 * (a*b*c*d*e))
///
}}}

{{{id=146|
poly33 = (-1 * (a^2*b^2*c + a*b^2*c^2 + b^2*c^2*d + b*c^2*d^2 + c^2*d^2*e + c*d^2*e^2) +
 -1 * (a^4*b + a*b^4 + b^4*c + b*c^4 + c^4*d + c*d^4 + d^4*e + d*e^4) +
 -2 * x^2 * (a^2*c + a^2*d + a^2*e + a*c^2 + a*d^2 + a*e^2 + b^2*d + b^2*e + b*d^2 + b*e^2 + c^2*e + c*e^2) +
 -2 * (a^2*c^2*e + a^2*c*e^2 + a*c^2*e^2) +
 -2 * x * (a^2*c^2 + a^2*d^2 + a^2*e^2 + b^2*d^2 + b^2*e^2 + c^2*e^2) +
 -2 * (a^2*b*c*e + a*b*c^2*e + a*c^2*d*e + a*c*d*e^2) +
 -2 * (a^2*b*c*d + a*b*c*d^2 + b^2*c*d*e + b*c*d*e^2) +
 -2 * x * (a^2*b*c + a*b*c^2 + b^2*c*d + b*c*d^2 + c^2*d*e + c*d*e^2) +
 -2 * x^3 * (a^2 + b^2 + c^2 + d^2 + e^2) +
 -2 * (a^3*c^2 + a^3*d^2 + a^3*e^2 + a^2*c^3 + a^2*d^3 + a^2*e^3 + b^3*d^2 + b^3*e^2 + b^2*d^3 + b^2*e^3 + c^3*e^2 + c^2*e^3) +
 -2 * (a^3*b*d + a^3*b*e + a*b^3*d + a*b^3*e + a*c^3*d + a*c*d^3 + a*d^3*e + a*d*e^3 + b^3*c*e + b*c^3*e + b*d^3*e + b*d*e^3) +
 -2 * x * (a^3*b + a*b^3 + b^3*c + b*c^3 + c^3*d + c*d^3 + d^3*e + d*e^3) +
 -2 * x^2 * (a^3 + b^3 + c^3 + d^3 + e^3) +
 -8 * x^2 * (a*c*e) +
 -8 * x * (a^2*c*e + a*c^2*e + a*c*e^2) +
 1 * x^4 * (a + b + c + d + e) +
 1 * (a^3*b^2 + a^2*b^3 + b^3*c^2 + b^2*c^3 + c^3*d^2 + c^2*d^3 + d^3*e^2 + d^2*e^3) +
 1 * (a^4*c + a^4*d + a^4*e + a*c^4 + a*d^4 + a*e^4 + b^4*d + b^4*e + b*d^4 + b*e^4 + c^4*e + c*e^4) +
 1 * x * (a^4 + b^4 + c^4 + d^4 + e^4) +
 1 * (a^5 + b^5 + c^5 + d^5 + e^5) +
 1 * x^5 * (1) +
 2 * x^2 * (a*b*d + a*b*e + a*c*d + a*d*e + b*c*e + b*d*e) +
 2 * x * (a*b*c*d + b*c*d*e) +
 2 * x^3 * (a*b + b*c + c*d + d*e) +
 2 * (a*b^2*c*e + a*c*d^2*e) +
 2 * (a*b^2*c*d + a*b*c^2*d + b*c^2*d*e + b*c*d^2*e) +
 2 * x * (a*b^2*c + b*c^2*d + c*d^2*e) +
 2 * (a*b^3*c + b*c^3*d + c*d^3*e) +
 2 * x * (a^2*c*d + a^2*d*e + a*b*d^2 + a*b*e^2 + b^2*d*e + b*c*e^2) +
 2 * (a^2*b*c^2 + b^2*c*d^2 + c^2*d*e^2) +
 2 * (a^3*c*d + a^3*d*e + a*b*d^3 + a*b*e^3 + b^3*d*e + b*c*e^3) +
 3 * (a^2*b^2*d + a^2*b^2*e + a*c^2*d^2 + a*d^2*e^2 + b^2*c^2*e + b*d^2*e^2) +
 3 * x * (a^2*b^2 + b^2*c^2 + c^2*d^2 + d^2*e^2) +
 -2 * x * (a*b*d*e) +
 2 * (a*b*c*d*e))
///
}}}

{{{id=157|
mystery = (1 * x^4 * (1) +
 1 * (a^4 + b^4 + c^4 + d^4 + e^4) +
 2 * (a^2*c*d + a^2*d*e + a*b*d^2 + a*b*e^2 + b^2*d*e + b*c*e^2) +
 2 * x^2 * (a*b + b*c + c*d + d*e) +
 3 * (a^2*b^2 + b^2*c^2 + c^2*d^2 + d^2*e^2) +
 -2 * (a*b*d*e) +
 -2 * (a^3*b + a*b^3 + b^3*c + b*c^3 + c^3*d + c*d^3 + d^3*e + d*e^3) +
 -2 * (a^2*c^2 + a^2*d^2 + a^2*e^2 + b^2*d^2 + b^2*e^2 + c^2*e^2) +
 -2 * x^2 * (a^2 + b^2 + c^2 + d^2 + e^2))
///
}}}

{{{id=149|
all([
 poly21(a=0)   == poly1(x=x+b) * poly1(x=x-b),
 #
 poly22(b=0)   == poly2(x=x+c) * poly11(x=x-c),
 poly22(c=0)   == poly21,
 poly31(b=0)   == poly2(x=x+c) * poly11(x=x+c) * poly2(x=x-c),
 poly31(c=0)   == poly3 * poly21,
 #
 poly5(c=0)    == poly3(x=x+d),
 #
 poly41(d=0)   == poly4 * poly31,
 poly41(c=0)   == poly3(x=x-d) * poly3(x=x+d) * poly21(x=x+d),
 poly41(b=0)   == (poly3(a=c,b=d)-a) * (poly3(a=c,b=d)+a) * poly21(x=x+a,a=c,b=d),
 #
 poly32(d=0)   == poly31 * poly22,
 poly32(c=0)   == poly3(x=x+d) * poly21(x=x+d) * poly21(x=x-d),
 poly32(b=0)   == (poly3(a=c,b=d) + a) * poly21(x=x+a,a=c,b=d) * poly21(x=x-a,a=c,b=d),
 #
 poly311(d=0)  == poly31 * poly211,
 poly311(c=0)  == poly3(x=x-d) * poly111(x=x+d) * poly21(x=x+d) * poly21(x=x-d),
 #
 poly2111(d=0) == poly1111 * poly211,
 poly2111(c=0) == poly111(x=x-d) * poly111(x=x+d) * poly21(x=x-d),
 #
 poly51(e=0)   == poly5 * poly41,
 poly51(d=0)   == poly4(x=x-e) * poly4(x=x+e) * poly31(x=x+e),
 poly51(c=0)   == poly21(x=poly3(a=d,b=e)) * poly3(x=poly3(a=d,b=e)) * poly21(x=poly3,a=d,b=e),
 #
 poly33(e=0)   == poly32,
 poly33(d=0)   == poly31(x=x+e) * poly22(x=x-e),
 poly33(c=0)   == poly3(x=poly3,a=d,b=e) * mystery(c=0),
 ])
///
True
}}}