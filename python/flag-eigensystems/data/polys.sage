
{{{id=0|
R.<x,a,b,c,d,e,f> = ZZ['x,a,b,c,d,e,f']; R
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
poly6 = x + a + b + c + d + e
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
 poly41(b=0)   == poly11(x=poly3(a=c,b=d)) * poly2(x=poly3(a=c,b=d)) * poly21(x=poly2,a=c,b=d),
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

{{{id=164|
poly61 = (-1 * (a^4*c*d + a^4*d*e + a^4*e*f + a*b*d^4 + a*b*e^4 + a*b*f^4 + b^4*d*e + b^4*e*f + b*c*e^4 + b*c*f^4 + c^4*e*f + c*d*f^4) +
 -1 * (a^6 + b^6 + c^6 + d^6 + e^6 + f^6) +
 -2 * (a^2*b^3*c + a*b^3*c^2 + b^2*c^3*d + b*c^3*d^2 + c^2*d^3*e + c*d^3*e^2 + d^2*e^3*f + d*e^3*f^2) +
 -2 * x^2 * (a^3*b + a*b^3 + b^3*c + b*c^3 + c^3*d + c*d^3 + d^3*e + d*e^3 + e^3*f + e*f^3) +
 -2 * (a^3*b^2*d + a^3*b^2*e + a^3*b^2*f + a^2*b^3*d + a^2*b^3*e + a^2*b^3*f + a*c^3*d^2 + a*c^2*d^3 + a*d^3*e^2 + a*d^2*e^3 + a*e^3*f^2 + a*e^2*f^3 + b^3*c^2*e + b^3*c^2*f + b^2*c^3*e + b^2*c^3*f + b*d^3*e^2 + b*d^2*e^3 + b*e^3*f^2 + b*e^2*f^3 + c^3*d^2*f + c^2*d^3*f + c*e^3*f^2 + c*e^2*f^3) +
 -2 * (a^3*b^3 + b^3*c^3 + c^3*d^3 + d^3*e^3 + e^3*f^3) +
 -2 * (a^4*c*e + a^4*c*f + a^4*d*f + a*c^4*e + a*c^4*f + a*c*e^4 + a*c*f^4 + a*d^4*f + a*d*f^4 + b^4*d*f + b*d^4*f + b*d*f^4) +
 -2 * (a^5*c + a^5*d + a^5*e + a^5*f + a*c^5 + a*d^5 + a*e^5 + a*f^5 + b^5*d + b^5*e + b^5*f + b*d^5 + b*e^5 + b*f^5 + c^5*e + c^5*f + c*e^5 + c*f^5 + d^5*f + d*f^5) +
 -3 * (a^4*b*c + a*b*c^4 + b^4*c*d + b*c*d^4 + c^4*d*e + c*d*e^4 + d^4*e*f + d*e*f^4) +
 -3 * (a^4*b^2 + a^2*b^4 + b^4*c^2 + b^2*c^4 + c^4*d^2 + c^2*d^4 + d^4*e^2 + d^2*e^4 + e^4*f^2 + e^2*f^4) +
 -3 * (a^5*b + a*b^5 + b^5*c + b*c^5 + c^5*d + c*d^5 + d^5*e + d*e^5 + e^5*f + e*f^5) +
 -4 * x * (a*b^3*c + b*c^3*d + c*d^3*e + d*e^3*f) +
 -4 * x * (a^3*b^2 + a^2*b^3 + b^3*c^2 + b^2*c^3 + c^3*d^2 + c^2*d^3 + d^3*e^2 + d^2*e^3 + e^3*f^2 + e^2*f^3) +
 -4 * x * (a^4*c + a^4*d + a^4*e + a^4*f + a*c^4 + a*d^4 + a*e^4 + a*f^4 + b^4*d + b^4*e + b^4*f + b*d^4 + b*e^4 + b*f^4 + c^4*e + c^4*f + c*e^4 + c*f^4 + d^4*f + d*f^4) +
 -4 * (a^4*b*d + a^4*b*e + a^4*b*f + a*b^4*d + a*b^4*e + a*b^4*f + a*c^4*d + a*c*d^4 + a*d^4*e + a*d*e^4 + a*e^4*f + a*e*f^4 + b^4*c*e + b^4*c*f + b*c^4*e + b*c^4*f + b*d^4*e + b*d*e^4 + b*e^4*f + b*e*f^4 + c^4*d*f + c*d^4*f + c*e^4*f + c*e*f^4) +
 -4 * x * (a^5 + b^5 + c^5 + d^5 + e^5 + f^5) +
 -5 * x^2 * (a^4 + b^4 + c^4 + d^4 + e^4 + f^4) +
 -6 * (a*b^4*c + b*c^4*d + c*d^4*e + d*e^4*f) +
 -8 * x * (a^4*b + a*b^4 + b^4*c + b*c^4 + c^4*d + c*d^4 + d^4*e + d*e^4 + e^4*f + e*f^4) +
 1 * (a*b^3*c*d + a*b*c^3*d + b*c^3*d*e + b*c*d^3*e + c*d^3*e*f + c*d*e^3*f) +
 1 * (a^4*c^2 + a^4*d^2 + a^4*e^2 + a^4*f^2 + a^2*c^4 + a^2*d^4 + a^2*e^4 + a^2*f^4 + b^4*d^2 + b^4*e^2 + b^4*f^2 + b^2*d^4 + b^2*e^4 + b^2*f^4 + c^4*e^2 + c^4*f^2 + c^2*e^4 + c^2*f^4 + d^4*f^2 + d^2*f^4) +
 1 * x^6 * (1) +
 10 * (a*b^2*c^2*d + b*c^2*d^2*e + c*d^2*e^2*f) +
 10 * (a^2*b^2*c*e + a^2*b^2*c*f + a*b^2*c^2*e + a*b^2*c^2*f + a*c^2*d^2*e + a*c*d^2*e^2 + a*d^2*e^2*f + a*d*e^2*f^2 + b^2*c^2*d*f + b*c^2*d^2*f + b*d^2*e^2*f + b*d*e^2*f^2) +
 10 * (a^2*b^2*c*d + a*b*c^2*d^2 + b^2*c^2*d*e + b*c*d^2*e^2 + c^2*d^2*e*f + c*d*e^2*f^2) +
 10 * x * (a^3*c*d + a^3*d*e + a^3*e*f + a*b*d^3 + a*b*e^3 + a*b*f^3 + b^3*d*e + b^3*e*f + b*c*e^3 + b*c*f^3 + c^3*e*f + c*d*f^3) +
 112 * x * (a*b*c*d*e + b*c*d*e*f) +
 116 * x * (a*b*c*e*f + a*b*d*e*f) +
 116 * x * (a*b*c*d*f + a*c*d*e*f) +
 12 * x^3 * (a^2*b + a*b^2 + b^2*c + b*c^2 + c^2*d + c*d^2 + d^2*e + d*e^2 + e^2*f + e*f^2) +
 12 * (a^2*b^2*d*f + a*c^2*d^2*f + a*c*e^2*f^2) +
 12 * (a^2*b^2*d*e + a^2*b^2*e*f + a*b*d^2*e^2 + a*b*e^2*f^2 + b^2*c^2*e*f + b*c*e^2*f^2) +
 12 * x * (a^2*b^2*d + a^2*b^2*e + a^2*b^2*f + a*c^2*d^2 + a*d^2*e^2 + a*e^2*f^2 + b^2*c^2*e + b^2*c^2*f + b*d^2*e^2 + b*e^2*f^2 + c^2*d^2*f + c*e^2*f^2) +
 12 * x * (a^2*b^2*c + a*b^2*c^2 + b^2*c^2*d + b*c^2*d^2 + c^2*d^2*e + c*d^2*e^2 + d^2*e^2*f + d*e^2*f^2) +
 13 * x^4 * (a*b + b*c + c*d + d*e + e*f) +
 14 * x^4 * (a*c + a*d + a*e + a*f + b*d + b*e + b*f + c*e + c*f + d*f) +
 16 * (a^2*c*d^2*e + a^2*d*e^2*f + a*b^2*c*e^2 + a*b^2*c*f^2 + b^2*d*e^2*f + b*c^2*d*f^2) +
 16 * x^3 * (a^2*c + a^2*d + a^2*e + a^2*f + a*c^2 + a*d^2 + a*e^2 + a*f^2 + b^2*d + b^2*e + b^2*f + b*d^2 + b*e^2 + b*f^2 + c^2*e + c^2*f + c*e^2 + c*f^2 + d^2*f + d*f^2) +
 16 * (a^2*b*c*e^2 + a^2*b*c*f^2 + a^2*c^2*d*e + a^2*c*d*e^2 + a^2*d^2*e*f + a^2*d*e*f^2 + a*b*c^2*e^2 + a*b*c^2*f^2 + b^2*c*d*f^2 + b^2*d^2*e*f + b^2*d*e*f^2 + b*c*d^2*f^2) +
 16 * (a^2*b*c*d^2 + b^2*c*d*e^2 + c^2*d*e*f^2) +
 16 * (a^2*b*c^2*e + a^2*b*c^2*f + a*c^2*d*e^2 + a*d^2*e*f^2 + b^2*c*d^2*f + b*d^2*e*f^2) +
 16 * (a^2*b*c^2*d + a*b^2*c*d^2 + b^2*c*d^2*e + b*c^2*d*e^2 + c^2*d*e^2*f + c*d^2*e*f^2) +
 18 * (a^2*c^2*e*f + a^2*c*d*f^2 + a*b*d^2*f^2) +
 18 * x^2 * (a^2*c^2 + a^2*d^2 + a^2*e^2 + a^2*f^2 + b^2*d^2 + b^2*e^2 + b^2*f^2 + c^2*e^2 + c^2*f^2 + d^2*f^2) +
 18 * (a^2*b*d^2*f + a^2*b*d*f^2 + a^2*c^2*d*f + a^2*c*d^2*f + a^2*c*e^2*f + a^2*c*e*f^2 + a*b^2*d^2*f + a*b^2*d*f^2 + a*c^2*d*f^2 + a*c^2*e^2*f + a*c^2*e*f^2 + a*c*d^2*f^2) +
 18 * (a^2*b*d^2*e + a^2*b*d*e^2 + a^2*b*e^2*f + a^2*b*e*f^2 + a*b^2*d^2*e + a*b^2*d*e^2 + a*b^2*e^2*f + a*b^2*e*f^2 + b^2*c*e^2*f + b^2*c*e*f^2 + b*c^2*e^2*f + b*c^2*e*f^2) +
 2 * x * (a^3*b*d + a^3*b*e + a^3*b*f + a*b^3*d + a*b^3*e + a*b^3*f + a*c^3*d + a*c*d^3 + a*d^3*e + a*d*e^3 + a*e^3*f + a*e*f^3 + b^3*c*e + b^3*c*f + b*c^3*e + b*c^3*f + b*d^3*e + b*d*e^3 + b*e^3*f + b*e*f^3 + c^3*d*f + c*d^3*f + c*e^3*f + c*e*f^3) +
 24 * x^2 * (a*b^2*c + b*c^2*d + c*d^2*e + d*e^2*f) +
 24 * x * (a^2*c^2*e + a^2*c^2*f + a^2*c*e^2 + a^2*c*f^2 + a^2*d^2*f + a^2*d*f^2 + a*c^2*e^2 + a*c^2*f^2 + a*d^2*f^2 + b^2*d^2*f + b^2*d*f^2 + b*d^2*f^2) +
 24 * x * (a^2*b*d^2 + a^2*b*e^2 + a^2*b*f^2 + a^2*c^2*d + a^2*c*d^2 + a^2*d^2*e + a^2*d*e^2 + a^2*e^2*f + a^2*e*f^2 + a*b^2*d^2 + a*b^2*e^2 + a*b^2*f^2 + b^2*c*e^2 + b^2*c*f^2 + b^2*d^2*e + b^2*d*e^2 + b^2*e^2*f + b^2*e*f^2 + b*c^2*e^2 + b*c^2*f^2 + c^2*d*f^2 + c^2*e^2*f + c^2*e*f^2 + c*d^2*f^2) +
 24 * x * (a^2*b*c^2 + b^2*c*d^2 + c^2*d*e^2 + d^2*e*f^2) +
 30 * x^2 * (a^2*b*d + a^2*b*e + a^2*b*f + a*b^2*d + a*b^2*e + a*b^2*f + a*c^2*d + a*c*d^2 + a*d^2*e + a*d*e^2 + a*e^2*f + a*e*f^2 + b^2*c*e + b^2*c*f + b*c^2*e + b*c^2*f + b*d^2*e + b*d*e^2 + b*e^2*f + b*e*f^2 + c^2*d*f + c*d^2*f + c*e^2*f + c*e*f^2) +
 30 * x^2 * (a^2*b*c + a*b*c^2 + b^2*c*d + b*c*d^2 + c^2*d*e + c*d*e^2 + d^2*e*f + d*e*f^2) +
 31 * (a*b*c^2*d*e + b*c*d^2*e*f) +
 32 * (a*b^2*c*e*f + a*b*d*e^2*f) +
 32 * (a*b^2*c*d*f + a*b*c^2*d*f + a*c*d^2*e*f + a*c*d*e^2*f) +
 32 * (a*b^2*c*d*e + a*b*c*d^2*e + b*c^2*d*e*f + b*c*d*e^2*f) +
 35 * (a^2*b*c*e*f + a*b*c^2*e*f + a*b*d^2*e*f + a*b*d*e*f^2) +
 35 * (a^2*b*c*d*e + a*b*c*d*e^2 + b^2*c*d*e*f + b*c*d*e*f^2) +
 36 * x^3 * (a*b*c + b*c*d + c*d*e + d*e*f) +
 36 * x^2 * (a^2*c*e + a^2*c*f + a^2*d*f + a*c^2*e + a*c^2*f + a*c*e^2 + a*c*f^2 + a*d^2*f + a*d*f^2 + b^2*d*f + b*d^2*f + b*d*f^2) +
 36 * x^2 * (a^2*c*d + a^2*d*e + a^2*e*f + a*b*d^2 + a*b*e^2 + a*b*f^2 + b^2*d*e + b^2*e*f + b*c*e^2 + b*c*f^2 + c^2*e*f + c*d*f^2) +
 36 * (a^2*b*d*e*f + a*b^2*d*e*f + a*b*c*e^2*f + a*b*c*e*f^2) +
 36 * (a^2*b*c*d*f + a*b*c*d^2*f + a*c^2*d*e*f + a*c*d*e*f^2) +
 38 * x^3 * (a*b*d + a*b*e + a*b*f + a*c*d + a*d*e + a*e*f + b*c*e + b*c*f + b*d*e + b*e*f + c*d*f + c*e*f) +
 39 * (a^2*c*d*e*f + a*b*c*d*f^2) +
 4 * x^5 * (a + b + c + d + e + f) +
 4 * x^2 * (a^3*c + a^3*d + a^3*e + a^3*f + a*c^3 + a*d^3 + a*e^3 + a*f^3 + b^3*d + b^3*e + b^3*f + b*d^3 + b*e^3 + b*f^3 + c^3*e + c^3*f + c*e^3 + c*f^3 + d^3*f + d*f^3) +
 4 * (a^3*c^2*e + a^3*c^2*f + a^3*c*e^2 + a^3*c*f^2 + a^3*d^2*f + a^3*d*f^2 + a^2*c^3*e + a^2*c^3*f + a^2*c*e^3 + a^2*c*f^3 + a^2*d^3*f + a^2*d*f^3 + a*c^3*e^2 + a*c^3*f^2 + a*c^2*e^3 + a*c^2*f^3 + a*d^3*f^2 + a*d^2*f^3 + b^3*d^2*f + b^3*d*f^2 + b^2*d^3*f + b^2*d*f^3 + b*d^3*f^2 + b*d^2*f^3) +
 4 * (a^3*c^3 + a^3*d^3 + a^3*e^3 + a^3*f^3 + b^3*d^3 + b^3*e^3 + b^3*f^3 + c^3*e^3 + c^3*f^3 + d^3*f^3) +
 4 * (a^3*b*d*f + a*b^3*d*f + a*c^3*d*f + a*c*d^3*f + a*c*e^3*f + a*c*e*f^3) +
 4 * (a^3*b*d^2 + a^3*b*e^2 + a^3*b*f^2 + a^2*c^3*d + a^2*c*d^3 + a^2*d^3*e + a^2*d*e^3 + a^2*e^3*f + a^2*e*f^3 + a*b^3*d^2 + a*b^3*e^2 + a*b^3*f^2 + b^3*c*e^2 + b^3*c*f^2 + b^2*d^3*e + b^2*d*e^3 + b^2*e^3*f + b^2*e*f^3 + b*c^3*e^2 + b*c^3*f^2 + c^3*d*f^2 + c^2*e^3*f + c^2*e*f^3 + c*d^3*f^2) +
 4 * (a^3*b*c*e + a^3*b*c*f + a*b*c^3*e + a*b*c^3*f + a*c^3*d*e + a*c*d*e^3 + a*d^3*e*f + a*d*e*f^3 + b^3*c*d*f + b*c*d^3*f + b*d^3*e*f + b*d*e*f^3) +
 4 * x * (a^3*b*c + a*b*c^3 + b^3*c*d + b*c*d^3 + c^3*d*e + c*d*e^3 + d^3*e*f + d*e*f^3) +
 40 * x^3 * (a*c*e + a*c*f + a*d*f + b*d*f) +
 40 * x * (a*b^2*c*e + a*b^2*c*f + a*c*d^2*e + a*d*e^2*f + b*c^2*d*f + b*d*e^2*f) +
 40 * x * (a*b^2*c*d + a*b*c^2*d + b*c^2*d*e + b*c*d^2*e + c*d^2*e*f + c*d*e^2*f) +
 46 * x * (a^2*b*c*e + a^2*b*c*f + a*b*c^2*e + a*b*c^2*f + a*c^2*d*e + a*c*d*e^2 + a*d^2*e*f + a*d*e*f^2 + b^2*c*d*f + b*c*d^2*f + b*d^2*e*f + b*d*e*f^2) +
 46 * x * (a^2*b*c*d + a*b*c*d^2 + b^2*c*d*e + b*c*d*e^2 + c^2*d*e*f + c*d*e*f^2) +
 48 * x * (a^2*b*d*f + a*b^2*d*f + a*c^2*d*f + a*c*d^2*f + a*c*e^2*f + a*c*e*f^2) +
 48 * x * (a^2*b*d*e + a^2*b*e*f + a*b^2*d*e + a*b^2*e*f + a*b*d^2*e + a*b*d*e^2 + a*b*e^2*f + a*b*e*f^2 + b^2*c*e*f + b*c^2*e*f + b*c*e^2*f + b*c*e*f^2) +
 5 * x^4 * (a^2 + b^2 + c^2 + d^2 + e^2 + f^2) +
 5 * (a^3*b*d*e + a^3*b*e*f + a*b^3*d*e + a*b^3*e*f + a*b*d^3*e + a*b*d*e^3 + a*b*e^3*f + a*b*e*f^3 + b^3*c*e*f + b*c^3*e*f + b*c*e^3*f + b*c*e*f^3) +
 5 * (a^3*b*c*d + a*b*c*d^3 + b^3*c*d*e + b*c*d*e^3 + c^3*d*e*f + c*d*e*f^3) +
 52 * x * (a^2*c*d*e + a^2*d*e*f + a*b*c*e^2 + a*b*c*f^2 + b^2*d*e*f + b*c*d*f^2) +
 54 * x * (a^2*c*d*f + a^2*c*e*f + a*b*d^2*f + a*b*d*f^2 + a*c^2*e*f + a*c*d*f^2) +
 6 * (a^2*c^2*e^2 + a^2*c^2*f^2 + a^2*d^2*f^2 + b^2*d^2*f^2) +
 6 * (a^2*b^2*d^2 + a^2*b^2*e^2 + a^2*b^2*f^2 + a^2*c^2*d^2 + a^2*d^2*e^2 + a^2*e^2*f^2 + b^2*c^2*e^2 + b^2*c^2*f^2 + b^2*d^2*e^2 + b^2*e^2*f^2 + c^2*d^2*f^2 + c^2*e^2*f^2) +
 6 * (a^2*b^2*c^2 + b^2*c^2*d^2 + c^2*d^2*e^2 + d^2*e^2*f^2) +
 6 * x^2 * (a^2*b^2 + b^2*c^2 + c^2*d^2 + d^2*e^2 + e^2*f^2) +
 6 * (a^3*c^2*d + a^3*c*d^2 + a^3*d^2*e + a^3*d*e^2 + a^3*e^2*f + a^3*e*f^2 + a^2*b*d^3 + a^2*b*e^3 + a^2*b*f^3 + a*b^2*d^3 + a*b^2*e^3 + a*b^2*f^3 + b^3*d^2*e + b^3*d*e^2 + b^3*e^2*f + b^3*e*f^2 + b^2*c*e^3 + b^2*c*f^3 + b*c^2*e^3 + b*c^2*f^3 + c^3*e^2*f + c^3*e*f^2 + c^2*d*f^3 + c*d^2*f^3) +
 6 * (a^3*b*c^2 + a^2*b*c^3 + b^3*c*d^2 + b^2*c*d^3 + c^3*d*e^2 + c^2*d*e^3 + d^3*e*f^2 + d^2*e*f^3) +
 77 * x^2 * (a*b*c*d + b*c*d*e + c*d*e*f) +
 8 * x * (a^3*c*e + a^3*c*f + a^3*d*f + a*c^3*e + a*c^3*f + a*c*e^3 + a*c*f^3 + a*d^3*f + a*d*f^3 + b^3*d*f + b*d^3*f + b*d*f^3) +
 8 * (a^3*c*d*f + a^3*c*e*f + a*b*d^3*f + a*b*d*f^3 + a*c^3*e*f + a*c*d*f^3) +
 8 * (a^3*c*d*e + a^3*d*e*f + a*b*c*e^3 + a*b*c*f^3 + b^3*d*e*f + b*c*d*f^3) +
 8 * x * (a^3*c^2 + a^3*d^2 + a^3*e^2 + a^3*f^2 + a^2*c^3 + a^2*d^3 + a^2*e^3 + a^2*f^3 + b^3*d^2 + b^3*e^2 + b^3*f^2 + b^2*d^3 + b^2*e^3 + b^2*f^3 + c^3*e^2 + c^3*f^2 + c^2*e^3 + c^2*f^3 + d^3*f^2 + d^2*f^3) +
 80 * x^2 * (a*b*c*e + a*b*c*f + a*c*d*e + a*d*e*f + b*c*d*f + b*d*e*f) +
 81 * x^2 * (a*b*d*e + a*b*e*f + b*c*e*f) +
 84 * x^2 * (a*b*d*f + a*c*d*f + a*c*e*f) +
 83 * (a*b*c*d*e*f))
///
}}}

{{{id=160|
poly61d0 = poly31(x=poly3(a=e,b=f)) * poly4(x=poly3(a=e,b=f)) * poly21(x=poly4,a=e,b=f)
poly61e0 = poly5(x=x+f) * poly5(x=x-f) * poly41(x=x+f)
poly61f0 = poly6 * poly51
///
}}}

{{{id=161|
def dump(poly, file):
    o = open(file,'w')
    o.write(str([[poly.monomial_coefficient(m), list(m.degrees())] for m in poly.monomials()]))

dump(poly61d0, '/tmp/poly61d0.json')
dump(poly61e0, '/tmp/poly61e0.json')
dump(poly61f0, '/tmp/poly61f0.json')
///
}}}

{{{id=162|
poly61(x,1,1,1,1,1,1)
///
x^6 + 24*x^5 + 235*x^4 + 1200*x^3 + 3366*x^2 + 4912*x + 2911
}}}

{{{id=163|
poly31(t,1,1,1,0,0,0).real_roots()
///
[-2.41421356237309, -1.00000000000000, 0.414213562373095]
}}}

{{{id=165|
[n(2 * cos(i * pi / 4) - 1) for i in range(1,4)]
///
[0.414213562373095, -1.00000000000000, -2.41421356237309]
}}}

{{{id=166|
poly51(t,1,1,1,1,1,0).real_roots()
///
[-4.73205080756888,
 -4.00000000000000,
 -3.00000000000000,
 -2.00000000000000,
 -1.26794919243112]
}}}

{{{id=167|
prod([t - n(2 * cos(i * pi / 7) - 4) for i in range(1,7)])
///
t^6 + 24.0000000000000*t^5 + 235.000000000000*t^4 + 1200.00000000000*t^3 + 3366.00000000000*t^2 + 4912.00000000000*t + 2911.00000000000
}}}

{{{id=168|
2911 - 2828
///
83
}}}

{{{id=169|
poly61(t,1,1.05,1.1,1.2,0.93,0.777).real_roots()
///
[-5.84910879776683,
 -5.33934651317899,
 -4.53912356269152,
 -3.71948218678709,
 -2.83693338597103,
 -1.94400555360454]
}}}
