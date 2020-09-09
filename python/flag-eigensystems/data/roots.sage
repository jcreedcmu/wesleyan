
{{{id=69|
R.<x,a,b,c,d,e> = ZZ['x,a,b,c,d,e']; R
///
Multivariate Polynomial Ring in x, a, b, c, d, e over Integer Ring
}}}

{{{id=68|
poly32 = (
     x^5 +
     x^4 * (a + b + c + d) +
 2 * x^3 * (-a^2 - b^2 - c^2 - d^2 + a*b + b*c + c*d ) +
-2 * x^2 * (a^3 + b^3 + c^3 + d^3 + a^2*c + a*c^2 + b^2*d + b*d^2 - a*b*d - a*c*d + a^2*d + a*d^2)
+    x * (
		 (a^4 + b^4 + c^4 + d^4)
		 - 2 * (a^3*b
				+ a*b^3
				+ b^3*c
				+ b*c^3
				+ c^3*d
				+ c*d^3)
		 + 3 * (a^2*b^2 + b^2*c^2 + c^2*d^2)
		 - 2 * (a^2*c^2 + b^2*d^2 + a^2*d^2)
		 + 2 * (0
	  + a * b^2 * c
	  - a^2 * b * c
	  - a * b * c^2
	  + b * c^2 * d
	  - b * c * d^2
	  - b^2 * c * d
	  + a^2 * c * d
	  + a * b * d^2
	  + a * b * c * d
	  ))
+
(
(a^5 + b^5 + c^5 + d^5)
- a^4*b - a*b^4
+ a^4*c + a*c^4
- b^4*c - b*c^4
+ b^4*d + b*d^4
- c^4*d - c*d^4
+ a^4*d + a*d^4

+ a^3*b^2 + a^2*b^3
+ b^3*c^2 + b^2*c^3
+ c^3*d^2 + c^2*d^3

- 2*a^3*c^2 - 2*a^2*c^3
- 2*b^3*d^2 - 2*b^2*d^3
- 2*a^3*d^2 - 2*a^2*d^3

- a^2 * b^2 * c
- b * c^2 * d^2
- a * b^2 * c^2
- b^2 * c^2 * d
+ 2 * a^2 * b * c^2
+ 2 * b^2 * c * d^2
+ 2 * a * b^3 * c
+ 2 * b * c^3 * d
- 2 * a * b^3 * d
- 2 * a * c^3 * d
- 2 * a^3 * b * d
- 2 * a * c * d^3
+ 3 * a * c^2 * d^2
+ 3 * a^2 * b^2 * d
+ 2 * a * b * d^3
+ 2 * a^3 * c * d
- 2 * a * b * c * d^2
- 2 * a^2 * b * c * d
+ 2 * a * b^2 * c * d
+ 2 * a * b * c^2 * d
)
)
///
}}}

{{{id=58|
p = poly32.polynomial(x).subs(a=0.1,b=0.22,c=0.35,d=0.9)
///
}}}

{{{id=62|
p.coefficients()
///
[0.599419647700000,
 0.222577610000000,
 -2.11946600000000,
 -1.15380000000000,
 1.57000000000000,
 1.00000000000000]
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
t^5 + 1.57000000000000*t^4 - 1.15380000000000*t^3 - 2.11946600000000*t^2 + 0.222577610000000*t + 0.599419647700000
}}}

{{{id=67|
ps.real_roots()
///
[-1.35692018012991,
 -1.05966845119743,
 -0.718990371846877,
 0.601262043754177,
 0.964316959420036]
}}}

{{{id=70|

///
}}}