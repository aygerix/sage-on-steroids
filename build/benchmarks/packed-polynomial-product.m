SetAutoColumns(false);
F<a> := GF(251^10);
P<x> := PolynomialRing(F);
f := P![a^((37*i) mod 1000) + F!(i mod 251) : i in [0..100000]];
g := P![a^((53*i + 1) mod 1000) + F!((3*i + 1) mod 251) : i in [0..100000]];
h := f * g;
print "packed-polynomial-product", Degree(h), Coefficient(h, 100000);
