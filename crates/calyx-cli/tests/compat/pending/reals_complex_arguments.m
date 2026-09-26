// Complex numbers that are real, where the real functions take them:
// MantissaExponent, Floor, Ceiling and BesselFunction at the precision of
// the complex field, and two-argument Log, Gamma, Arctan and Arctan2 in the
// default real field. Other complex numbers are rejected.
C<i> := ComplexField(20); D := ComplexField(50); R := RealField(20); S := RealField(50);
x := C!2.75; y := D!2.75;
MantissaExponent(x); MantissaExponent(y); MantissaExponent(C!0);
a, b := MantissaExponent(C!Pi(R)); c, d := MantissaExponent(Pi(R)); a eq c, b eq d;
Floor(x), Ceiling(x), Floor(-x), Ceiling(-x), Floor(y), Ceiling(y);
Floor(C!(-2.5)), Ceiling(C!(-0.5)), Floor(C!0);
Floor(ComplexField(40)!10^30), Ceiling(D!(-10^40));
Type(Floor(x)), Type(Ceiling(x));
a := BesselFunction(2, x); a, Parent(a);
a := BesselFunction(2, y); a, Parent(a);
BesselFunction(2, D!Pi(S)) eq BesselFunction(2, Pi(S)); BesselFunction(3, C!(-2));

// A complex argument puts both arguments in the default real field.
for u in [* C!2, D!2, R!2, S!2, 2, 1/2 *] do
  for v in [* C!8, D!8 *] do
    a := Log(u, v); b := Log(v, u); c := Gamma(u, v); d := Gamma(v, u); e := Arctan2(u, v); f := Arctan2(v, u);
    a, Parent(a) eq RealField(), b, Precision(b), c, Precision(c), d, Precision(d), e, Precision(e), f, Precision(f);
  end for;
end for;
x := Pi(R); y := Exp(R!1); T := RealField(30);
Log(C!x, C!y) eq Log(T!x, T!y), Gamma(C!x, C!y) eq Gamma(T!x, T!y), Arctan2(C!x, C!y) eq Arctan2(T!x, T!y), Arctan(C!x, C!y) eq Arctan2(T!x, T!y);
x := Pi(S); y := Exp(S!1);
Log(D!x, D!y) eq Log(T!x, T!y), Gamma(D!x, D!y) eq Gamma(T!x, T!y), Arctan2(D!x, D!y) eq Arctan2(T!x, T!y);
Gamma(D!2, D!3 : Complementary), Gamma(D!2, D!3 : Gamma := S!1), Gamma(C!2, 3 : Gamma := R!1);
SetDefaultRealField(RealField(40));
a := Log(D!2, D!8); a, Parent(a);
a := Gamma(D!2, D!3); a, Parent(a);
a := Arctan2(D!1, D!2); a, Parent(a);
a := Arctan(D!1, D!2); a, Parent(a);
SetDefaultRealField(RealField(30));

// With no complex argument, Arctan and Arctan2 use the field of the first
// real argument. Values with fewer-precision later arguments are omitted:
// 2.22 returns the right parent but loses digits there.
a := Arctan2(R!1, S!2); a, Parent(a);
a := Arctan2(1/2, R!1); a, Parent(a);
a := Arctan2(R!1, 1/2); a, Parent(a);
Parent(Arctan2(S!1, R!2)), Parent(Arctan2(R!1, S!2));
Parent(Arctan2(1, S!2)), Parent(Arctan2(1, 2)), Parent(Arctan2(1/2, 2));
Parent(Arctan(S!1, R!2)), Parent(Arctan(R!1, S!2));
Parent(Log(1/2, R!8)), Parent(Log(R!2, 3)), Parent(Log(R!2, S!8)), Parent(Gamma(1/2, R!3)), Parent(Gamma(R!2, S!3));

// Errors: those of the real functions, and bad argument types for other
// complex numbers.
Log(C!2, C!(-8));
Log(C!(-2), C!8);
Log(C!1, C!8);
Gamma(C!0, C!1);
Gamma(D!2, D!3 : Gamma := D!1);
BesselFunction(-1, C!2);
z := C!2.5 + i;
MantissaExponent(z);
Floor(z);
Ceiling(z);
BesselFunction(2, z);
Log(C!2, z);
Log(z, 2);
Gamma(C!2, z);
Gamma(z, R!2);
Arctan2(C!1, z);
Arctan2(z, 1);
Arctan(z, C!1);
Truncate(C!2.5);
Sign(C!2.5);
