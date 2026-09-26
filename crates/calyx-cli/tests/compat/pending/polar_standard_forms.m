// Handbook H30E8.
K := GF(5);
J := StandardAlternatingForm(4,K);
J;

// Handbook H30E9 and H30E10.
K<z> := GF(7,2);
Q := StandardQuadraticForm(4,49 : Minus);
Q;
P<x> := PolynomialRing(K);
a := Q[2,2] * Q[3,3];
IsIrreducible(x^2+x+a);
QR := StandardQuadraticForm(4,49 : Minus, Variant := "Revised");
QR;

// The remaining constructors, including the field involution.
StandardPseudoAlternatingForm(3, GF(2));
H, sigma := StandardHermitianForm(3, 3);
H;
sigma(GF(9).1) eq GF(9).1^3;
StandardQuadraticForm(3, GF(5) : Minus);
StandardSymmetricForm(4, GF(5) : Minus);
