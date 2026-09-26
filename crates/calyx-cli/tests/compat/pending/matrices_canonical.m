// Canonical forms: Smith forms and elementary divisors, saturations,
// Hessenberg forms, the rational, primary rational and Jordan forms with
// their invariant factors, similarity, and the Frobenius form of an
// alternating matrix. calyx finds other transformations than Magma does
// (save for SmithForm over a field), so they are checked by their
// relations to the forms, and a saturation by its Hermite form.

// Mat_CanonicalForms (H27E9), without printing T
K := GF(5);
A := Matrix(K, 5,
    [ 0, 2, 4, 2, 0,
      2, 2, 2, 3, 3,
      3, 4, 4, 1, 3,
      0, 0, 0, 0, 1,
      0, 0, 0, 1, 0 ]);
A;
PrimaryInvariantFactors(A);
JordanForm(A);
R, T, F := RationalForm(A);
R;
T*A*T^-1 eq R;
F;
P<x> := PolynomialRing(K);
PM := MatrixAlgebra(P, 5);
Ax := PM ! x - PM ! A;
Ax;
S, U, V := SmithForm(Ax);
S;
U*Ax*V eq S;
ElementaryDivisors(Ax);

// Mat_Forms1 (H27E10), with the Smith form alone
K<w> := GF(8);
A := Matrix(K, 4, 3, [1,w,w^5, 0,w^3,w^4, w,1,w^6, w^3,1,w^4]);
A;
EchelonForm(A);
A := Matrix(4, 5,
    [ 2,-4,12,7,0,
      3,-3,5,-1,4,
      2,-1,-4,-5,-12,
      0,3,6,-2,0]);
A;
Rank(A);
HermiteForm(A);
S := SmithForm(A);
S;
ElementaryDivisors(A);

// Smith forms over the integers: P*A*Q = S with P and Q unimodular
Z := Integers();
for A in [* Matrix(Z, 4, 5, [2,-4,12,7,0, 3,-3,5,-1,4, 2,-1,-4,-5,-12, 0,3,6,-2,0]),
            Matrix(Z, 3, 3, [2,4,4, -6,6,12, 10,-4,-16]),
            Matrix(Z, 2, 3, [2,4,6, 0,3,9]),
            Matrix(Z, 3, 2, [6,0, 0,10, 15,0]),
            DiagonalMatrix(Z, [12, 18, 0, -8]),
            Matrix(Z, 1, 3, [0, -4, 6]),
            Matrix(Z, 4, 4, [1,2,3,4, 2,5,1,3, 0,1,4,2, 3,1,1,5]) * DiagonalMatrix(Z, [1,2,6,12])
              * Matrix(Z, 4, 4, [2,1,0,1, 1,3,1,0, 0,1,2,1, 1,0,1,4]),
            10^25 * Matrix(Z, 3, 3, [1,2,3, 4,5,6, 7,8,10]),
            DiagonalMatrix(Z, [NextPrime(10^30), NextPrime(10^30)^2, 1]),
            Matrix(Z, 3, 4, [1,2,3,4, 2,4,6,8, 1,0,1,0]) *] do
  S, U, V := SmithForm(A);
  S, U*A*V eq S, Abs(Determinant(U)), Abs(Determinant(V)), ElementaryDivisors(A);
end for;
S, U, V := SmithForm(ZeroMatrix(Z, 2, 3)); S; U; V;
S, U, V := SmithForm(Matrix(Z, 0, 3, [])); S; U; V;
ElementaryDivisors(ZeroMatrix(Z, 2, 3));
ElementaryDivisors(Matrix(Z, 0, 2, []));
S, U, V := SmithForm(Vector(Z, [2, 4, 6])); S; U; Vector(Z, [2, 4, 6])*V eq S;
ElementaryDivisors(Vector(Z, [2, 4, 6]));
S := SmithForm(Matrix(Z, 2, 3, [2,4,6, 0,3,9])); Parent(S);
S, U, V := SmithForm(Matrix(Z, 2, 3, [2,4,6, 0,3,9])); Parent(U); Parent(V);
S, U, V := SmithForm(MatrixAlgebra(Z, 2) ! [2,4,6,8]); Parent(S); Parent(U);
Universe(ElementaryDivisors(Matrix(Z, 2, 2, [2,4,6,8])));

// Over a field: 1s as many as the rank, with Magma's transformations
SmithForm(Matrix(GF(7), 2, 3, [1,2,3,2,4,6]));
SmithForm(Matrix(Rationals(), 2, 2, [1,2,2,4]));
SmithForm(Matrix(Rationals(), 3, 3, [1/2,1,0, 0,0,1, 1,2,5]));
SmithForm(Matrix(Integers(7), 2, 2, [1,2,3,4]));
SmithForm(Matrix(GF(9), 2, 2, [1,2,2,1]));
SmithForm(Matrix(RealField(), 2, 2, [1,2,3,4]));
SmithForm(Matrix(Rationals(), 0, 3, []));
ElementaryDivisors(Matrix(Rationals(), 2, 2, [1,2,2,4]));
ElementaryDivisors(Matrix(GF(7), 2, 2, [1,2,3,4]));
ElementaryDivisors(Vector(GF(5), [0, 2]));
ElementaryDivisors(Matrix(RealField(), 2, 2, [1,2,3,4]));
Universe(ElementaryDivisors(Matrix(Rationals(), 2, 2, [1,2,3,4])));

// Over the integers modulo a composite: the divisors of n
for A in [* Matrix(Integers(12), 2, 2, [4,0,0,6]), Matrix(Integers(12), 2, 2, [8,0,0,9]),
            Matrix(Integers(6), 2, 2, [2,0,0,3]), Matrix(Integers(36), 2, 3, [6,4,0, 3,9,12]) *] do
  S, U, V := SmithForm(A);
  S, U*A*V eq S, IsUnit(U), IsUnit(V), ElementaryDivisors(A);
end for;

// Over polynomial rings over a field
P<x> := PolynomialRing(GF(5));
M := Matrix(P, 2, 2, [x, 1, 0, x]);
S, U, V := SmithForm(M); S; U*M*V eq S;
ElementaryDivisors(M);
Q<y> := PolynomialRing(Rationals());
M := Matrix(Q, 3, 3, [y^2 - 1, 0, y + 1, 0, y - 1, 0, y^2 + y, 1, y^3]);
S, U, V := SmithForm(M); S; U*M*V eq S;
ElementaryDivisors(M);
ElementaryDivisors(Matrix(Q, 2, 2, [1,2,3,4]));

// Errors
SmithForm(Matrix(PolynomialRing(Integers()), 2, 2, [1,2,3,4]));
ElementaryDivisors(Matrix(PolynomialRing(Integers()), 2, 2, [1,2,3,4]));

// Saturations, compared by their Hermite forms
for A in [* Matrix(Z, 2, 3, [2,4,6, 0,3,9]), Matrix(Z, 3, 3, [2,4,6, 1,2,3, 0,0,5]),
            Matrix(Z, 3, 2, [2,4, 3,6, 5,10]), Matrix(Z, 2, 3, [0,0,0, 4,6,8]),
            Matrix(Z, 2, 2, [1,2,3,4]), Matrix(Z, 2, 3, [6,10,15, 0,0,0]),
            Matrix(Z, 3, 4, [2,0,4,6, 0,3,0,9, 2,3,4,15]),
            DiagonalMatrix(Z, [4, 6, 1]) * Matrix(Z, 3, 5, [1,2,0,1,3, 0,1,1,2,1, 1,0,2,1,1]),
            Matrix(Z, 2, 3, [NextPrime(10^40), 0, NextPrime(10^40), 0, NextPrime(10^40), NextPrime(10^40)]) *] do
  S := Saturation(A);
  HermiteForm(S), Nrows(S) eq Rank(A);
end for;
HermiteForm(Saturation(Matrix(Rationals(), 2, 2, [1,2,3,4])));
HermiteForm(Saturation(Matrix(Rationals(), 1, 2, [1/2, 1])));
Saturation(ZeroMatrix(Z, 2, 3));
Saturation(Matrix(Z, 0, 3, []));
HermiteForm(Saturation(Vector(Z, [2, 4])));
Parent(Saturation(Matrix(Z, 2, 3, [2,4,6, 0,3,9])));
Parent(Saturation(Matrix(Rationals(), 2, 2, [1,2,3,4])));
Saturation(Matrix(GF(5), 2, 2, [1,2,3,4]));

// Hessenberg forms
HessenbergForm(Matrix(Rationals(), 3, 3, [1,2,3, 4,5,6, 7,8,10]));
HessenbergForm(Matrix(GF(7), 4, 4, [1,2,3,4, 0,1,5,6, 2,0,1,3, 4,4,0,1]));
HessenbergForm(Matrix(Integers(7), 3, 3, [1,2,3,4,5,6,0,1,1]));
HessenbergForm(Matrix(Rationals(), 4, 4, [1,0,0,2, 3,4,0,5, 1,1,1,1, 0,2,0,3]));
HessenbergForm(Matrix(Rationals(), 3, 3, [1,0,0, 2,3,0, 4,5,6]));
HessenbergForm(Matrix(Rationals(), 3, 3, [1,0,5, 2,3,0, 4,5,6]));
HessenbergForm(Vector(Rationals(), [3]));
HessenbergForm(ZeroMatrix(Rationals(), 0, 0));
Parent(HessenbergForm(KMatrixSpace(Rationals(), 2, 2) ! [1,2,3,4]));
HessenbergForm(Matrix(Integers(), 2, 2, [1,2,3,4]));
HessenbergForm(Matrix(Rationals(), 2, 3, [1,2,3,4,5,6]));
HessenbergForm(Matrix(Integers(), 2, 3, [1,2,3,4,5,6]));

// Invariant factors and primary invariant factors
Q := Rationals();
J := DiagonalJoin(<Matrix(Q, 1, 1, [2]), Matrix(Q, 2, 2, [2,1,0,2]), Matrix(Q, 1, 1, [5]),
    Matrix(Q, 3, 3, [2,1,0, 0,2,1, 0,0,2])>);
C := Matrix(Q, 2, 2, [0,-1,1,0]);
B := BlockMatrix(2, 2, [C, IdentityMatrix(Q, 2), ZeroMatrix(Q, 2, 2), C]);
PrimaryInvariantFactors(J);
InvariantFactors(J);
PrimaryInvariantFactors(B);
InvariantFactors(B);
PrimaryInvariantFactors(DiagonalJoin(<C, C, B>));
InvariantFactors(DiagonalJoin(<C, C, B>));
InvariantFactors(DiagonalMatrix(Q, [1,2,3]));
InvariantFactors(ScalarMatrix(Q, 3, 1/2));
PrimaryInvariantFactors(ScalarMatrix(Q, 3, 1/2));
PrimaryInvariantFactors(Matrix(Integers(7), 2, 2, [1,2,3,4]));
PrimaryInvariantFactors(ZeroMatrix(GF(3), 2, 2));
InvariantFactors(Vector(Q, [3]));
InvariantFactors(ZeroMatrix(Q, 0, 0));
PrimaryInvariantFactors(ZeroMatrix(Q, 0, 0));
F<a> := GF(9);
G := Matrix(F, 4, 4, [a,1,0,0, 0,a,0,0, 0,0,a,0, 0,0,0,a^2]);
PrimaryInvariantFactors(G);
InvariantFactors(G);
Universe(InvariantFactors(J));
Universe(PrimaryInvariantFactors(J));

// The forms, their transformations and lists
for A in [* J, B, DiagonalJoin(<C, C, B>), DiagonalMatrix(Q, [1,2,3]), ScalarMatrix(Q, 3, 1/2),
            Matrix(Q, 3, 3, [0,1,0, 0,0,1, 0,0,0]), Matrix(Q, 3, 3, [2,0,0, 1,2,0, 0,0,3]),
            Matrix(Q, 3, 3, [1,2,3, 4,5,6, 7,8,10]), G *] do
  RationalForm(A);
  F, T, L := RationalForm(A); F eq RationalForm(A), T*A*T^-1 eq F, L eq InvariantFactors(A);
  JordanForm(A);
  F, T, L := JordanForm(A); T*A*T^-1 eq F, L eq PrimaryInvariantFactors(A);
  F, T, L := PrimaryRationalForm(A); F; T*A*T^-1 eq F, L eq PrimaryInvariantFactors(A);
end for;
A := Matrix(GF(2), 6, 6, [0,1,0,0,0,0, 0,0,1,0,0,0, 1,1,0,0,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1, 0,0,0,1,1,0]);
RationalForm(A);
JordanForm(A);
F, T, L := PrimaryRationalForm(A); F; L; T*A*T^-1 eq F;
RationalForm(Vector(Q, [1]));
F, T, L := RationalForm(ZeroMatrix(Q, 0, 0)); F; T; L;
F, T, L := JordanForm(ZeroMatrix(GF(3), 2, 2)); F; L; T*ZeroMatrix(GF(3), 2, 2)*T^-1 eq F;
K := KMatrixSpace(Q, 2, 2); A := K ! [1,2,3,4];
F, T, L := JordanForm(A); Parent(F); Parent(T); Universe(L);
F, T, L := RationalForm(A); Parent(F); Parent(T); Universe(L);

// Errors: the ring is checked first
RationalForm(Matrix(RealField(), 2, 2, [1,2,3,4]));
RationalForm(Matrix(RealField(), 2, 3, [1,2,3,4,5,6]));
RationalForm(Matrix(Integers(), 2, 2, [1,2,3,4]));
RationalForm(Matrix(Q, 2, 3, [1,2,3,4,5,6]));
JordanForm(Matrix(Integers(), 2, 2, [1,2,3,4]));
JordanForm(Matrix(GF(5), 2, 3, [1,2,3,4,0,1]));
JordanForm(Vector(GF(5), [1, 2]));
PrimaryRationalForm(Matrix(Q, 2, 3, [1,2,3,4,5,6]));
InvariantFactors(Matrix(Integers(6), 2, 2, [1,2,3,4]));
InvariantFactors(Matrix(Integers(), 2, 3, [1,2,3,4,5,6]));
PrimaryInvariantFactors(Matrix(Integers(), 2, 2, [1,2,3,4]));

// Similarity: T*A*T^-1 = B
A := Matrix(Q, 2, 2, [1,2,3,4]);
IsSimilar(A, Matrix(Q, 2, 2, [0,1,2,5]));
IsSimilar(A, Matrix(Q, 2, 2, [1,0,0,4]));
b, T := IsSimilar(A, Matrix(Q, 2, 2, [0,1,2,5])); b, T*A*T^-1 eq Matrix(Q, 2, 2, [0,1,2,5]), Parent(T);
for A in [* J, B, G, Matrix(Q, 3, 3, [0,1,0, 0,0,1, 0,0,0]) *] do
  n := Nrows(A);
  U := Matrix(BaseRing(A), n, n, [i gt j select 0 else i eq j select 1 else (i + 2*j) mod 3 - 1 : j in [1..n], i in [1..n]]);
  b, T := IsSimilar(A, U*A*U^-1); b, T*A*T^-1 eq U*A*U^-1;
end for;
IsSimilar(J, Transpose(J));
IsSimilar(B, DiagonalJoin(C, C));
IsSimilar(A, Transpose(A));
IsSimilar(Matrix(Q, 2, 2, [1,2,3,4]), Matrix(GF(5), 2, 2, [1,2,3,4]));
b, T := IsSimilar(Matrix(Q, 2, 2, [1,2,3,4]), Matrix(GF(5), 2, 2, [1,2,3,4])); b; Parent(T);
IsSimilar(Matrix(GF(5), 2, 2, [1,2,3,4]), Matrix(Q, 2, 2, [1,2,3,4]));
IsSimilar(Matrix(Q, 2, 2, [1,2,3,4]), Matrix(Integers(), 2, 2, [1,2,3,4]));
IsSimilar(Vector(Q, [3]), Vector(Q, [3]));
IsSimilar(ZeroMatrix(Q, 0, 0), ZeroMatrix(Q, 0, 0));
IsSimilar(Matrix(Integers(), 2, 2, [1,2,3,4]), Matrix(Integers(), 2, 2, [1,2,3,4]));
IsSimilar(Matrix(RealField(), 2, 2, [1,2,3,4]), Matrix(RealField(), 2, 2, [1,2,3,4]));
IsSimilar(Matrix(Q, 2, 2, [1,2,3,4]), Matrix(Q, 3, 3, [1,2,3,4,5,6,7,8,9]));
IsSimilar(Matrix(Q, 2, 3, [1,2,3,4,5,6]), Matrix(Q, 2, 3, [1,2,3,4,5,6]));
IsSimilar(Matrix(Q, 2, 2, [1,2,3,4]), Matrix(Q, 2, 3, [1,2,3,4,5,6]));
IsSimilar(Matrix(Q, 2, 2, [1/5,2,3,4]), Matrix(GF(5), 2, 2, [1,2,3,4]));
IsSimilar(Matrix(GF(5), 2, 2, [1,2,3,4]), Matrix(GF(7), 2, 2, [1,2,3,4]));

// The Frobenius form of an alternating matrix: B*A*B^t = F
for l in [[0,3,-3,0], [0,-3,3,0], [0,2,4,6, -2,0,8,10, -4,-8,0,12, -6,-10,-12,0],
          [0,4,6,0, -4,0,0,6, -6,0,0,4, 0,-6,-4,0], [0,1,0,0, -1,0,0,0, 0,0,0,5, 0,0,-5,0],
          [0,-3,2,-4, 3,0,4,-6, -2,-4,0,-5, 4,6,5,0], [0,5,5,0, -5,0,5,-6, -5,-5,0,5, 0,6,-5,0],
          [0,-4,0,-4, 4,0,-4,-4, 0,4,0,5, 4,4,-5,0],
          [0,3,-5,2,-2,-1, -3,0,-1,1,5,-5, 5,1,0,5,-4,-3, -2,-1,-5,0,0,-4, 2,-5,4,0,0,-4, 1,5,3,4,4,0],
          [0,-3,-3,3,1,-3,3,2, 3,0,3,-1,0,1,3,1, 3,-3,0,-3,-3,2,0,1, -3,1,3,0,3,1,-3,-3,
           -1,0,3,-3,0,2,0,0, 3,-1,-2,-1,-2,0,3,2, -3,-3,0,3,0,-3,0,2, -2,-1,-1,3,0,-2,-2,0]] do
  n := Isqrt(#l); A := Matrix(Z, n, n, l);
  F, B := FrobeniusFormAlternating(A);
  F, B*A*Transpose(B) eq F, Abs(Determinant(B));
end for;
F := FrobeniusFormAlternating(Matrix(Z, 2, 2, [0,3,-3,0])); F;
F, B := FrobeniusFormAlternating(Matrix(Z, 2, 2, [0,3,-3,0])); Parent(F); Parent(B);
FrobeniusFormAlternating(Matrix(Z, 2, 2, [0,1,1,0]));
FrobeniusFormAlternating(Matrix(Z, 2, 2, [1,1,-1,0]));
FrobeniusFormAlternating(Matrix(Z, 2, 2, [0,0,0,0]));
FrobeniusFormAlternating(Matrix(Z, 4, 4, [0,1,0,0, -1,0,0,0, 0,0,0,0, 0,0,0,0]));
FrobeniusFormAlternating(Matrix(Z, 3, 3, [0,1,2,-1,0,3,-2,-3,0]));
FrobeniusFormAlternating(Matrix(Z, 3, 3, [1,2,3,4,5,6,7,8,9]));
FrobeniusFormAlternating(Matrix(Rationals(), 2, 2, [0,1,-1,0]));
FrobeniusFormAlternating(Matrix(Rationals(), 0, 0, []));
FrobeniusFormAlternating(Matrix(Z, 0, 0, []));
FrobeniusFormAlternating(Matrix(Z, 2, 3, [0,1,2,-1,0,3]));
FrobeniusFormAlternating(Matrix(GF(5), 2, 2, [0,1,-1,0]));
FrobeniusFormAlternating(Matrix(Integers(6), 2, 2, [0,1,-1,0]));
FrobeniusFormAlternating(Matrix(RealField(), 2, 2, [0,1,-1,0]));

// A prime field above 2^64.
K := GF(NextPrime(10^30));
M := Matrix(K, 3, 3, [1,2,3, 4,5,6, 7,8,10]);
RationalForm(M); InvariantFactors(M); PrimaryInvariantFactors(M);
M^-1 eq Adjoint(M) / Determinant(M); MinimalPolynomial(M);
N := Matrix(K, 3, 3, [2,1,0, 0,2,0, 0,0,3]);
J, T := JordanForm(N); J, T*N*T^-1 eq J;
F, T, f := PrimaryRationalForm(N); F, T*N*T^-1 eq F, f;
IsSimilar(N, Transpose(N));
