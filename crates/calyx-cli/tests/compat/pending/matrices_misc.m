// Miscellaneous operations on matrices: the Frobenius image of a matrix
// over a finite field, x -> x^(p^e) on each entry.

F<w> := GF(9);
A := Matrix(F, 2, 3, [w, w^2, 1, 0, w^5, 2]);
FrobeniusImage(A, 1); FrobeniusImage(A, 2); FrobeniusImage(A, 0); FrobeniusImage(A, 3);
FrobeniusImage(A, -1);
B := FrobeniusImage(A, 1); Parent(B); Type(B);
C := Matrix(F, 2, 2, [w, 1, 0, w^3]); FrobeniusImage(C, 1); Parent(FrobeniusImage(C, 1));
FrobeniusImage(Vector(F, [w, w^2]), 1);
FrobeniusImage(Matrix(GF(7), 2, 2, [1,2,3,4]), 5);
FrobeniusImage(Matrix(Integers(), 2, 2, [1,2,3,4]), 1);
FrobeniusImage(Matrix(Rationals(), 2, 2, [1,2,3,4]), 1);
K<t> := GF(2, 10); M := Matrix(K, 2, 2, [t, t^3, t^100, 1]); FrobeniusImage(M, 3); FrobeniusImage(M, 13);
FrobeniusImage(Matrix(F, 0, 3, []), 1);
FrobeniusImage(Matrix(Integers(9), 2, 2, [1,2,3,4]), 1);
FrobeniusImage(RMatrixSpace(F, 2, 2) ! [w,0,0,1], 1); Parent(FrobeniusImage(RMatrixSpace(F, 2, 2) ! [w,0,0,1], 1));
FrobeniusImage(MatrixAlgebra(F, 2) ! [w,0,0,1], 1); Parent(FrobeniusImage(MatrixAlgebra(F, 2) ! [w,0,0,1], 1));
FrobeniusImage(A, 10^30); FrobeniusImage(A, -10^30 - 1);
L := GF(NextPrime(10^30), 2); FrobeniusImage(Matrix(L, 1, 2, [L.1, L.1^2]), 1);
FrobeniusImage(Matrix(GF(9), 1, 1, [w]), w);
K<t> := GF(3, 5); P<x> := PolynomialRing(K);
A := Matrix(K, 4, 4, [t^(i*j + i) : i, j in [1..4]]); B := Matrix(K, 4, 4, [t^(i + 2*j) + i : i, j in [1..4]]);
[FrobeniusImage(A*B, e) eq FrobeniusImage(A, e)*FrobeniusImage(B, e) : e in [0..5]];
[Determinant(FrobeniusImage(A, e)) eq Frobenius(Determinant(A), e) : e in [0..5]];
FrobeniusImage(FrobeniusImage(A, 2), 3) eq A;
L := GF(7, 3); M := Matrix(L, 2, 2, [L.1, L.1^2, L.1^3, 1]); FrobeniusImage(M, 1) eq Matrix(L, 2, 2, [x^7 : x in Eltseq(M)]);
FrobeniusImage(Matrix(GF(2^20), 1, 1, [GF(2^20).1]), 19)^2;
