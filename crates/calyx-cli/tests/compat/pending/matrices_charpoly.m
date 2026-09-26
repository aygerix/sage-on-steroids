// Minimal and characteristic polynomials, their factorizations,
// eigenvalues and eigenspaces. Eigenvalues come in a set that Magma prints
// in an order of its own, so the sets of more than one pair are checked by
// their size and members.

A := Matrix(Integers(), 3, 3, [1,2,3, 4,5,6, 7,8,10]);
D := DiagonalMatrix(Rationals(), [1,1,2]);
J := Matrix(Integers(), 4, 4, [2,1,0,0, 0,2,1,0, 0,0,2,0, 0,0,0,2]);
C := CompanionMatrix(PolynomialRing(Integers())![3, -1, 0, 2, 1]);
Q := Matrix(Rationals(), 3, 3, [1/2, 1/3, 0, 0, 1/2, 0, 1, 2, 3/4]);
M := Matrix(GF(5), 5, 5, [1,1,0,0,0, 0,1,0,0,0, 0,0,1,0,0, 0,0,0,3,1, 0,0,0,0,3]);
F<w> := GF(4);
G<a> := GF(9);
N := Matrix(G, 3, 3, [a, 1, 0, 0, a, 0, 0, 0, a^3]);
H := Matrix(Integers(7), 3, 3, [1,2,3, 4,5,6, 0,1,1]);
X := RMatrixSpace(Integers(), 2, 2) ! [1,2,3,4];
N23 := Matrix(Integers(), 2, 3, [1,2,3,4,5,6]);
Z6 := Matrix(Integers(6), 2, 2, [1,2,3,4]);
R10 := Matrix(RealField(10), 2, 2, [1.5,2,3,4]);

// Characteristic and minimal polynomials over the integers and the
// rationals
CharacteristicPolynomial(A);
MinimalPolynomial(A);
MinimalPolynomial(IdentityMatrix(Integers(), 3));
CharacteristicPolynomial(IdentityMatrix(Rationals(), 3));
MinimalPolynomial(J);
CharacteristicPolynomial(J);
MinimalPolynomial(ScalarMatrix(Rationals(), 4, 7/3));
MinimalPolynomial(Matrix(Integers(), 2, 2, [0, -1, 1, 0]));
CharacteristicPolynomial(Matrix(Integers(), 1, 1, [-5]));
MinimalPolynomial(Matrix(Integers(), 3, 3, [0,1,0, 0,0,1, 0,0,0]));
MinimalPolynomial(ZeroMatrix(Integers(), 3, 3));
MinimalPolynomial(C);
MinimalPolynomial(DiagonalJoin(C, C));
CharacteristicPolynomial(DiagonalJoin(C, C));
MinimalPolynomial(ZeroMatrix(Rationals(), 0, 0));
CharacteristicPolynomial(ZeroMatrix(Rationals(), 0, 0));
CharacteristicPolynomial(X);
MinimalPolynomial(X);

// Both at once
MCPolynomials(D);
MinimalAndCharacteristicPolynomials(D);
m, c := MCPolynomials(Q); m; c;
MCPolynomials(DiagonalJoin(C, C));

// Over finite fields and residue rings
CharacteristicPolynomial(Matrix(GF(7), 2, 2, [1,2,3,4]));
MinimalPolynomial(Matrix(GF(7), 2, 2, [1,2,3,4]));
MCPolynomials(M);
CharacteristicPolynomial(Matrix(F, 2, 2, [w, 1, 0, 1]));
MinimalPolynomial(Matrix(F, 2, 2, [w, 0, 0, w]));
MCPolynomials(N);
MinimalPolynomial(ZeroMatrix(GF(3), 2, 2));
MCPolynomials(H);
CharacteristicPolynomial(Z6);

// Over the reals, the characteristic polynomial only
CharacteristicPolynomial(R10);

// Factorizations
FactoredCharacteristicPolynomial(A);
FactoredMinimalPolynomial(DiagonalMatrix(Integers(), [1,1,2]));
FactoredMCPolynomials(DiagonalMatrix(Integers(), [1,1,2]));
FactoredMinimalAndCharacteristicPolynomials(DiagonalMatrix(Integers(), [-1,1,2]));
FactoredCharacteristicPolynomial(Matrix(Integers(), 2, 2, [2, 4, 6, 8]));
FactoredCharacteristicPolynomial(Matrix(Rationals(), 2, 2, [1/2, 4, 6, 8]));
FactoredMinimalPolynomial(J);
FactoredCharacteristicPolynomial(J);
FactoredMCPolynomials(DiagonalJoin(C, C));
FactoredMCPolynomials(Q);
FactoredMCPolynomials(M);
FactoredMCPolynomials(N);
FactoredMinimalPolynomial(H);
FactoredCharacteristicPolynomial(DiagonalMatrix(GF(7), [5,3,0,6,3]));
FactoredMinimalPolynomial(DiagonalMatrix(GF(7), [5,3,0,6,3]));
FactoredCharacteristicPolynomial(Matrix(Integers(7), 2, 2, [1,2,3,4]));
FactoredCharacteristicPolynomial(ZeroMatrix(Rationals(), 0, 0));

// Eigenvalues: pairs <e, k> of an eigenvalue in the coefficient ring and
// its multiplicity
Eigenvalues(Matrix(Rationals(), 2, 2, [0,-1,1,0]));
Eigenvalues(Matrix(Integers(), 2, 2, [2,1,0,2]));
Eigenvalues(ZeroMatrix(Integers(), 3, 3));
Eigenvalues(ZeroMatrix(Rationals(), 0, 0));
Eigenvalues(Matrix(GF(7), 2, 2, [1,2,3,4]));
Eigenvalues(Matrix(Integers(7), 2, 2, [1,2,3,4]));
Eigenvalues(Vector([2]));
Eigenvalues(Matrix(Rationals(), 1, 1, [2]));
Eigenvalues(A);
Eigenvalues(X);
E := Eigenvalues(D); #E, <1, 2> in E, <2, 1> in E;
E := Eigenvalues(Matrix(Rationals(), 2, 2, [0,1,1,0])); #E, <1, 1> in E, <-1, 1> in E;
E := Eigenvalues(DiagonalMatrix(Integers(), [5,-3,0,7])); #E, <-3, 1> in E, <0, 1> in E, <7, 2> in E;
E := Eigenvalues(Matrix(GF(7), 2, 2, [2,0,0,3])); #E, <2, 1> in E, <3, 1> in E;
E := Eigenvalues(Matrix(F, 2, 2, [w, 1, 0, 1])); #E, <w, 1> in E, <1, 1> in E;
E := Eigenvalues(J); #E, <2, 4> in E;
E := Eigenvalues(M); #E, <1, 3> in E, <3, 2> in E;
E := Eigenvalues(DiagonalMatrix(Rationals(), [1/2, -1/3])); #E, <1/2, 1> in E, <-1/3, 1> in E;
Parent(Eigenvalues(A));
Parent(Eigenvalues(Matrix(GF(7), 2, 2, [1,2,3,4])));
Parent(Eigenvalues(Matrix(Rationals(), 1, 1, [2])));
Type(Eigenvalues(A));
S := Eigenvalues(Matrix(Integers(), 2, 2, [2,1,0,2])); Universe(S); Parent(Rep(S));

// Eigenspaces: the kernels of A - e
Eigenspace(D, 1);
Eigenspace(D, 3);
Eigenspace(DiagonalMatrix(Integers(), [1,1,2]), 1);
Eigenspace(J, 2);
Eigenspace(Q, 1/2);
Eigenspace(Q, 3/4);
Eigenspace(M, 1);
Eigenspace(M, 3);
Eigenspace(M, 2);
Eigenspace(N, a);
Eigenspace(N, a^3);
Eigenspace(Matrix(Rationals(), 2, 2, [1,2,3,4]), 1/2);
Eigenspace(Matrix(GF(7), 2, 2, [1,2,3,4]), 5);
Eigenspace(Matrix(F, 2, 2, [1,0,0,1]), 1);
Eigenspace(Z6, 1);
Eigenspace(R10, 1);
Eigenspace(Vector([2]), 2);
Eigenspace(X, 1);
Eigenspace(A, GF(7)!1);
Eigenspace(Matrix(Integers(), 3, 3, [0,1,0, 0,0,1, 0,0,0]), 0);

// Errors
CharacteristicPolynomial(N23);
MinimalPolynomial(N23);
MCPolynomials(N23);
FactoredCharacteristicPolynomial(N23);
FactoredMinimalPolynomial(N23);
FactoredMCPolynomials(N23);
Eigenvalues(N23);
Eigenspace(N23, 1);
Eigenvalues(Vector([2, 3]));
Eigenspace(Vector([2, 3]), 1);
MinimalPolynomial(Vector([2]));
CharacteristicPolynomial(Vector([2]));
MCPolynomials(Vector([2]));
FactoredCharacteristicPolynomial(Vector([2]));
FactoredMinimalPolynomial(Vector([2]));
FactoredMCPolynomials(Vector([2]));
MinimalPolynomial(Z6);
MCPolynomials(Z6);
FactoredCharacteristicPolynomial(Z6);
FactoredMinimalPolynomial(Z6);
Eigenvalues(Z6);
MinimalPolynomial(R10);
MCPolynomials(R10);
FactoredCharacteristicPolynomial(R10);
Eigenspace(A, 1/2);
Eigenspace(Matrix(GF(7), 2, 2, [1,2,3,4]), GF(49).1);
Eigenspace(A, "x");

// The algorithms of CharacteristicPolynomial, which need rings of their
// own, and the other parameters
CharacteristicPolynomial(A : Al := "Modular");
CharacteristicPolynomial(A : Al := "Interpolation");
CharacteristicPolynomial(A : Al := "Trace");
CharacteristicPolynomial(Matrix(Rationals(), 2, 2, [1,2,3,4]) : Al := "Hessenberg");
CharacteristicPolynomial(Matrix(Rationals(), 2, 2, [1,2,3,4]) : Al := "Trace");
CharacteristicPolynomial(Matrix(GF(7), 2, 2, [1,2,3,4]) : Al := "Hessenberg");
CharacteristicPolynomial(Matrix(GF(7), 2, 2, [1,2,3,4]) : Al := "Trace");
CharacteristicPolynomial(Matrix(GF(7), 2, 2, [1,2,3,4]) : Al := "Modular");
CharacteristicPolynomial(Matrix(Integers(7), 2, 2, [1,2,3,4]) : Al := "Hessenberg");
CharacteristicPolynomial(Z6 : Al := "Trace");
CharacteristicPolynomial(R10 : Al := "Hessenberg");
CharacteristicPolynomial(R10 : Al := "Modular");
CharacteristicPolynomial(A : Al := "Hessenberg");
CharacteristicPolynomial(Z6 : Al := "Hessenberg");
CharacteristicPolynomial(Matrix(GF(7), 2, 2, [1,2,3,4]) : Al := "Interpolation");
CharacteristicPolynomial(Z6 : Al := "Interpolation");
FactoredCharacteristicPolynomial(A : Al := "Hessenberg");
CharacteristicPolynomial(A : Proof := false);
MinimalPolynomial(A : Proof := false);
MinimalPolynomial(A : Al := "Default");
MCPolynomials(A : Proof := false);
FactoredMCPolynomials(A : Proof := false);
FactoredMinimalPolynomial(A : Proof := false);
FactoredCharacteristicPolynomial(A : Al := "Trace", Proof := false);

// Bad parameters
CharacteristicPolynomial(A : Al := "Foo");
CharacteristicPolynomial(A : Al := "Berkowitz");
CharacteristicPolynomial(A : Al := 1);
CharacteristicPolynomial(A : Proof := 1);
CharacteristicPolynomial(N23 : Al := "Foo");
MinimalPolynomial(A : Al := "Modular");
MinimalPolynomial(A : Al := "Foo");
MinimalPolynomial(A : Al := 1);
MinimalPolynomial(A : Proof := 1);
MCPolynomials(A : Al := "Modular");
MCPolynomials(A : Proof := 1);
MinimalAndCharacteristicPolynomials(A : Foo := 1);
FactoredCharacteristicPolynomial(A : Al := "Foo");
FactoredCharacteristicPolynomial(A : Proof := 1);
FactoredMinimalPolynomial(A : Al := "Foo");
FactoredMinimalPolynomial(A : Proof := 1);
FactoredMCPolynomials(A : Al := "Foo");
FactoredMinimalAndCharacteristicPolynomials(A : Foo := 1);
Eigenvalues(A : Foo := 1);
Eigenspace(A, 1 : Foo := 1);

// The polynomials are in the global polynomial ring over the coefficient
// ring, and print with the names given to it
Parent(CharacteristicPolynomial(A));
Parent(MinimalPolynomial(ZeroMatrix(GF(3), 2, 2)));
P<x> := PolynomialRing(Rationals());
CharacteristicPolynomial(Matrix(Rationals(), 2, 2, [1,2,3,4]));
MCPolynomials(Q);
FactoredMCPolynomials(Q);
T<t> := PolynomialRing(GF(5));
MinimalPolynomial(M);
FactoredCharacteristicPolynomial(M);
Parent(CharacteristicPolynomial(M));
Zy<y> := PolynomialRing(Integers());
CharacteristicPolynomial(A);
Parent(CharacteristicPolynomial(A));
CharacteristicPolynomial(Matrix(Zy, 2, 2, [y, 1, 0, y]));
MinimalPolynomial(Matrix(Zy, 2, 2, [y, 1, 0, y]));
FactoredCharacteristicPolynomial(Matrix(Zy, 2, 2, [y, 1, 0, y]));
Eigenvalues(Matrix(Zy, 2, 2, [1,2,3,4]));
