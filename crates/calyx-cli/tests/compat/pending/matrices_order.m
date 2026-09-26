// Orders of invertible matrices: over finite fields, Z, Q, Z/nZ and other
// rings, factored and projective, with the value true that Magma returns
// after them (printed by a call statement only when Proof is false).

// Finite fields
A := Matrix(GF(5), 3, 3, [1,1,0, 0,1,1, 0,0,2]);
Type(A);
Order(A); FactoredOrder(A); ProjectiveOrder(A); FactoredProjectiveOrder(A); HasFiniteOrder(A);
n, s := ProjectiveOrder(A); n, s, Parent(s);
f, s := FactoredProjectiveOrder(A); f, s;
Order(A : Proof := false); Order(A : Proof := true);
o, b := Order(A); o, b;
x := Order(A : Proof := false); x;
[Order(A : Proof := false)];
FactoredOrder(A : Proof := false);
ProjectiveOrder(A : Proof := false);
FactoredProjectiveOrder(A : Proof := false);
o, s, b := ProjectiveOrder(A); o, s, b;
o, b := FactoredOrder(A); o, b;
F<w> := GF(9);
B := Matrix(F, 2, 2, [w, 1, 0, w^2]); Order(B); FactoredOrder(B); ProjectiveOrder(B);
Order(ScalarMatrix(F, 3, w));
ProjectiveOrder(ScalarMatrix(F, 3, w));
FactoredOrder(IdentityMatrix(F, 3));
FactoredProjectiveOrder(IdentityMatrix(F, 3));
Order(IdentityMatrix(GF(2), 0)); FactoredOrder(Matrix(GF(2), 0, 0, []));
HasFiniteOrder(Matrix(GF(5), 0, 0, []));
Order(Matrix(GF(7), 1, 1, [3])); ProjectiveOrder(Matrix(GF(7), 1, 1, [3]));
Order(Matrix(GF(7), 3, 3, [3,1,0, 0,3,1, 0,0,3])); ProjectiveOrder(Matrix(GF(7), 3, 3, [3,1,0, 0,3,1, 0,0,3]));
F<w> := GF(4); FactoredProjectiveOrder(Matrix(F, 2, 2, [w,1,0,w]));
Order(Matrix(GF(2,3), 2, 2, [1,0,0,1])); ProjectiveOrder(Matrix(GF(2,3), 2, 2, [1,0,0,1]));
FactoredProjectiveOrder(Matrix(GF(5), 2, 2, [2,0,0,2]));
Order(Matrix(GF(2), 3, 3, [0,0,1, 1,0,1, 0,1,0]));
Order(Matrix(GF(2), 9, 9, [0,0,0,0,0,0,0,0,1, 1,0,0,0,0,0,0,0,0, 0,1,0,0,0,0,0,0,0, 0,0,1,0,0,0,0,0,0,
    0,0,0,1,0,0,0,0,0, 0,0,0,0,1,0,0,0,0, 0,0,0,0,0,1,0,0,0, 0,0,0,0,0,0,1,0,0, 0,0,0,0,0,0,0,1,0]));
Order(MatrixAlgebra(GF(3), 2) ! [1,1,0,1]);
Order(RMatrixSpace(GF(5), 2, 2) ! [1,1,0,1]);
HasFiniteOrder(RMatrixSpace(GF(5), 2, 2) ! [1,1,0,1]);

// Large fields, with the Cunningham tables
K<t> := GF(2, 100); M := Matrix(K, 3, 3, [t, 1, 0, 0, t^5, 1, 1, 0, t^2 + 1]); FactoredOrder(M);
p := NextPrime(10^30); M := Matrix(GF(p), 2, 2, [1, 2, 3, 5]);
FactoredOrder(M); ProjectiveOrder(M);
Order(M : Proof := false); FactoredOrder(M : Proof := false);
K<z> := GF(2^20); M := Matrix(K, 2, 2, [z, 1, 1, 0]); Order(M); FactoredProjectiveOrder(M);
q := NextPrime(10^60); while not IsPrime(2*q+1) do q := NextPrime(q); end while; p := 2*q+1;
M := Matrix(GF(p), 1, 1, [3]);
Order(M : Proof := false);
o, b := Order(M); o eq p-1 or o eq q, b;
o, b := FactoredOrder(M : Proof := false); #o, b;
o, s, b := ProjectiveOrder(M : Proof := false); o, s, b;
for q in [2, 3, 4, 7, 25, 101, 3^7] do
  K := GF(q);
  for n in [5, 12, 20] do
    M := Matrix(K, n, n, [K.1^((i^3 + 7*j^2 + i*j) mod 11) * ((i + j) mod 3) + (i eq j select 1 else 0) : i, j in [1..n]]);
    if Determinant(M) ne 0 then
      f := FactoredOrder(M); o := Order(M);
      <q, n, f, M^o eq 1, &and[M^(o div r[1]) ne 1 : r in f]>;
      m, s := ProjectiveOrder(M);
      <m, M^m eq ScalarMatrix(K, n, s), o mod m>;
    end if;
  end for;
end for;

// Integers and rationals
C := Matrix(Integers(), 2, 2, [0, -1, 1, 0]); Order(C); HasFiniteOrder(C); FactoredOrder(C);
D := Matrix(Integers(), 2, 2, [1, 1, 0, 1]); HasFiniteOrder(D);
Order(D);
E := Matrix(Rationals(), 2, 2, [0, 1/2, 2, 0]); Order(E); HasFiniteOrder(E);
Order(Matrix(Rationals(), 2, 2, [2, 0, 0, 1/2]));
Order(-IdentityMatrix(Integers(), 3));
Order(Matrix(Integers(), 3, 3, [0,1,0, 0,0,1, 1,0,0]));
Order(Matrix(Integers(), 0, 0, [])); HasFiniteOrder(Matrix(Integers(), 0, 0, []));
FactoredOrder(Matrix(Integers(), 0, 0, []));
Order(Matrix(Integers(), 4, 4, [0,0,0,-1, 1,0,0,0, 0,1,0,0, 0,0,1,0]));
Order(Matrix(Integers(), 4, 4, [0,0,0,-1, 1,0,0,-1, 0,1,0,-1, 0,0,1,-1]));
Order(DiagonalJoin(Matrix(Integers(), 2, 2, [0,-1,1,-1]), Matrix(Integers(), 2, 2, [0,-1,1,0])));
Order(Matrix(Integers(), 2, 2, [-1, 1, 0, -1]));
HasFiniteOrder(Matrix(Integers(), 2, 2, [-1, 1, 0, -1]));
Order(Matrix(Integers(), 2, 2, [0,1,-1,1]) : Proof := true);
Order(Matrix(Integers(), 2, 2, [0,-1,1,0]) : Proof := false);
FactoredOrder(Matrix(Integers(), 2, 2, [0,-1,1,0]) : Proof := false);
o, b := Order(Matrix(Integers(), 2, 2, [0,1,1,0])); o, b;
Order(Matrix(Integers(), 1, 1, [1])); Order(Matrix(Integers(), 1, 1, [-1])); FactoredOrder(Matrix(Integers(), 1, 1, [1]));
Order(Matrix(Integers(), 3, 3, [1,0,0, 0,1,0, 0,0,1]));
Order(RMatrixSpace(Integers(), 2, 2) ! [0,1,1,0]);
Order(Matrix(Rationals(), 3, 3, [0,0,1/2, 1,0,0, 0,2,0]));
Order(Matrix(Rationals(), 2, 2, [1/2,0,0,2]));
HasFiniteOrder(Matrix(Rationals(), 2, 2, [1/2,0,0,2]));
Order(Matrix(Rationals(), 2, 2, [0,1,-1,0]) : Proof := false);
o, b := Order(Matrix(Rationals(), 2, 2, [0,1,1,0])); o, b;
FactoredOrder(Matrix(Rationals(), 2, 2, [0, 1, 1, 0]));
P<x> := PolynomialRing(Integers());
cyclo := [x^4 + x^3 + x^2 + x + 1, x^6 + x^3 + 1, x^4 - x^2 + 1, x^8 + 1, x^6 + x^5 + x^4 + x^3 + x^2 + x + 1];
Z := DiagonalJoin(<CompanionMatrix(f) : f in cyclo>);
T := Matrix(Integers(), 28, 28, [i eq j select 1 else (j eq i + 1 select (-1)^i else 0) : i, j in [1..28]]);
Z := T^-1 * Z * T;
Order(Z); FactoredOrder(Z); HasFiniteOrder(Z);
HasFiniteOrder(Z + 1);

// Z/nZ
Order(Matrix(Integers(7), 2, 2, [1,1,0,1]));
Order(Matrix(Integers(8), 2, 2, [1,1,0,1]));
Order(Matrix(Integers(12), 2, 2, [0,1,1,1]));
HasFiniteOrder(Matrix(Integers(12), 2, 2, [0,1,1,1]));
FactoredOrder(Matrix(Integers(12), 2, 2, [0,1,1,1]));
o, b := FactoredOrder(Matrix(Integers(12), 2, 2, [0,1,1,1])); o, b;
Order(Matrix(Integers(12), 2, 2, [0,1,1,1]) : Proof := false);
Order(Matrix(Integers(9), 2, 2, [1,3,0,1])); Order(Matrix(Integers(9), 2, 2, [4,0,0,1])); Order(Matrix(Integers(16), 2, 2, [3,0,0,1]));
Order(Matrix(Integers(2^5), 2, 2, [3,1,0,1])); FactoredOrder(Matrix(Integers(2^5), 2, 2, [3,1,0,1]));
Order(Matrix(Integers(6), 2, 2, [5,0,0,1]));
HasFiniteOrder(Matrix(Integers(6), 0, 0, []));
Order(Matrix(Integers(4), 1, 1, [3]));
Order(Matrix(Integers(3^4*5^3), 3, 3, [2,1,0, 1,2,1, 1,0,2]));
FactoredOrder(Matrix(Integers(10^4), 2, 2, [2,1,1,1]));
FactoredOrder(Matrix(Integers(10^6), 2, 2, [2,1,1,1]));
FactoredOrder(Matrix(Integers(10^6), 2, 2, [1,1,0,1]));
FactoredOrder(Matrix(Integers(1009 * 3^5), 2, 2, [1,2,3,5]));

// Other rings, by multiplying
Order(Matrix(RealField(), 2, 2, [0, 1, 1, 0]));
Order(Matrix(RealField(), 2, 2, [0,1,1,0]) : Proof := false);
FactoredOrder(Matrix(RealField(), 2, 2, [0,1,1,0]));
Order(Matrix(ComplexField(), 2, 2, [0,-1,1,0]));
P<x> := PolynomialRing(GF(3));
Order(Matrix(P, 2, 2, [0, 1, 1, 0]));
Order(Matrix(P, 2, 2, [1, x, 0, 1]));

// Errors
Order(Matrix(GF(5), 2, 2, [1,2,2,4]));
HasFiniteOrder(Matrix(GF(5), 2, 2, [1,2,2,4]));
ProjectiveOrder(Matrix(GF(5), 2, 2, [1,2,2,4]));
FactoredOrder(Matrix(GF(5), 2, 2, [1,2,2,4]));
Order(Matrix(Integers(), 2, 2, [2, 0, 0, 1]));
HasFiniteOrder(Matrix(Integers(), 2, 2, [2, 0, 0, 1]));
FactoredOrder(Matrix(Integers(), 2, 2, [1,1,0,1]));
Order(Matrix(Integers(), 2, 2, [1,1,1,1]));
Order(Matrix(Rationals(), 2, 2, [1,1,1,1]));
HasFiniteOrder(Matrix(Rationals(), 2, 2, [1,1,1,1]));
Order(Matrix(Integers(12), 2, 2, [2,0,0,1]));
HasFiniteOrder(Matrix(Integers(12), 2, 2, [2,0,0,1]));
Order(Matrix(Integers(4), 1, 1, [2]));
Order(Matrix(Integers(1), 2, 2, [0,1,1,0]));
Order(Matrix(GF(5), 2, 3, [1,2,2,4,1,1]));
HasFiniteOrder(Matrix(GF(5), 2, 3, [1,2,2,4,1,1]));
ProjectiveOrder(Matrix(GF(5), 2, 3, [1,2,2,4,1,1]));
HasFiniteOrder(Matrix(Integers(), 2, 3, [1,2,2,4,1,1]));
ProjectiveOrder(Matrix(Integers(), 2, 2, [0, -1, 1, 0]));
ProjectiveOrder(Matrix(Rationals(), 2, 2, [0, 1, 1, 0]));
ProjectiveOrder(Matrix(Integers(12), 2, 2, [0,1,1,1]));
ProjectiveOrder(Matrix(RealField(), 2, 2, [0,1,1,0]));
HasFiniteOrder(Matrix(RealField(), 2, 2, [0, 1, 1, 0]));
HasFiniteOrder(Matrix(P, 2, 2, [0, 1, 1, 0]));
Order(Matrix(RealField(), 2, 2, [0,0,0,0]));
Order(Matrix(P, 2, 2, [x,0,0,1]));
Order(Vector(GF(5), [1,2]));
Order(A : Proof := 1);
HasFiniteOrder(A : Proof := false);
o, b := HasFiniteOrder(Matrix(Integers(), 2, 2, [0,1,1,0]));
Order(Matrix(GF(5), 2, 2, [1,1,0,1]) : Foo := 1);
