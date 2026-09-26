// A copy of compat/pending/rationals_linear.m, so that calyx's output, checked against
// Magma 2.22, is kept until #24 records the output of 2.29.
// Q as an algebra and as a vector space over itself, and the rational
// reconstruction of a matrix (Rational Field chapter, "Structure
// Operations" and "Rational Reconstruction"). The handbook describes the
// maps of Algebra(Q, Q) and VectorSpace(Q, Q) as maps to Q; Magma 2.22
// gives them from Q, and so does calyx until 2.29 is checked.
Q := Rationals();

// Algebra(Q, Q): an associative algebra of dimension 1
A, f := Algebra(Q, Q);
A; f; Type(A); Type(f); Domain(f); Codomain(f);
Dimension(A); BaseRing(A); BaseField(A); IsCommutative(A); IsAssociative(A);
x := A.1; x; One(A); Zero(A); Basis(A);
A.2;
A.0;
a := A![3/4]; a; Type(a); A!2; A!(1/3); A![Integers()!5];
A![1, 2];
A![];
x*x + x; 2*x; x*2/3; x + 1; 1 + x; -x; x - x; x^3; x^0; x^-1; (2*x)^-1; x eq 1; x eq A!1;
x/0;
(0*x)^-1;
1 in A; x in A; Parent(x) eq A;

// the map from Q, and coercion to Q
f(1/2); Type(f(1/2)); f(3); f(x); f(3*x); f(x/2); f(a);
x @@ f; Type(x @@ f); (2*x) @@ f; (5/7) @@ f; Type((5/7) @@ f);
Q!x; Q!(x/3); Integers()!(4*x);

// another algebra is another structure
B := Algebra(Q, Q);
A eq B;
B.1 eq x;
B.1 + x;
A.1 * B.1;
Algebra(Q, GF(5));
Algebra(Q, Integers());
Algebra(Q, RealField());

// VectorSpace(Q, Q): the full vector space of degree 1
V, g := VectorSpace(Q, Q);
V; g; Type(V); Type(g); Domain(g); Codomain(g); Dimension(V); Basis(V);
V eq VectorSpace(Q, 1);
g(1/2); Type(g(1/2)); g(3);
v := Basis(V)[1]; v @@ g; Type(v @@ g); (V![2/3]) @@ g;
g(v);
g(V![2/3]);
(5/7) @@ g;
VectorSpace(Q, GF(5));

// RationalReconstruction of a matrix over a prime field: every entry, or
// false
F := GF(101);
M := Matrix(F, 2, 2, [1, 51, 34, 3]); M;
RationalReconstruction(M);
b, R := RationalReconstruction(M); b; R; Type(R); Parent(R);
N := Matrix(F, 2, 3, [0, 1, 100, 50, 51, 7]);
b, R := RationalReconstruction(N); b; R;
N := Matrix(F, 1, 2, [1, 30]);
b, R := RationalReconstruction(N); b; assigned R;
RationalReconstruction(Matrix(F, 0, 0, []));
RationalReconstruction(ZeroMatrix(F, 2, 2));
RationalReconstruction(Matrix(GF(2), 1, 1, [1]));
RationalReconstruction(Vector(F, [1, 51]));
RationalReconstruction(Matrix(GF(9), 1, 1, [1]));
RationalReconstruction(Matrix(Integers(101), 1, 1, [51]));
RationalReconstruction(Matrix(Integers(), 1, 1, [51]));
RationalReconstruction(Matrix(F, 2, 2, [1, 51, 34, 3]) : Denominator := 5);
