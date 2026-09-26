// Creation of vector spaces and arithmetic with vectors: spaces with an
// inner product matrix, inner products and norms, the basis vectors V.i,
// and the attributes ip_form and Involution of a space over a field.

// ModFld_InnerProduct (H29E6)
Q := RationalField();
F := SymmetricMatrix(Q, [1, 0,2, 0,0,3, 1,2,3,4]);
F;
V := VectorSpace(Q, 4, F);
V;
v := V![1,0,0,0];
Norm(v);
w := V![0,1,0,0];
Norm(w);
InnerProduct(v, w);
z := V![0,0,0,1];
Norm(z);
InnerProduct(v, z);
InnerProduct(w, z);

// FldForms_generalform (H30E1)
K := GF(11);
J := Matrix(K,3,3,[1,2,3, 4,5,6, 7,8,9]);
V := VectorSpace(K,3,J);
InnerProductMatrix(V);

// Spaces with a form
V := VectorSpace(Q, 4, F);
Type(V); Sprint(V, "Magma");
InnerProductMatrix(V); InnerProductMatrix(VectorSpace(Q, 3)); InnerProductMatrix(RSpace(Integers(), 2));
Type(InnerProductMatrix(V)); Parent(InnerProductMatrix(V));
V eq VectorSpace(Q, 4, F);
u := V![1,0,0,0] + VectorSpace(Q, 4)![0,1,0,0]; Parent(u) eq V; InnerProduct(u, u); Norm(u);
KSpace(Q, 2, Matrix(Q, 2, 2, [1,2,3,4]));
RSpace(Integers(), 2, Matrix(Integers(), 2, 2, [2,1,1,2]));
RSpace(Integers(), 3, ZeroMatrix(Integers(), 3, 3));
KSpace(GF(5), 3, ZeroMatrix(GF(5), 3, 3));
VectorSpace(Q, 0, ZeroMatrix(Q, 0, 0));
I := VectorSpace(Q, 2, IdentityMatrix(Q, 2)); I; I eq VectorSpace(Q, 2);
KSpace(Q, 2, Matrix(Q, 2, 2, [1,0,0,1])) eq VectorSpace(Q, 2);
F9<w> := GF(9); U := VectorSpace(F9, 2, Matrix(F9, 2, 2, [0,1,1,0])); U; Parent(U.1);
InnerProduct(U![w,1], U![1,w]);

// Arithmetic keeps the space of the first vector
X := VectorSpace(Q, 2, Matrix(Q, 2, 2, [1,2,3,4])); Y := VectorSpace(Q, 2, Matrix(Q, 2, 2, [5,6,7,8])); P := VectorSpace(Q, 2);
a := X![1,0] + Y![0,1]; a; Parent(a) eq X; b := Y![0,1] + X![1,0]; Parent(b) eq Y;
c := P![1,1] + X![1,0]; Parent(c) eq P; d := X![1,0] + P![1,1]; Parent(d) eq X;
e := 2 * X![1,0]; Parent(e) eq X;
f := X![1,0] * Matrix(Q, 2, 2, [1,1,0,1]); f; Parent(f) eq X;
P!(X![1,2]); Parent(P!(X![1,2])) eq P; X![1,2] eq P![1,2];
InnerProduct(X![1,0], Y![0,1]); InnerProduct(Y![0,1], X![1,0]); InnerProduct(P![1,0], X![0,1]);
X.1 + X.2; Parent(X.1) eq X;

// Inner products and norms without a form
InnerProduct(VectorSpace(F9, 2)![w,1], VectorSpace(F9, 2)![1,w]); Norm(VectorSpace(F9, 2)![w,1]);
R := RSpace(Integers(), 2, Matrix(Integers(), 2, 2, [2,1,1,2])); Norm(R![1,1]); InnerProduct(R![1,0], R![0,1]); R.2;
Z := RSpace(Integers(), 2); Norm(Z![3,4]); InnerProduct(Z![1,2], Z![3,4]);
Norm(RSpace(GF(7), 3)![1,2,3]); Norm(Vector(Integers(6), [1,2,3]));
C := ComplexField(5); VC := VectorSpace(C, 2); i := C.1; InnerProduct(VC![i, 1], VC![i, 1]); Norm(VC![i, 1]);

// Basis vectors
V := VectorSpace(Q, 4, F);
V.1; V.4; VectorSpace(Q, 3).2; RSpace(Integers(), 3).3;

// Attributes
F9<w> := GF(9); sigma := hom<F9 -> F9 | x :-> x^3>; J := Matrix(F9, 2, 2, [0,1,1,0]);
H := VectorSpace(F9, 2, J); H`Involution := sigma; H; assigned H`Involution;
T := VectorSpace(F9, 2, J); T eq H; assigned T`Involution;
assigned VectorSpace(F9, 2)`Involution;
H`ip_form;

// Errors
VectorSpace(Q, 2, Matrix(Integers(), 2, 2, [1,2,2,1]));
VectorSpace(Q, 3, Matrix(Q, 2, 2, [1,0,0,1]));
VectorSpace(Q, 2, Matrix(Q, 2, 3, [1,0,0,1,0,0]));
VectorSpace(Q, 2, Matrix(GF(5), 2, 2, [1,0,0,1]));
VectorSpace(Q, -1, Matrix(Q, 0, 0, []));
VectorSpace(Q, 2, Matrix(Q, 2, 2, [1,2,3,4]) : Foo := 1);
V := VectorSpace(Q, 4, F);
V.0;
V.5;
InnerProduct(VectorSpace(Q, 2)![1,2], VectorSpace(Q, 3)![1,2,3]);
InnerProduct(VectorSpace(Q, 2)![1,2], RSpace(Integers(), 2)![1,2]);
InnerProduct(RSpace(Integers(), 2)![1,2], VectorSpace(Q, 2)![1,2]);
RSpace(Integers(), 2)`Involution;
VectorSpace(Q, 2)`Involution;
KMatrixSpace(Q, 2, 2)`ip_form;
