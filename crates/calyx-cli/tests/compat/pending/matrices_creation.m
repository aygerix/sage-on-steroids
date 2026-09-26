// Creation of matrices (H27E1, H27E2, H27E3): the forms of Matrix, the
// shortcuts, structured matrices and vectors, with their parents.

// H27E1
X := Matrix(IntegerRing(), 2, 2, [1,2, 3,4]);
X;
Parent(X);
X := Matrix(GF(23), 2, 3, [1,-2,3, 4,100,-6]);
X;
Parent(X);
X := Matrix(RationalField(), 5, 10, [<1,2,23>, <3,7,11>, <5,10,-1>]);
X;
Parent(X);
X := Matrix(GF(101), 10, 10, [<2*i-1, 2*j-1, i*j>: i, j in [1..5]]);
X;
Parent(X);

// H27E2
X := Matrix(2, [1,2, 3,4]);
X;
X := Matrix([[1,2], [3,4]]);
X;
X := Matrix(GF(23), 3, [1,-2,3, 4,100,-6]);
X;
Parent(X);
X := Matrix(GF(23), [[1,-2,3], [4,100,-6]]);
X;
X := Matrix([[GF(23)|1,-2,3], [4,100,-6]]);
X;

// H27E3
S := ScalarMatrix(3, -4);
S;
Parent(S);
D := DiagonalMatrix(GF(23), [1, 2, -3]);
D;
Parent(D);
S := SymmetricMatrix([1, 1/2,3, 1,3,4]);
S;
Parent(S);
low := func<n | LowerTriangularMatrix([i: i in [1 .. Binomial(n + 1, 2)]])>;
up := func<n | UpperTriangularMatrix([i: i in [1 .. Binomial(n + 1, 2)]])>;
sym := func<n | SymmetricMatrix([i: i in [1 .. Binomial(n + 1, 2)]])>;
low(3);
up(3);
sym(3);
up(6);

// Types and parents
X := Matrix(IntegerRing(), 2, 2, [1,2, 3,4]);
Y := Matrix(GF(23), 2, 3, [1,-2,3, 4,100,-6]);
Z := Matrix(IntegerRing(), 2, 3, [1,-2,3, 4,100,-6]);
v := Vector([1,2,3]);
w := Vector(GF(23), [1,2,3]);
Type(X), Type(Y), Type(Z), Type(v), Type(w);
ExtendedType(X), ExtendedType(Y), ExtendedType(Z), ExtendedType(v), ExtendedType(w);
Type(Parent(X)), Type(Parent(Y)), Type(Parent(Z)), Type(Parent(v)), Type(Parent(w));
Parent(Z); Parent(v); Parent(w);
ISA(Type(X), Mtrx), ISA(Type(Y), Mtrx), ISA(Type(v), Mtrx), ISA(Type(X), AlgElt), ISA(Type(Y), ModElt);
Parent(X) eq MatrixAlgebra(Integers(), 2), Parent(Y) eq KMatrixSpace(GF(23), 2, 3), Parent(Z) eq RMatrixSpace(Integers(), 2, 3);
Parent(v) eq RSpace(Integers(), 3), Parent(w) eq VectorSpace(GF(23), 3);
MatrixAlgebra(Integers(), 2) ! [1,2,3,4] eq X;
MatrixRing(GF(23), 2) ! 3;
KMatrixSpace(GF(23), 2, 3) ! [1,-2,3, 4,100,-6] eq Y;
RSpace(Integers(), 3) ! [1,2,3] eq v;

// More forms
Matrix(Integers(), 2, 3, [Vector([1,2,3]), Vector([4,5,6])]);
Matrix([Vector([1,2,3]), Vector([4,5,6])]);
Matrix(Rationals(), [[1,2],[3,4]]);
Matrix(Integers(), 1, 1, [4/2]);
Matrix(GF(5), 1, 1, [1/2]);
Matrix(Integers(), 0, 3, []);
Matrix(Integers(), 3, 0, []);
Matrix(Integers(), 0, 0, []);
Parent(Matrix(Integers(), 0, 0, []));
Matrix(2, 0, [Integers()|]);
ZeroMatrix(GF(7), 2, 3);
IdentityMatrix(Rationals(), 3);
ScalarMatrix(GF(7), 2, 10);
DiagonalMatrix(Integers(), 3, [1, 2, 3]);
DiagonalMatrix([1/2, 2]);
Matrix(DiagonalMatrix([1, 2]));
LowerTriangularMatrix(GF(5), [1, 2, 3]);
UpperTriangularMatrix(Rationals(), [1, 2, 3]);
AntisymmetricMatrix([1, 2, 3]);
AntisymmetricMatrix(GF(7), [1]);
PermutationMatrix(Integers(), [2, 3, 1]);
PermutationMatrix(GF(2), Sym(3)![2,1,3]);

// Vectors
Vector([1, -2, 3]);
Vector(3, [1, 2, 3]);
Vector(GF(7), [1, 2, 10]);
Vector(Rationals(), 2, [1/2, 3]);
Parent(Vector(Rationals(), 2, [1/2, 3]));
Vector(Integers(), []);
Parent(Vector(Integers(), []));

// Errors
Matrix(Integers(), 2, 2, [1,2,3]);
Matrix(Integers(), 1, 1, [1/2]);
Matrix(3, [1,2,3,4]);
Vector(2, [1,2,3]);
DiagonalMatrix([]);
Matrix([]);
Matrix(Integers(), 2, 2, [[1,2],[3,4,5]]);
Matrix(Integers(), 2, 3, [[1,2],[3,4]]);
Matrix(Integers(), 2, 2, [<1,3,1>]);
Matrix([[1,2],[3]]);
Matrix(2, 2, [1,2,3,4,5]);
Matrix(Integers(), -1, 2, []);
KMatrixSpace(Integers(), 2, 2);

// Edge cases
Matrix(Integers(), 2, 2, []);
Matrix(2, 2, [Integers()|]);
M := RandomMatrix(GF(5), 2, 3); Parent(M);
RandomMatrix(Integers(), 2, 2);
Vector(Integers(), 0, []);
ScalarMatrix(0, 5);
Parent(ScalarMatrix(0, 5));
Matrix(Integers(10), 1, 2, [1/3, 2]);
Matrix(GF(4), 2, 2, [1, 2, 3, 4]);
A := RandomSLnZ(3, 2, 10); Parent(A);
B := RandomGLnZ(3, 2, 10); Parent(B);
C := RandomUnimodularMatrix(3, 5); Parent(C);
F := RandomSymplecticMatrix(2, 3); Parent(F);
LowerTriangularMatrix([1, 2]);
SymmetricMatrix([]);
AntisymmetricMatrix([]);
PermutationMatrix(Integers(), [1, 1]);
Matrix(Rationals(), 2, [1, 2, 3]);
Matrix(0, [Integers()|]);
Matrix(0, [1]);
DiagonalMatrix(Integers(), 3, [1, 2]);
ZeroMatrix(Integers(), -1, 2);
IdentityMatrix(GF(3), -2);
Vector([]);
Vector(GF(3), 2, [1, 2, 3]);
Matrix([[GF(3)|]]);
Matrix(Integers(), [[]]);
Matrix([Vector([1,2]), Vector([1,2,3])]);

// Sequences of rows: sequences, vectors, or matrices whose entries make
// the rows; empty rows over a given ring
Matrix([Matrix(1, 2, [1,2]), Matrix(1, 2, [3,4])]);
Parent($1);
Matrix([Matrix(2, 2, [1,2,3,4])]);
Parent($1);
Matrix([Matrix(2, 2, [1,2,3,4]), Matrix(2, 2, [5,6,7,8])]);
Matrix([Matrix(GF(5), 1, 2, [1,2])]);
Parent($1);
Matrix([Vector(GF(5), [1,2])]);
Parent($1);
Matrix([Vector([1,2])] cat [Vector([3,4])]);
Matrix(Rationals(), []);
Parent($1);
Matrix(Rationals(), [[]]);
Parent($1);
Matrix(Rationals(), [[], []]);
Matrix([[GF(5)|]]);
Matrix([[Integers()|]]);
Matrix(GF(5), [[1/2, 1]]);
Matrix([ [1, 2], [1/2, 3] ]);
Matrix([ [GF(5)!1, 2] ]);
Parent($1);
Matrix(Rationals(), 2, [1/2, 3, 1, 1]);

// Errors of the sequence forms
Matrix(Rationals(), [Vector([1,2]), Vector([3,4])]);
Matrix(Rationals(), 2, [Vector([1,2]), Vector([3,4])]);
Matrix(Rationals(), [Matrix(1, 2, [1,2])]);
Matrix(2, [[1,2],[3,4]]);
Matrix(Rationals(), 2, [[1,2],[3,4]]);
Matrix(2, [Vector([1,2])]);
Matrix(Rationals(), [[1], []]);
Matrix([[1], []]);
Matrix([[], [1]]);
Matrix([[]]);
Matrix([Integers()|]);
Matrix(Rationals(), [Integers()|]);
Matrix(Rationals(), [1,2,3,4]);
Matrix([1,2,3,4]);
Matrix(Rationals(), 3, [1, 2]);
Matrix(0, []);
Matrix(Rationals(), 2, [Matrix(GF(5), 1, 2, [1,2])]);
Matrix(Rationals(), 2, [Vector(GF(5), [1,2])]);
Matrix(Rationals(), 2, [Matrix(Rationals(), 1, 2, [1,2])]);
Matrix(Rationals(), 2, {Matrix(Integers(), 1, 2, [1,2])});
Matrix(Rationals(), 2, [[Matrix(Integers(), 1, 2, [1,2])]]);
Matrix([Matrix(1, 2, [1,2])] : Foo := 1);

// Parameters: the forms that Magma writes in its own language (those of
// Matrix taking sequences of sequences, the zero, identity, diagonal and
// random matrices) report them without the argument types
Matrix([[1,2],[3,4]] : Foo := 1);
Matrix([Vector([1,2]), Vector([3,4])] : Foo := 1);
Matrix(Rationals(), [[1,2],[3,4]] : Foo := 1);
Matrix(Rationals(), 2, 2, [1,2,3,4] : Foo := 1);
Matrix(2, [1,2,3,4] : Foo := 1);
ZeroMatrix(Rationals(), 2, 2 : Foo := 1);
IdentityMatrix(Rationals(), 2 : Foo := 1);
ScalarMatrix(2, 3 : Foo := 1);
DiagonalMatrix([1,2] : Foo := 1);
DiagonalMatrix(Rationals(), 2, [1,2] : Foo := 1);
UpperTriangularMatrix([1,2,3] : Foo := 1);
RandomMatrix(GF(5), 2, 2 : Foo := 1);
RandomSLnZ(3, 2, 2 : Foo := 1);
RandomSymplecticMatrix(2, 2 : Foo := 1);
Vector([1,2] : Foo := 1);
