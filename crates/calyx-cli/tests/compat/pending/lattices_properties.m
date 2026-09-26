// Properties of lattices (Lattices chapter, "Properties of Lattices"):
// the associated structures, attributes and predicates, and the base
// ring.
B := RMatrixSpace(IntegerRing(), 2, 3) ! [1,2,3, 3,2,1];
M := MatrixRing(IntegerRing(), 3) ! [3,-1,1, -1,3,1, 1,1,3];
L := LatticeWithBasis(B, M);
Rank(L); Dimension(L); Degree(L); Determinant(L);
BasisMatrix(L); InnerProductMatrix(L); Basis(L); GramMatrix(L); BasisDenominator(L);
BaseRing(L); CoefficientRing(L); CoordinateRing(L); Order(L);
IsIntegral(L); IsEven(L); IsExact(L); IsFull(L); IsZero(L); IsHermitian(L); IsQuadratic(L);
Content(L); Level(L); QuadraticForm(L);
V, f := AmbientSpace(L); V; f; f(L.2); Norm(f(L.2)) eq Norm(L.2);
W, g := CoordinateSpace(L); W; g; g(L.1 + 2*L.2);
CoordinateSpace(LatticeWithBasis(2, [1/2, 0, 0, 1/3]));

// A lattice over Q
Q := LatticeWithBasis(2, [1/2, 0, 0, 1/3]);
Basis(Q); BasisDenominator(Q); BasisMatrix(Q); Parent(BasisMatrix(Q)); BaseRing(Q);
Content(Q); Determinant(Q); IsIntegral(Q); IsEven(Q); QuadraticForm(Q);
Level(Q);
G := LatticeWithGram(2, [1/2, 0, 0, 1/3]);
GramMatrix(G); InnerProductMatrix(G); BaseRing(G); Determinant(G); Type(Determinant(G));

// Content, level and evenness
S := StandardLattice(3);
Content(S); Level(S); QuadraticForm(S); IsFull(S);
Level(LatticeWithGram(2, [2, 1, 1, 2]));
Level(LatticeWithGram(3, [2, 1, 2, 0, 1, 2]));
Level(LatticeWithGram(2, [6, 0, 0, 10]));
Content(LatticeWithGram(2, [6, 4, 4, 10]));
Content(LatticeWithGram(2, [1/2, 1/3, 1/3, 1/2]));
IsEven(LatticeWithGram(2, [2, 1, 1, 2])); IsEven(LatticeWithGram(2, [2, 1, 1, 3]));
QuadraticForm(LatticeWithGram(3, [2, 1, 2, 0, 1, 2]));
Z := Lattice(3, [0, 0, 0]); Z; Rank(Z); IsZero(Z); Determinant(Z); Content(Z);

// Comparing lattices
S subset StandardLattice(3);
LatticeWithBasis(3, [2,0,0, 0,1,0, 0,0,1]) subset S;
S subset LatticeWithBasis(3, [2,0,0, 0,1,0, 0,0,1]);
S eq LatticeWithBasis(3, [1,1,0, 0,1,0, 0,0,1]);
Q subset S;

// Gram matrices of elements and of matrices
GramMatrix([S.1, S.2 + S.3]);
GramMatrix([Q.1, Q.1 + Q.2]);
GramMatrix(Matrix(Integers(), 2, 2, [1,2,3,4]));
GramMatrix(Matrix(Rationals(), 2, 3, [1/2,0,1, 0,1,1]));

// Definiteness
IsPositiveDefinite(MatrixRing(Integers(), 2) ! [2, 1, 1, 2]);
IsPositiveDefinite(MatrixRing(Rationals(), 2) ! [1/2, 1, 1, 2]);
IsPositiveDefinite(MatrixRing(Integers(), 0) ! []);
IsPositiveDefinite(MatrixRing(Integers(), 2) ! [2, 1, 0, 2]);
IsPositiveDefinite(Matrix(Integers(), 2, 3, [1,0,0, 0,1,0]));
