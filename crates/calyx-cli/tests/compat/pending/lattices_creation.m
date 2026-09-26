// Creation of lattices (Lattices chapter, "Creation of Lattices"): from
// generators, from a basis and from a Gram matrix, the standard,
// coordinate and scaled lattices, and how lattices print.

// Handbook example H31E1 (Lat_LatticeCreate)
B := RMatrixSpace(IntegerRing(), 2, 3) ! [1,2,3, 3,2,1];
B;
L1 := Lattice(B);
L1;
L2 := Lattice(3, [1,2,3, 3,2,1]);
L2 eq L1;
L3 := LatticeWithBasis(B);
L3;
L4 := LatticeWithBasis(3, [1,2,3, 3,2,1]);
L4 eq L3, L1 eq L3;
B := RMatrixSpace(IntegerRing(), 2, 3) ! [1,2,3, 3,2,1];
M := MatrixRing(IntegerRing(), 3) ! [3,-1,1, -1,3,1, 1,1,3];
M;
IsPositiveDefinite(M);
L := LatticeWithBasis(B, M);
L;
GramMatrix(L);
F := MatrixRing(IntegerRing(), 2) ! [56,40, 40,40];
C := LatticeWithGram(F);
C;
GramMatrix(C);
C eq CoordinateLattice(L);
GramMatrix(C) eq GramMatrix(L);
C eq L;

// Printing: the determinant, unless both the basis and the inner product
// matrix are multiples of the identity, and each of them as an integral
// matrix with a denominator
StandardLattice(3);
StandardLattice(0);
LatticeWithBasis(2, [1,1, 0,1]);
LatticeWithBasis(2, [0,1, 1,0]);
LatticeWithBasis(2, [1,0]);
LatticeWithBasis(2, [1/2,0, 0,1/2]);
LatticeWithBasis(2, [1/2,0, 0,1/3]);
LatticeWithGram(2, [2,1, 1,1]);
LatticeWithGram(1, [15/4]);
LatticeWithGram(1, [1/2]);
LatticeWithGram(1, [3/10]);
LatticeWithGram(1, [15/14]);
LatticeWithGram(1, [12]);
LatticeWithGram(2, [1/2, 0, 0, 1/3]);
LatticeWithGram(2, [30030, 0, 0, 1]);
LatticeWithGram(2, [2^40, 0, 0, 3^20]);
LatticeWithBasis(2, [1/2, 0, 0, 1], MatrixRing(Rationals(), 2) ! [2, 1/3, 1/3, 2]);
Lattice(3, [0,0,0]);
Type(L); Category(L);

// Gram matrices in full or by their lower triangle
LatticeWithGram(2, [2, 1, 2]) eq LatticeWithGram(2, [2, 1, 1, 2]);
LatticeWithGram(3, [4, 2, 4, 2, 2, 4]);
LatticeWithGram(MatrixRing(Integers(), 2) ! [2, 1, 1, 2]);

// Generators reduced to a basis
Lattice(2, [6, 0, 0, 10]);
Lattice(Matrix(Integers(), 3, 2, [1, 2, 2, 4, 3, 6]));
Lattice(RSpace(Integers(), 2));
Lattice(3, [1/2, 1/3, 1, 0, 1, 0]);
LatticeWithBasis(RMatrixSpace(Integers(), 2, 2) ! [1,2,3,4]);
BaseRing(Lattice(Matrix(Rationals(), 2, 2, [1, 0, 0, 1])));

// Errors
LatticeWithBasis(2, [1,1, 2,2]);
LatticeWithGram(2, [1, 2, 1]);
LatticeWithGram(Matrix(Integers(), 2, 2, [2, 1, 0, 2]));
LatticeWithGram(2, [1, 2, 3, 4, 5]);
Lattice(2, [1, 2, 3]);
LatticeWithBasis(2, [1, 0, 0, 1], MatrixRing(Rationals(), 2) ! [2, 1/3, 1/3, 2]);
LatticeWithBasis(2, [1/2, 0, 0, 1], MatrixRing(Integers(), 2) ! [2, 1, 1, 2]);
LatticeWithBasis(2, [1, 0, 0, 1], MatrixRing(Integers(), 3) ! 1);

// The coordinate and scaled lattices
L := LatticeWithBasis(B, M);
CoordinateLattice(LatticeWithBasis(2, [1/2, 0, 0, 1/3]));
ScaledLattice(L, 2);
ScaledLattice(L, 1/2);
ScaledLattice(L, -1);
Module(L) eq L, ZLattice(L) eq L;
