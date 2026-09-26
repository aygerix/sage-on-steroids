// Lattice elements (Lattices chapter, "Lattice Elements"): creating them,
// their arithmetic, comparing them, and their entries and coordinates.

// Handbook example H31E4 (Lat_LatticeFunctions)
L := LatticeWithBasis(3, [1,0,0, 1,2,3, 3,6,2]);
L;
Coordelt(L, [1, 2, 1]);
v := L.2;
w := L ! [2, 4, 6];
Eltseq(v);
Coordinates(w);
Coordelt(L, [1, 1, 1]);
Norm(v);
InnerProduct(v, w);
A := MatrixRing(Integers(), 3);
X := A ! [0,-1,0, 1,0,0, 0,1,2];
X;
u := L.1 + L.3;
Determinant(X);
Norm(u);
u * X;
Norm(u * X);

// Creation
S := StandardLattice(3);
S.1; S.2 + 2*S.3; -S.1; S!0; Zero(S); S![1,2,3]; Type(S.1); Parent(S.1);
S.4;
S.0;
S!1;
S![1,2];
S![1/2, 0, 0];
L![1, 1, 1];
Coordelt(L, [1, 2]);
Coordelt(L, [1, 2, 1/2]);
Q := LatticeWithBasis(2, [1/2, 0, 0, 1/3]);
Q.1; Q.2; Q![1/2, 1/3]; Q![1, 0]; CoordinatesToElement(Q, [2, 3]); Zero(Q);

// Arithmetic: integer multiples stay in the lattice, other scalars give
// vectors
2*S.1; S.1*2; S.1/2; Type(S.1/2); Parent(S.1/2); S.1*(1/2); (1/2)*S.1;
(2*S.1) div 2; (2*L.2) div 2;
S.1 div 2;
v := S.1; v +:= S.2; v; v *:= 3; v; v -:= S.3; v;
Q.1 + Q.1; Parent(Q.1 + Q.1) eq Q; 2*Q.1; Q.1*3; Q.1 div 1;
S.2 * MatrixRing(Integers(), 3) ! [1,0,0, 0,0,0, 0,0,1];
S.2 * MatrixRing(Rationals(), 3) ! [1,0,0, 0,1/2,0, 0,0,1];

// Elements of compatible lattices (the same base ring and inner product
// matrix) meet
L1 := Lattice(3, [1,2,3, 3,2,1]);
x := L1.1 + S.1; x; Parent(x) eq S;
L1.1 eq S![2,0,-2]; S![2,0,-2] in L1; S.1 in L1; L1!S![2,0,-2];
L1!S.1;
S.1 eq Q.1;
S.1 + Q.1;
S.1 in Q;
InnerProduct(S.1, Q.1);
M := MatrixRing(Integers(), 3) ! [2,1,0, 1,2,0, 0,0,1];
L2 := LatticeWithBasis(3, [1,0,0, 0,1,0, 0,0,1], M);
L2.1 + S.1;

// Access
v := S![0, 5, 0];
Support(v); IsZero(v); IsZero(S!0); Eltseq(v); ElementToSequence(v); Coordinates(v); Degree(v);
Norm(Q.1); Type(Norm(Q.1)); InnerProduct(Q.1, Q.2); Eltseq(Q.1); Length(S![1,2,3]); Length(Q.1);
Coordinates(Q.1 + Q.2); Coordinates(Q, Q.1 + Q.2); CoordinateVector(Q.1 + 2*Q.2);
Coordinates(L1, S![2,0,-2]); CoordinateVector(L1, S![2,0,-2]);
Coordinates(L1, S.1);
