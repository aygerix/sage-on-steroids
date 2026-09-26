// Added after 2.22.
A := Matrix(GF(5),2,2,[1,2,3,4]);
EnsureUpperTriangular(A);

V := VectorSpace(GF(5),2,Matrix(GF(5),2,2,[1,0,0,0]));
IsDegenerate(V);

// Characteristic-two singular radical of a quadratic space.
K := GF(4);
Q := Matrix(K,3,3,[1,1,0, 0,0,0, 0,0,0]);
X := QuadraticSpace(Q);
BasisMatrix(Radical(X));
BasisMatrix(SingularRadical(X));
IsNonsingular(X);
