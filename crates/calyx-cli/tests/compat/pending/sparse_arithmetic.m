Z := SparseMatrix(Integers(), 3, 3);
I := IdentitySparseMatrix(Integers(), 3);
N := ScalarSparseMatrix(3, -1);
D := DiagonalSparseMatrix([2, 2, 2]);
A := SparseMatrix(3, 3, [<1,1,1>, <1,3,2>, <2,2,3>, <3,1,4>]);
B := SparseMatrix(3, 3, [<1,2,5>, <2,1,6>, <2,2,-3>, <3,3,7>]);

IsZero(Z); IsZero(A);
IsOne(I); IsOne(A);
IsMinusOne(N); IsMinusOne(I);
IsScalar(D); IsScalar(A);
IsDiagonal(D); IsDiagonal(A);
IsSymmetric(A); IsSymmetric(A + Transpose(A));
IsUpperTriangular(A); IsLowerTriangular(A);
A eq A; A eq B; A ne B;

Matrix(A + B);
Matrix(A - B);
Matrix(A * B);
Matrix(3 * A);
Matrix(A * -2);
Matrix(-A);
Matrix(A^0);
Matrix(A^2);
Matrix(Transpose(A));

F := SparseMatrix(GF(7), 2, 2, [<1,1,1>, <1,2,2>, <2,2,1>]);
Matrix(F^-1);
Matrix(F * F^-1);

E := SparseMatrix(Integers(), 0, 0);
IsOne(E); IsMinusOne(E); IsScalar(E); IsDiagonal(E); IsSymmetric(E);
Matrix(E^0);
