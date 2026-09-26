A := SparseMatrix(2, 3, [<1,1,1>, <1,3,2>, <2,2,3>]);
B := SparseMatrix(2, 2, [<1,2,4>, <2,1,5>]);
Matrix(HorizontalJoin(A, B));
Matrix(VerticalJoin(A, SparseMatrix(1, 3, [<1,2,6>])));
Matrix(DiagonalJoin(A, B));

D := Matrix(A);
D;
S := SparseMatrix(D);
S;
S eq A;
Parent(S);

Q := ChangeRing(A, Rationals());
Q;
Matrix(Q);
SparseMatrix(GF(7), A);
SparseMatrixStructure(Rationals()) ! A;

Matrix(SparseMatrix(Matrix(Integers(), 0, 4, [])));
Matrix(SparseMatrix(Matrix(Integers(), 3, 0, [])));
