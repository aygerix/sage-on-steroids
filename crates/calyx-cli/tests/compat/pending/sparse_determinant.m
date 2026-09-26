A := SparseMatrix(Integers(), 4, 4, [<1,1,2>, <1,4,1>, <2,2,3>, <2,3,5>, <3,1,1>, <3,3,7>, <4,2,2>, <4,4,4>]);
Determinant(A);
Determinant(SparseMatrix(GF(7), A));
Determinant(SparseMatrix(Integers(), 0, 0));
