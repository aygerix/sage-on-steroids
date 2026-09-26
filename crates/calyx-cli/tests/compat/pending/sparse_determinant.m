A := SparseMatrix(Integers(), 4, 4, [<1,1,2>, <1,4,1>, <2,2,3>, <2,3,5>, <3,1,1>, <3,3,7>, <4,2,2>, <4,4,4>]);
Determinant(A);
Determinant(SparseMatrix(GF(7), A));
Determinant(SparseMatrix(Integers(), 0, 0));

// Large enough for structured elimination: a zero row and a zero column.
B := SparseMatrix(Integers(), 600, 600, [<i,i,1> : i in [2..600]]);
Determinant(B), Determinant(SparseMatrix(GF(1009), B));
C := SparseMatrix(Integers(), 600, 600, [<i,i,1> : i in [1..600]] cat [<1,2,1>]);
Determinant(C), Determinant(SparseMatrix(GF(1009), C));
