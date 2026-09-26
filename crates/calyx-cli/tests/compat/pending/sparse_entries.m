// Handbook H28E2 and the block and row/column operations from text/290.
A := SparseMatrix(2, 3, [<1,2,3>, <2,3,-1>]);
A;
Matrix(A);
A[1];
A[1, 3] := 5;
A[1];

SetEntry(~A, 1, 5, -7);
A;
Matrix(A);

A := SparseMatrix();
A;
SetEntry(~A, 1, 4, -2);
A;
SetEntry(~A, 2, 3, 8);
A;
Matrix(A);
SetEntry(~A, 200, 319, 1);
SetEntry(~A, 200, 3876, 1);
A;
Nrows(A); Ncols(A); NNZEntries(A); Density(A); Support(A, 200);

B := SparseMatrix(4, 5, [<1,1,1>, <1,4,2>, <2,2,3>, <3,5,4>, <4,3,5>]);
Matrix(Submatrix(B, 2, 2, 2, 3));
Matrix(ExtractBlockRange(B, 2, 2, 4, 5));
Matrix(Submatrix(B, [4,1,1], [5,3]));
Matrix(RowSubmatrix(B, 2, 2));
Matrix(RowSubmatrix(B, 3));
Matrix(RowSubmatrixRange(B, 2, 3));
Matrix(ColumnSubmatrix(B, 2, 3));
Matrix(ColumnSubmatrix(B, 4));
Matrix(ColumnSubmatrixRange(B, 2, 4));

C := SparseMatrix(2, 2, [<1,1,9>, <2,2,8>]);
Matrix(InsertBlock(B, C, 2, 3));
InsertBlock(~B, C, 2, 3);
Matrix(B);
Matrix(SwapRows(B, 1, 4));
Matrix(SwapColumns(B, 1, 5));
Matrix(ReverseRows(B));
Matrix(ReverseColumns(B));
Matrix(AddRow(B, -2, 1, 2));
Matrix(AddColumn(B, 3, 1, 2));
Matrix(MultiplyRow(B, 0, 1));
Matrix(MultiplyColumn(B, -2, 3));
Matrix(RemoveRow(B, 2));
Matrix(RemoveColumn(B, 4));
Matrix(RemoveRowColumn(B, 2, 4));
Matrix(RemoveZeroRows(MultiplyRow(B, 0, 1)));
