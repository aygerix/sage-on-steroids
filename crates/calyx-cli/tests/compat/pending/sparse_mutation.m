S := SparseMatrix(4, 5, [<1,1,1>, <1,4,2>, <2,2,3>, <3,5,4>, <4,3,5>]);

A := S; SwapRows(~A, 1, 4); Matrix(A); Matrix(S);
A := S; SwapColumns(~A, 1, 5); Matrix(A);
A := S; ReverseRows(~A); Matrix(A);
A := S; ReverseColumns(~A); Matrix(A);
A := S; AddRow(~A, -2, 1, 2); Matrix(A);
A := S; AddColumn(~A, 3, 1, 2); Matrix(A);
A := S; MultiplyRow(~A, 0, 1); Matrix(A);
A := S; MultiplyColumn(~A, -2, 3); Matrix(A);
A := S; RemoveRow(~A, 2); Matrix(A);
A := S; RemoveColumn(~A, 4); Matrix(A);
A := S; RemoveRowColumn(~A, 2, 4); Matrix(A);
A := S; MultiplyRow(~A, 0, 1); RemoveZeroRows(~A); Matrix(A);
