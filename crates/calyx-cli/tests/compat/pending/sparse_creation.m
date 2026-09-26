// Handbook H28E1 and the structured constructors from text/288.
A := SparseMatrix(2, 3, [<1,2,3>, <2,3,-1>]);
A;
Matrix(A);

A := SparseMatrix(GF(23), 2, 3, [<1,2,3>, <2,3,-1>]);
A;
Matrix(A);

K<w> := GF(2^4);
A := SparseMatrix(K, 2, 3, [<1,2,3>, <2,3,w>]);
A;
Matrix(A);
A: Magma;

A := SparseMatrix(4,5, [1,3,-1, 3,2,9,3,7,4,-3, 0, 1,4,3]);
A;
Matrix(A);
A: Magma;

IdentitySparseMatrix(Rationals(), 3);
ScalarSparseMatrix(3, -4);
ScalarSparseMatrix(GF(7), 2, 10);
DiagonalSparseMatrix(Integers(), 3, [1, 0, 3]);
DiagonalSparseMatrix(GF(23), [1, 2, -3]);
DiagonalSparseMatrix([1/2, 2]);
SparseMatrix(Integers(), 0, 4);
SparseMatrix(3, 0);
SparseMatrix();
SparseMatrixStructure(Integers());
