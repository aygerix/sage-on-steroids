A := SparseMatrix(Integers(), 4, 5, [<1,3,-1>, <2,2,9>, <2,3,7>, <2,4,-3>, <4,4,3>]);
BaseRing(A);
CoefficientRing(A);
Nrows(A); NumberOfRows(A);
Ncols(A); NumberOfColumns(A);
Eltseq(A);
ElementToSequence(A);
NNZEntries(A); NumberOfNonZeroEntries(A);
Density(A);
Support(A);
Support(A, 2);
RowWeight(A, 3);
RowWeights(A);
ColumnWeight(A, 4);
ColumnWeights(A);

Z := SparseMatrix(Integers(), 0, 7);
Nrows(Z); Ncols(Z); NNZEntries(Z); Density(Z); Support(Z);
