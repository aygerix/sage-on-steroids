A := SparseMatrix(GF(7), 4, 5, [<1,1,1>, <1,3,2>, <2,2,1>, <2,4,3>, <3,1,2>, <3,3,4>, <4,5,1>]);
N := Nullspace(A);
N;
BasisMatrix(N);
NullspaceMatrix(A);
KernelMatrix(A);
BasisMatrix(Kernel(A));
BasisMatrix(NullspaceOfTranspose(A));
BasisMatrix(Rowspace(A));
Rank(A);

Z := SparseMatrix(Integers(), 4, 3, [<1,1,2>, <1,2,4>, <2,2,3>, <2,3,6>, <3,1,1>, <3,2,2>]);
NullspaceMatrix(Z);
BasisMatrix(Nullspace(Z));
BasisMatrix(Rowspace(Z));
Rank(Z);

E := SparseMatrix(GF(5), 0, 3);
NullspaceMatrix(E);
BasisMatrix(Rowspace(E));
Rank(E);
