A := SparseMatrix(Integers(), 4, 6, [<1,1,1>, <1,2,2>, <1,5,-1>, <2,2,1>, <2,3,3>, <2,6,-1>, <3,1,2>, <3,4,1>, <3,5,-2>, <4,3,1>, <4,4,4>, <4,6,-1>]);
v := ModularSolution(A, 102);
v[1];
Matrix(Integers(102), 1, 6, Eltseq(v)) * Transpose(Matrix(ChangeRing(A, Integers(102))));
Parent(v);
w := ModularSolution(A, Factorization(102));
Matrix(Integers(102), 1, 6, Eltseq(w)) * Transpose(Matrix(ChangeRing(A, Integers(102))));
u := ModularSolution(A, 102 : Lanczos := true);
Matrix(Integers(102), 1, 6, Eltseq(u)) * Transpose(Matrix(ChangeRing(A, Integers(102))));
