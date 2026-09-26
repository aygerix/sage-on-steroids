A := SparseMatrix(GF(7), 3, 3, [<1,1,1>, <1,2,1>, <2,2,2>, <2,3,1>, <3,3,2>]);
MinimalPolynomial(A);
CharacteristicPolynomial(A);
MinimalAndCharacteristicPolynomials(A);
MCPolynomials(A);
FactoredMinimalPolynomial(A);
FactoredCharacteristicPolynomial(A);
FactoredMinimalAndCharacteristicPolynomials(A);
FactoredMCPolynomials(A);
Eigenvalues(A);
BasisMatrix(Eigenspace(A, 2));
ElementaryDivisors(A);

Z := SparseMatrix(Integers(), 3, 4, [<1,1,2>, <1,2,4>, <2,2,6>, <2,3,8>, <3,1,4>, <3,4,10>]);
ElementaryDivisors(Z);
ElementaryDivisors(SparseMatrix(Integers(), 0, 4));
SetVerbose("SparseMatrix", 3);
GetVerbose("SparseMatrix");
SetVerbose("SparseMatrix", false);
