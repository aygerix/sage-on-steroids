// Numerical linear algebra (text/282). Decomposition factors are not
// unique, so test their shapes, identities and ordering instead of entries.

RR := RealField(15);
CC<i> := ComplexField(15);

function CT(A)
    return Matrix([[Conjugate(A[c,r]): c in [1..Nrows(A)]]: r in [1..Ncols(A)]]);
end function;

function Small(A)
    return Max([Abs(x): x in Eltseq(A)]) lt 1e-10;
end function;

// RQ and QL, wide and tall, real and complex. Q has determinant one.
procedure CheckRQQL(A)
    R,Q := RQDecomposition(A);
    Small(R*Q-A), <Nrows(R),Ncols(R)>, <Nrows(Q),Ncols(Q)>, Small(Q*Transpose(Q)-1), Abs(Determinant(Q)-1) lt 1e-10;
    Q,L := QLDecomposition(A);
    Small(Q*L-A), <Nrows(Q),Ncols(Q)>, <Nrows(L),Ncols(L)>, Small(Q*Transpose(Q)-1), Abs(Determinant(Q)-1) lt 1e-10;
end procedure;
CheckRQQL(Matrix(RR, 2, 3, [1,2,3,4,5,6]));
CheckRQQL(Matrix(RR, 3, 2, [1,2,3,4,5,7]));
Z := Matrix(CC, 3, 2, [1+i,2,3*i,4-i,2+i,1-2*i]);
R,Q := RQDecomposition(Z);
Small(R*Q-Z), Small(Q*CT(Q)-1), Abs(Determinant(Q)-1) lt 1e-10;
Q,L := QLDecomposition(Z);
Small(Q*L-Z), Small(Q*CT(Q)-1), Abs(Determinant(Q)-1) lt 1e-10;

// Inverse, rank, row kernel, row image, solutions and pseudoinverse.
A := Matrix(RR, 3, 2, [1,0,0,1,1,1]);
K := NumericalKernel(A); I := NumericalImage(A); P := NumericalPseudoinverse(A);
NumericalRank(A), <Nrows(K),Ncols(K)>, Small(K*A), <Nrows(I),Ncols(I)>;
Small(P*A*P-P), Small(A*P*A-A), Small(P*A-Transpose(P*A)), Small(A*P-Transpose(A*P));
w := Vector(RR, [2,3]);
v,k := NumericalSolution(A,w);
Small(Matrix(v*A-w)), Small(k*A), <Nrows(k),Ncols(k)>;
ok,v,k := NumericalIsConsistent(A,w);
ok, Small(Matrix(v*A-w)), Small(k*A);
NumericalIsConsistent(Matrix(RR,2,2,[1,0,0,0]), Vector(RR,[0,1]));
A0 := Matrix(RR, 3, 2, [1,0,2,0,3,0]);
NumericalRank(A0), NumericalRank(A0:Epsilon:=0.1), Small(NumericalKernel(A0)*A0);
R2 := RealField(30);
A2 := Matrix(R2, 40, 20, [ ((37*i + 19*j + i*j) mod 101) - 50 : i in [1..40], j in [1..20]]);
B2 := Matrix(R2, 20, 40, [ ((23*i + 41*j + 3*i*j) mod 103) - 51 : i in [1..20], j in [1..40]]);
NumericalRank(A2 * B2);
B := Matrix(RR, 3, 3, [1,2,3,4,5,7,8,10,11]);
Small(B*NumericalInverse(B)-1);

// Hessenberg and Schur transformations, and ordered eigenvalues.
H,Q := NumericalHessenbergForm(B);
Small(H-Q*B*Transpose(Q)), Small(Q*Transpose(Q)-1), Abs(H[3,1]) lt 1e-10;
S,Q := NumericalSchurForm(B);
Small(S-Q*B*Transpose(Q)), Small(Q*Transpose(Q)-1), Abs(S[3,1]) lt 1e-10;
D := Matrix(RR, 3, 3, [0,-1,0,1,0,0,0,0,2]);
E := NumericalEigenvalues(D);
#E, Abs(&+E-Trace(D)) lt 1e-10, Real(E[1]) le Real(E[2]) and Real(E[2]) le Real(E[3]);
V := NumericalEigenvectors(D, CC!i);
#V, Small(Matrix(V[1])*ChangeRing(D,CC)-Matrix(V[1])*ScalarMatrix(3,i));

// Bidiagonal form and SVD, including their full unitary factors.
A := Matrix(RR, 2, 3, [1,2,3,4,5,6]);
B,U,V := NumericalBidiagonalForm(A);
Small(B-U*A*Transpose(V)), Small(U*Transpose(U)-1), Small(V*Transpose(V)-1), <Nrows(B),Ncols(B)>;
S,U,V := NumericalSingularValueDecomposition(A);
Small(S-U*A*Transpose(V)), Small(U*Transpose(U)-1), Small(V*Transpose(V)-1), S[1,1] ge S[2,2] and S[2,2] ge 0;
B,U,V := NumericalBidiagonalForm(Z);
Small(B-U*Z*CT(V)), Small(U*CT(U)-1), Small(V*CT(V)-1), <Nrows(B),Ncols(B)>;
S,U,V := NumericalSingularValueDecomposition(Z);
Small(S-U*Z*CT(V)), Small(U*CT(U)-1), Small(V*CT(V)-1), Real(S[1,1]) ge Real(S[2,2]) and Real(S[2,2]) ge 0;

// The large-matrix path uses FLINT's arbitrary-precision shifted QR on the
// Hermitian Gram matrix, then reorthogonalizes the singular vectors.
n := 20;
A := Matrix(RR, n, n, [((37*i+19*j+i*j) mod 101)-50: i,j in [1..n]]);
S,U,V := NumericalSingularValueDecomposition(A);
Small(S-U*A*Transpose(V)), Small(U*Transpose(U)-1), Small(V*Transpose(V)-1);
