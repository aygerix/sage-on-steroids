// The Numerical prefix may be omitted for real and complex matrices. These
// overloads return numerical matrices rather than the exact spaces/tuples.

R := RealField(12);
A := Matrix(R, 3, 2, [1,0,0,1,1,1]);
Rank(A), Nrows(Kernel(A)), Nrows(Image(A));
P := Pseudoinverse(A);
Nrows(P), Ncols(P);
v,k := Solution(A, Vector(R,[2,3]));
Ncols(v), Nrows(k);
ok,v,k := IsConsistent(A, Vector(R,[2,3]));
ok, Ncols(v), Nrows(k);
Nrows(Inverse(Matrix(R,2,2,[1,2,3,5])));

H,Q := HessenbergForm(Matrix(R,3,3,[1,2,3,4,5,7,8,10,11]));
Nrows(H), Nrows(Q);
S,Q := SchurForm(Matrix(R,3,3,[1,2,3,4,5,7,8,10,11]));
Nrows(S), Nrows(Q);
#Eigenvalues(Matrix(R,2,2,[0,-1,1,0]));
B,U,V := BidiagonalForm(A);
<Nrows(B),Ncols(B)>, <Nrows(U),Ncols(U)>, <Nrows(V),Ncols(V)>;
S,U,V := SingularValueDecomposition(A);
<Nrows(S),Ncols(S)>, <Nrows(U),Ncols(U)>, <Nrows(V),Ncols(V)>;
