// Handbook H30E1.
K := GF(11);
J := Matrix(K,3,3,[1,2,3, 4,5,6, 7,8,9]);
V := VectorSpace(K,3,J);
InnerProductMatrix(V);

u := V![1,2,3];
v := V![4,5,6];
DotProduct(u,v);
DotProductMatrix([u,v]);
GramMatrix(V);
IsNondegenerate(V);
R := Radical(V);
BasisMatrix(R);
OrthogonalComplement(V,R) eq V;
RR := Radical(V : Right := true);
BasisMatrix(RR);
OrthogonalComplement(V,RR : Right := true) eq V;

// A degenerate hermitian form distinguishes the left and right radicals.
L<a> := GF(9);
H, sigma := StandardHermitianForm(3,L);
H[2,2] := 0;
U := VectorSpace(L,3,H);
U`Involution := sigma;
BasisMatrix(Radical(U));
BasisMatrix(Radical(U : Right := true));
IsNondegenerate(U);
GramMatrix(U);
DotProductMatrix(Basis(U));
