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
Dimension(Radical(V));
