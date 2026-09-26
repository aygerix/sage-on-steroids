A := SparseMatrix(GF(7), 3, 4, [<1,1,1>, <1,4,2>, <2,2,3>, <3,1,4>, <3,3,5>]);
D := Matrix(A);

v := Vector(GF(7), [1, 2, 3]);
v * A;
v * D;

w := Vector(GF(7), [1, 2, 3, 4]);
MultiplyByTranspose(w, A);
w * Transpose(D);

V := Matrix(GF(7), 2, 3, [1, 2, 3, 4, 5, 6]);
V * A;
V * D;

W := Matrix(GF(7), 2, 4, [1, 2, 3, 4, 5, 6, 0, 1]);
MultiplyByTranspose(W, A);
W * Transpose(D);
