SetAutoColumns(false);
SetSeed(1);
F := GF(10007);
A := RandomMatrix(F, 3000, 3000);
B := RandomMatrix(F, 3000, 3000);
C := A * B;
print "matrix-product", C[1, 1], C[3000, 3000];
