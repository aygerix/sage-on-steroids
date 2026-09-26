SetAutoColumns(false);
SetSeed(1);
A := RandomMatrix(GF(10007), 3000, 3000);
print "matrix-rank", Rank(A);
