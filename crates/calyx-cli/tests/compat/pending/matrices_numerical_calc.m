// Ill-conditioned product for a 2.29 calculator recording. Singular values
// 14 through 40 sit on one rounding floor, so its reported rank is
// implementation-dependent rather than a compatibility requirement.
R := RealField(30);
A := Matrix(R, 40, 20, [ (i + 2*j) / (i + j + 1) : i in [1..40], j in [1..20]]);
B := Matrix(R, 20, 40, [ (3*i - j) / (i + 2*j + 5) : i in [1..20], j in [1..40]]);
Rank(A * B);
NumericalRank(A * B);
