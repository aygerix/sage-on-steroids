// Benchmark input: deterministic 100 by 100 SVD at the default real
// precision. Keep all three results live without printing them.
R := RealField();
A := Matrix(R, 100, 100, [((37*i+19*j+i*j) mod 101)-50: i,j in [1..100]]);
S,U,V := NumericalSingularValueDecomposition(A);
assert Nrows(S) eq 100 and Nrows(U) eq 100 and Nrows(V) eq 100;
