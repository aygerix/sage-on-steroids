// Benchmark input shared with Magma 2.22: deterministic 100 by 100 RQ at
// the default real precision. Keep both results live without printing them.
R := RealField();
A := Matrix(R, 100, 100, [((37*i+19*j+i*j) mod 101)-50: i,j in [1..100]]);
T,Q := RQDecomposition(A);
assert Nrows(T) eq 100 and Nrows(Q) eq 100;
