// Benchmark input: deterministic 100 by 100 eigenvalue computation at the
// default real precision. Keep the result live without printing it.
R := RealField();
A := Matrix(R, 100, 100, [((37*i+19*j+i*j) mod 101)-50: i,j in [1..100]]);
E := Eigenvalues(A);
assert #E gt 0;
