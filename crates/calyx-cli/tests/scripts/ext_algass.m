// The associative algebras go through the core's plug-in point for kinds
// defined outside it (ext.rs): equality and hashing of elements and
// structures, printing inside aggregates, coercion both ways, operators.
Q := Rationals();
A := Algebra(Q, Q);
B := Algebra(Q, Q);
x := A.1;
#{x, 2*x, x, A!2, A!1}; #{A, A, B}; #{x, B.1};
[x, 2*x, -x]; <x, 3/4>; [* x, A *];
x cmpeq 2; x cmpeq A!1; x cmpeq B.1; A cmpeq B; A eq A;
IsCoercible(A, 3); IsCoercible(A, B.1); IsCoercible(Q, 2*x); IsCoercible(Integers(), x/2);
Type(x); Type(A); Parent(x) eq A; x in A; x in B;
-x; -(A!0); x^-2; (3*x)^2 - 9*x;
A eq B;
// Operators on the algebras themselves go to the kind's structure hook.
A * B;
A + 1;
A * IdentityMatrix(Q, 2);
2 in A; (1/2) in A; B.1 in A; A subset A;
