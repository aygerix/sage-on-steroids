// Words that start in the first half of a line fill it to column 79 and continue after a backslash;
// words that start in the second half move to the next line. A continued word keeps the indentation
// of the place it started in (4 inside a polynomial).
P<x, y, z> := PolynomialRing(Rationals(), 3);
119/44*x^2 - 15798558582429/4*y^2 + 34932799628335074761085292707227419544217/934*z^2 - 1;
(10^30 + 1)*x^2 + (10^40 + 3)/7*y^2 + 12345678901234567890123/11*z;
// Long terms that start late break at the space before them.
Q<t> := PolynomialRing(Integers());
t^3 + 123456789012345678901234567890123456789012345678901234567890123456789*t + 1;
t^3 + (10^49 + 7)*t^2 + (10^28 + 9)*t + 1;
// The threshold: a 62-character term starting in columns 39 to 42 (0-based).
for m in [30 .. 36] do
  (10^(m-1) + 1)*t^2 + (10^59 + 3)*t + 1;
end for;
// Early and late words ending in the last columns, followed by a comma or bracket.
for k in [72 .. 76] do
  <1, 10^k>; [1, 10^k, 2]; <10^k, 1>;
  <1, t^2 + (10^(k-7) + 1)*t>;
end for;
// Reals of every length around the edge.
for d in [72 .. 76] do
  R := RealField(d); <1, Pi(R)>; [Pi(R), Pi(R)];
end for;
// Words in strings and messages.
print "a b c d e f g h i j k l m n o p q r s t u v w x y z aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
print "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
[t^2 + 123456789012345678901234567890123456789012345678901234567890*t + 1, t + 1];
// A polynomial, then numbers that wrap at spaces.
<t^2 + t, 10^40, 10^40, 10^40>;
[t^2 + t, 10^40, 10^40, 10^40];
<1, 10^40, t^2 + t, 10^40, 10^40>;
// A polynomial that ends in the column before the last, then more.
<1, t^2 + (10^66 + 1)*t>;
<1, t^2 + (10^66 + 1)*t, 1>;
<1, t^2 + (10^66 + 1)*t, 10^40, 10^40, 10^40>;
<1, t^2 + (10^66 + 1)*t, t + 1, 10^40, 10^40>;
[t^2 + (10^68 + 1)*t];
[t^2 + (10^68 + 1)*t, 1];
// A polynomial that wraps inside, then more.
<1, t^3 + (10^60 + 1)*t^2 + (10^60 + 1)*t, 10^40, 10^40>;
// The threshold is half of the line after its indentation: a word too long for any line starting
// in columns 40 and 41 at indentation 0, 42 and 43 at 4 (continued) and 44 and 45 at 8 (nested).
big := 10^79 + 1;
for k in [34, 35] do (10^k + 1)*t + big; end for;
for k in [31, 32] do (10^(80+k) + 1)*t + big; end for;
for k in [30, 31] do [[(10^k + 1)*t + big]]; end for;
