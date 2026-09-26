// Rational approximation (Rational Field chapter): Qround, continued
// fractions and rational reconstruction. 2.22 lacks ContinuedFractionValue
// and the Hirzebruch-Jung continued fractions, which the handbook
// documents; they are tested only on expansions that the forward functions
// return, where the handbook fixes the value. Qround with ContFrac and a
// negative bound fails inside Magma's package code, so it is not tested.
// RationalReconstruction of a matrix is tested in rationals_linear.m.
Q := Rationals();

// Qround: by default Ceiling(q*M)/M, with ContFrac a convergent
Qround(355/113, 10); Qround(355/113, 100); Qround(355/113, 1000); Qround(-355/113, 10);
Qround(355/113, 10 : ContFrac); Qround(355/113, 100 : ContFrac); Qround(-355/113, 10 : ContFrac);
Qround(22/7, 1); Qround(22/7, 1 : ContFrac);
Qround(1/2, 0); Qround(1/2, 0 : ContFrac); Qround(0/1, 5); Qround(5/1, 5); Qround(5/1, 5 : ContFrac);
[Qround(x/97, 10) : x in [1..30]];
[Qround(x/97, 10 : ContFrac) : x in [1..30]];
[Qround(a/b, M) : a in [-5..5], b in [1..5], M in [-3..3] | Gcd(a, b) eq 1];
for M in [1..6] do
    [Qround(a/b, M : ContFrac) : a in [-b..2*b], b in [1..8] | Gcd(a, b) eq 1];
end for;
Qround(1/101, 100 : ContFrac); Qround(10^20 + 1/7, 6 : ContFrac); Qround(-7 - 1/1000001, 1000000 : ContFrac);
Qround(1/(2^70 + 1), 2^70 : ContFrac); Qround(1/(2^70 + 1), 2^70);
Qround(51/103, 102 : ContFrac); Qround(101/102, 101 : ContFrac);
Parent(Qround(1/3, 2));
Qround(3, 5);
Qround(1/3, 1/2);

// continued fractions
ContinuedFraction(355/113); ContinuedFraction(-355/113); ContinuedFraction(1/3); ContinuedFraction(3/4);
ContinuedFraction(0/1); ContinuedFraction(5/1); ContinuedFraction(-5/1); ContinuedFraction(-1/2);
ContinuedFraction(3); ContinuedFraction(-3); ContinuedFraction(0);
ContinuedFraction(10^30/7);
ContinuedFraction(Fibonacci(40)/Fibonacci(39));
// Bound limits the quotients (to at least one); a negative small integer is
// refused, and one of 2^30 or more leaves them unlimited.
ContinuedFraction(355/113 : Bound := 2); ContinuedFraction(355/113 : Bound := 1); ContinuedFraction(355/113 : Bound := 0);
ContinuedFraction(355/113 : Bound := 3); ContinuedFraction(355/113 : Bound := 100); ContinuedFraction(-355/113 : Bound := 2);
ContinuedFraction(0/1 : Bound := 0); ContinuedFraction(3/4 : Bound := 1); ContinuedFraction(10^30/7 : Bound := 3);
ContinuedFraction(Fibonacci(40)/Fibonacci(39) : Bound := 10);
ContinuedFraction(355/113 : Bound := 2^70); ContinuedFraction(355/113 : Bound := -2^70); ContinuedFraction(355/113 : Bound := -2^30);
ContinuedFraction(355/113 : Bound := -1);
ContinuedFraction(355/113 : Bound := -(2^30 - 1));
ContinuedFraction(355/113 : Bound := "x");
ContinuedFraction(355/113 : Bound := 1/2);
ContinuedFraction(355/113 : Numerators := [1, 1, 1]);
ContinuedFraction(355/113 : Bound := -1, Numerators := [1]);
ContinuedFractionValue([3, 7, 16]); ContinuedFractionValue([-4, 1, 6, 16]); ContinuedFractionValue([5]);
ContinuedFractionValue([0, 3]); ContinuedFractionValue([1, 1, 1, 1, 2]); ContinuedFractionValue([-1, 2]);
Parent(ContinuedFractionValue([2]));
forall{q : q in [a/b : a in [-30..30], b in [1..30]] | ContinuedFractionValue(ContinuedFraction(q)) eq q};

// Hirzebruch-Jung continued fractions: q = a1 - 1/(a2 - 1/(a3 - ...))
HirzebruchJungContinuedFraction(7/3); HJContinuedFraction(7/3);
HJContinuedFraction(5/2); HJContinuedFraction(10/7); HJContinuedFraction(1/2); HJContinuedFraction(-1/2);
HJContinuedFraction(3/1); HJContinuedFraction(0/1); HJContinuedFraction(-7/3);
HirzebruchJungContinuedFractionValue([3, 2, 2]); HJContinuedFractionValue([3, 2, 2]);
HJContinuedFractionValue([2, 2, 2, 2]); HJContinuedFractionValue([5]); HJContinuedFractionValue([1, 2]);
forall{q : q in [a/b : a in [-30..30], b in [1..30]] | HJContinuedFractionValue(HJContinuedFraction(q)) eq q};
forall{q : q in [a/b : a in [1..30], b in [1..30]] | forall{c : c in HJContinuedFraction(q)[2..#HJContinuedFraction(q)] | c ge 2}};

// rational reconstruction: |n|, d <= Sqrt(m/2)
RationalReconstruction(Integers(1001)!500);
RationalReconstruction(GF(1009)!505);
ok, r := RationalReconstruction(Integers(10)!3); ok; assigned r;
RationalReconstruction(Integers(10)!3);
for m in [1..12] cat [72, 98, 128] do
    R := Integers(m);
    [<s, r> where ok, r := RationalReconstruction(R!s) : s in [0..m-1] | ok];
end for;
[<s, r> where ok, r := RationalReconstruction(GF(29)!s) : s in [0..28] | ok];
RationalReconstruction(Integers(10^30 + 1)!(10^29));
p := 2^127 - 1; q := -1234567/9876543;
RationalReconstruction(GF(p)!q);
RationalReconstruction(Integers(p^2)!q);
RationalReconstruction(Integers(p)!q);
m := 2*10^40; RationalReconstruction(Integers(m)!(Integers(m)!(10^20) / (Integers(m)!(10^20 - 1))));
RationalReconstruction(GF(4).1);
RationalReconstruction(GF(9)!1);
RationalReconstruction(3);
