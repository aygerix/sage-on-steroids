// Arithmetic of Dirichlet characters, comparisons and coercions between
// groups, Kronecker characters, decompositions and base rings.
a4 := DirichletGroup(4).1; a3 := DirichletGroup(3).1;
a4 * a3; Parent(a4 * a3);
a4 eq a3; a4 eq DirichletGroup(4).1; a4 eq DirichletGroup(8)!a4;
k := KroneckerCharacter(-4);
k * a3; Parent(k * a3); a3 * k; Parent(a3 * k);
k eq a4; k * a3 eq KroneckerCharacter(12);
k / k; Parent(k / k);
DirichletGroup(5).1 * DirichletGroup(5, Integers()).1;
Parent(DirichletGroup(5).1 * DirichletGroup(5, Integers()).1);
x := DirichletGroup(7, GF(13)).1; y := DirichletGroup(5, GF(13)).1;
x * y; Parent(x * y); Eltseq(x * y); ValuesOnUnitGenerators(x * y);
x / y; x^-1; x^0; x^13; x^(10^30);
DirichletGroup(5, GF(7)).1 * DirichletGroup(3, GF(7)).1;
Parent(DirichletGroup(5, GF(7)).1 * DirichletGroup(3, GF(7)).1);
// Comparisons over different rings.
g7 := DirichletGroup(5, GF(7)).1; q5 := DirichletGroup(5).1;
f5 := DirichletGroup(4, GF(5)).1;
g7 eq q5; q5 eq g7; k eq f5; f5 eq k; g7 ne q5;
q5 eq DirichletGroup(5, Integers()).1;
g7 eq DirichletGroup(5, GF(49)).1^2;
[x eq y : x in Elements(DirichletGroup(5, GF(7))), y in Elements(DirichletGroup(5))];
DirichletGroup(3).1 cmpeq DirichletGroup(3, GF(7)).1;
DirichletGroup(3).1 cmpeq 1;
g7 in DirichletGroup(5); q5 in DirichletGroup(5, GF(7)); q5 in DirichletGroup(10);
DirichletGroup(35, GF(13)).1 in DirichletGroup(35, GF(13));
// Kronecker characters.
KroneckerCharacter(209); Parent(KroneckerCharacter(209)); Conductor(KroneckerCharacter(209));
for D in [-4, 12, -7, 8, 1, 0, 4, -1, 18, -12, 45, -8, 5, -3] do KroneckerCharacter(D); end for;
Parent(KroneckerCharacter(4));
KroneckerCharacter(-3, GF(7)); Parent(KroneckerCharacter(-3, GF(7)));
KroneckerCharacter(5, Rationals()); Parent(KroneckerCharacter(5, Rationals()));
KroneckerCharacter(-8, GF(4));
// Decompositions and primitive characters.
Decomposition(DirichletGroup(7, GF(7)).1);
Decomposition(DirichletGroup(24).1 * DirichletGroup(24).3);
Decomposition(DirichletGroup(24).1);
Decomposition(Elements(DirichletGroup(3))[1]);
Decomposition(DirichletGroup(1).0);
H<b, c> := DirichletGroup(35, GF(13));
Decomposition(b); Decomposition(b*c);
[Parent(x) : x in Decomposition(b)];
AssociatedPrimitiveCharacter(b^2); Parent(AssociatedPrimitiveCharacter(b^2));
AssociatedPrimitiveCharacter(H!1); Parent(AssociatedPrimitiveCharacter(H!1));
Elements(Parent(AssociatedPrimitiveCharacter(b^2)));
AssociatedPrimitiveCharacter(DirichletGroup(7, GF(7)).1^3);
AssociatedPrimitiveCharacter(DirichletGroup(24).1 * DirichletGroup(24).3);
Parent(AssociatedPrimitiveCharacter(DirichletGroup(24).1 * DirichletGroup(24).3));
// Base rings.
B := BaseExtend(H, GF(13^2)); B; Elements(B)[1..5];
BaseExtend(DirichletGroup(5), GF(7)); Elements(BaseExtend(DirichletGroup(5), GF(7)));
BaseExtend(DirichletGroup(5), Integers());
BaseExtend(DirichletGroup(5), Rationals());
E := BaseExtend(H, GF(13), GF(13)!6); E; Elements(E)[1..4];
ValuesOnUnitGenerators(E.1);
BaseExtend(H, GF(13), GF(13)!3);
MinimalBaseRingCharacter(b); MinimalBaseRingCharacter(b^2);
Parent(MinimalBaseRingCharacter(b^2));
MinimalBaseRingCharacter(H!1); Parent(MinimalBaseRingCharacter(H!1));
MinimalBaseRingCharacter(DirichletGroup(5).1);
Parent(MinimalBaseRingCharacter(DirichletGroup(5).1));
GaloisConjugacyRepresentatives(DirichletGroup(24));
G := DirichletGroup(12);
GaloisConjugacyRepresentatives([G.1, G.1, G.2, G.1*G.2]);
// Square roots over the rationals: of characters of odd order, so trivial.
Sqrt(DirichletGroup(5)!1);
Sqrt(DirichletGroup(1).0);
Sqrt(DirichletGroup(35)!1);
Sqrt(DirichletGroup(8)!1);

// Separate calls give equal groups, but aggregates find no common universe
// for their elements (#89). Coercion into one of them, as by Append, still
// works.
G := DirichletGroup(12); H := DirichletGroup(12);
G eq H; G.1 eq H.1; G.1 * H.2;
[G.1, G.2];
[G.1, H.2];
[H.1, G.1, G.2];
{G.1, H.1};
[* G.1, H.1 *]; <G.1, H.1>; [G, H]; {G, H};
GaloisConjugacyRepresentatives([DirichletGroup(12).1, DirichletGroup(12).2]);
S := [G.1]; Append(~S, H.1); S; Universe(S) eq G;
S := [G.1]; S[2] := H.1; S;
[G.1] cat [H.1];
CoveringStructure(G, H);
