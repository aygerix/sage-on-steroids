SetAutoColumns(false);
n := 8;
P := PolynomialRing(GF(32003), n, "grevlex");
x := [P.i : i in [1..n]];
S := [];
for d in [1..n-1] do
    Append(~S, &+[&*[x[((i+j-2) mod n)+1] : j in [1..d]] : i in [1..n]]);
end for;
Append(~S, &*x - 1);
G := GroebnerBasis(S);
print "groebner-f4", #G, &+[#Terms(g) : g in G];
