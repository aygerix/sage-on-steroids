// Cunningham numbers b^k - 1 and b^k + 1 with large k, where the tables of
// known factors matter, and Factorization of such numbers, which looks them
// up too (text/185). The bases below 100 are in the small table that comes
// with calyx; the larger bases have k small enough to factor without it.
Cunningham(2, 1001, -1);
Cunningham(2, 1001, 1);
Cunningham(3, 500, 1);
Cunningham(13, 200, -1);
Cunningham(97, 100, -1);
// Aurifeuillian factors: 2^(2m) + 1, 3^(3m) + 1, 5^(5m) - 1, 6^(6m) + 1,
// 7^(7m) + 1, 10^(10m) + 1, 11^(11m) + 1, 12^(3m) + 1 and 99^(11m) + 1 for
// odd m.
Cunningham(2, 1150, 1);
Cunningham(3, 999, 1);
Cunningham(5, 875, -1);
Cunningham(6, 546, 1);
Cunningham(7, 497, 1);
Cunningham(10, 450, 1);
Cunningham(11, 385, 1);
Cunningham(12, 399, 1);
Cunningham(99, 55, 1);
// Powers as bases.
Cunningham(4, 250, 1);
Cunningham(8, 350, -1);
Cunningham(10000, 5, 1);
// Many cyclotomic factors.
procedure Check(b, k, c)
    f := Cunningham(b, k, c);
    #f, &*[p[1]^p[2] : p in f] eq b^k + c, [#Sprint(p[1]) : p in f];
end procedure;
Check(2, 1200, 1);
Check(2, 1680, -1);
Check(2, 2310, -1);
Check(3, 1050, -1);
Check(2, 3960, -1);
Check(2, 4620, -1);
Check(10, 1260, -1);
// Larger bases.
Cunningham(1001, 20, 1);
Cunningham(9999, 12, -1);
Cunningham(1000, 30, -1);
Cunningham(1073741823, 3, 1);
// Factorization finds b^k - 1 and b^k + 1 in the tables, and proves the
// primes unless told not to.
Factorization(2^1001 - 1);
f, s := Factorization(-(10^450 + 1)); #f, s, &*[p[1]^p[2] : p in f] eq 10^450 + 1;
Factorization(2^1150 + 1 : Proof := false);
Factorization(2^1001 + 1 : Proof := false) eq Cunningham(2, 1001, 1);
Factorization(3^500 + 1 : Proof := false) eq Cunningham(3, 500, 1);
f, s, r := Factorization(2^1001 - 1 : ECMLimit := 0, MPQSLimit := 0); #f, assigned r;
// IsPower and IsPrimePower give the smallest base.
IsPower(2^1001); IsPower(6^1001); IsPower(3^2310); IsPower(2^143);
IsPrimePower(2^1001); IsPrimePower(6^1001); IsPrimePower(3^2310);
