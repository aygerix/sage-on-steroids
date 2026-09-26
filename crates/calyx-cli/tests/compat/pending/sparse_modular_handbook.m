// Handbook H28E3, with its progress printing omitted.
function Sieve(K, qlimit, climit, ratio)
    p := #K;
    Z := Integers();
    H := Iroot(p, 2) + 1;
    J := H^2 - p;
    fb_primes := [q: q in [2 .. qlimit] | IsPrime(q)];
    a := rep{x: x in [2..qlimit] | IsPrime(x) and IsPrimitive(K!x)};
    SetPrimitiveElement(K,K!a);
    FB := {@ Z!a @};
    for x in fb_primes do
        Include(~FB, x);
    end for;
    A := SparseMatrix();
    log2 := Log(2.0);
    logqs := [Log(q)/log2: q in fb_primes];
    for c1 in [1 .. climit] do
        if Nrows(A)/#FB ge ratio then break; end if;
        sieve := [z: i in [1 .. climit]] where z := Log(1.0);
        den := H + c1;
        num := -(J + c1*H);
        for i := 1 to #fb_primes do
            q := fb_primes[i];
            logq := logqs[i];
            qpow := q;
            while qpow le qlimit do
                if den mod qpow eq 0 then break; end if;
                c2 := num * Modinv(den, qpow) mod qpow;
                if c2 eq 0 then c2 := qpow; end if;
                nextqpow := qpow*q;
                while c2 lt c1 do
                    c2 +:= qpow;
                end while;
                while c2 le #sieve do
                    sieve[c2] +:= logq;
                    if nextqpow gt qlimit then
                        prod := (J + (c1 + c2)*H + c1*c2) mod p;
                        nextp := nextqpow;
                        while prod mod nextp eq 0 do
                            sieve[c2] +:= logq;
                            nextp *:= q;
                        end while;
                    end if;
                    c2 +:= qpow;
                end while;
                qpow := nextqpow;
            end while;
        end for;
        rel := den * (H + 1);
        relinc := H + c1;
        for c2 in [1 .. #sieve] do
            n := rel mod p;
            if Abs(sieve[c2] - Ilog2(n)) lt 1 then
                fact, r := TrialDivision(n, qlimit);
                if r eq 1 then
                    Include(~FB, H + c1);
                    Include(~FB, H + c2);
                    row := Nrows(A) + 1;
                    for t in fact do
                        SetEntry(~A, row, Index(FB, t[1]), t[2]);
                    end for;
                    if c1 eq c2 then
                        SetEntry(~A, row, Index(FB, H + c1), -2);
                    else
                        SetEntry(~A, row, Index(FB, H + c1), -1);
                        SetEntry(~A, row, Index(FB, H + c2), -1);
                    end if;
                end if;
            end if;
            rel +:= relinc;
        end for;
    end for;
    return A, FB;
end function;

K := GF(103);
A, F := Sieve(K, 35, 27, 1.1);
Nrows(A); Ncols(A); #F;
A[1]; A[2]; A[30];
v := ModularSolution(A, #K - 1);
v[1];
Matrix(Integers(#K - 1), 1, Ncols(A), Eltseq(v)) * Transpose(Matrix(ChangeRing(A, Integers(#K - 1))));
