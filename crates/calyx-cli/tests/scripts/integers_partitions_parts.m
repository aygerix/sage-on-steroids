// A copy of compat/pending/integers_partitions_parts.m, so that calyx's output, checked
// against Magma 2.22, is kept until #24 records the output of 2.29.
// Partitions of n into k parts (both small and non-negative), in the order
// of Partitions(n).
Partitions(10, 3);
Partitions(5, 1); Partitions(5, 5); Partitions(5, 6); Partitions(5, 0); Partitions(0, 0); Partitions(0, 1);
#Partitions(60, 12); #Partitions(100, 3); #Partitions(10^5, 2); [p : p in Partitions(20) | #p eq 4] eq [p : p in Partitions(20, 4)];
// The lists of partitions lie in the power structure of sequences, which a
// sequence of integer sequences does not compare with.
Universe(Partitions(20, 4)); Universe(Partitions(5)); Universe(RestrictedPartitions(5, {1})); Universe([p : p in Partitions(5)]);
Partitions(20, 4) eq Partitions(20)[1..#Partitions(20, 4)];
[p : p in Partitions(5)] eq Partitions(5);
x := Partitions(10^4, 2); #x, x[1], x[#x];
x := Partitions(10^4, 10^4); #x, #x[1];
Partitions(10, 2^30 - 1);
Partitions(-1, 2);
Partitions(5, -1);
Partitions(-1, -1);
Partitions(2^30, 2);
Partitions(10, 2^30);
Partitions(10, 2^62);
Partitions(2^64, 2);
Partitions(5, 2 : Foo := 1);
Partitions(5/1, 2);
