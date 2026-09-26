// calyx refuses lists of partitions that would hold more than 2^27
// integers (their parts, and one for each), about 2.5 GB, where Magma runs
// out of memory; Partitions(74) is the largest that fits. Partitions with
// many parts, and long searches that find none, which crash Magma 2.22, are
// fine.
#Partitions(60);
x := RestrictedPartitions(10^6, {1}); #x, #x[1];
RestrictedPartitions(10^6 + 1, {2, 4}); RestrictedPartitions(2 * 10^6 + 2, 3, {10^6, 1, 2});
Partitions(75);
Partitions(1000);
RestrictedPartitions(2^29, {1});
RestrictedPartitions(2^29, 2^29, {1});
