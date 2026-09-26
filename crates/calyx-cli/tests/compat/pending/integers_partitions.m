// Partitions of small integers only (at most 2^30 - 1), the number of parts
// (small and non-negative), and partitions with very many parts.
#Partitions(40); Partitions(6)[3]; #RestrictedPartitions(100, {3, 5, 7}); RestrictedPartitions(20, 3, {2, 5, 7, 11});
x := RestrictedPartitions(10^5, {1}); #x, #x[1], x[1][10^5];
RestrictedPartitions(10^4 + 1, {2, 4}); RestrictedPartitions(99, {6, 10, 15}); #RestrictedPartitions(1000, 3, {1, 2, 3, 4, 5});
RestrictedPartitions(10, 2^29, {1}); RestrictedPartitions(0, 0, {1}); RestrictedPartitions(10, 3, {}); RestrictedPartitions(10, {});
Partitions(2^30);
Partitions(2^64);
RestrictedPartitions(2^62, {2^20});
RestrictedPartitions(2^30 + 3, {2^29 + 1});
RestrictedPartitions(10, 2^30, {1});
RestrictedPartitions(10, -1, {1});
RestrictedPartitions(10, {2^30});
