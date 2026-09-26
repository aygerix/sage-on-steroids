// Shifts are small (below 2^30 in absolute value, whatever the number
// shifted) and non-negative; the bitwise operations on large and negative
// integers.
ShiftLeft(0, 2^30 - 1); Ilog2(ShiftLeft(1, 2^30 - 1)); ShiftLeft(-3, 5);
ShiftRight(2^100, 2^30 - 1); ShiftRight(-2^100, 2^30 - 1); ShiftRight(-5, 1); ShiftRight(-3, 0);
ModByPowerOf2(5, 2^30 - 1); Ilog2(ModByPowerOf2(-5, 2^30 - 1)); ModByPowerOf2(-5, 3); ModByPowerOf2(-3, 0); ModByPowerOf2(2^100 + 7, 100);
ShiftLeft(0, 2^30);
ShiftLeft(1, 2^30);
ShiftLeft(0, 2^62);
ShiftLeft(0, 2^64);
ShiftLeft(0, -2^64);
ShiftLeft(0, -2^30);
ShiftLeft(5, -1);
ShiftLeft(0, -2^30 + 1);
ShiftRight(0, 2^30);
ShiftRight(-1, 2^30);
ShiftRight(0, 2^64);
ShiftRight(40, -3);
ModByPowerOf2(0, 2^30);
ModByPowerOf2(5, 2^64);
ModByPowerOf2(5, -1);
BitwiseAnd(2^100 + 5, 7); BitwiseOr(-2^100, 1); BitwiseXor(-5, 2^70); BitwiseNot(2^80); BitwiseAnd(-1, -2^200);
Ilog2(BitwiseXor(2^(2^20), 1)); BitwiseAnd(-2^65 - 3, 2^66 - 1); BitwiseOr(0, 0); BitwiseNot(-1); BitwiseNot(0);
