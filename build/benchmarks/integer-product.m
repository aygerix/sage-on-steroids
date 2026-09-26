SetAutoColumns(false);
a := 10^2000000 + 123456789;
b := 10^2000000 - 987654321;
c := a * b;
print "integer-product", c mod 1000003;
