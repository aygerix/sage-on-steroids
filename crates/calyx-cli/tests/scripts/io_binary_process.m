// Binary strings and one-way process pipes. Files stay in the configured
// temporary directory and the commands are harmless local utilities.
b := BinaryString([0, 65, 10, 255]);
Type(b); Parent(b); #b; Eltseq(b);
b[2]; Substring(b, 2, 2);
b cat BString("Z");
b eq BinaryString([0, 65, 10, 255]);
b lt BinaryString([1]);
Sprint(b); Sprint(b, "Magma");

fn := Sprintf("%o/calyx-io-binary-%o.bin", GetTempDir(), Getpid());
WriteBinary(fn, b : Overwrite := true);
ReadBinary(fn) eq b;
WriteBinary(fn, BinaryString("X"));
Eltseq(ReadBinary(fn));
_ := System("rm -f " cat fn);

I := POpen("printf process-output", "r");
IOType(I); Read(I); AtEof(I);
J := POpen("cat", "w");
IOType(J); Write(J, "process-input\n"); Flush(J);
delete J;
