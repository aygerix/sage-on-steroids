// Object files use calyx's own versioned format, not Magma's object format.
fn := Tempname("/tmp/calyx_object_test_");
R := RealField(20); C<i> := ComplexField(20);
x := <123, -7/9, true, "hé", BinaryString([0, 255]), [1, 2, 3], {4, 5}, R!5/8, C![2, -3], Infinity()>;
A := Matrix(R, 2, 2, [1/3, 2, -4, 5/7]);
F := Open(fn, "w");
WriteObject(F, x);
WriteObject(F, A);
WriteObjectCheck(F, func<t | t>);
delete F;
F := Open(fn, "r");
y := ReadObject(F);
B := ReadObject(F);
x eq y;
A eq B;
Parent(y[8]) eq R;
Parent(y[9]) eq C;
ok, z := ReadObjectCheck(F);
ok;
delete F;

// Asynchronous object I/O is framed, and all socket waits are bounded.
server := Socket(: LocalHost := "127.0.0.1", LocalPort := 0);
loc, _ := SocketInformation(server);
client := Socket("127.0.0.1", loc[2]);
_ := WaitForIO([server] : TimeLimit := 1000);
peer := WaitForConnection(server);
AsyncWriteObject(client, x);
AsyncWriteObject(client, A);
_, ready := WaitForIO([], [client] : TimeLimit := 1000);
#ready;
AsyncReadObject(peer);
ready := WaitForIO([peer] : TimeLimit := 1000);
#ready;
ReadObject(peer) eq x;
AsyncReadObject(peer);
ready := WaitForIO([peer] : TimeLimit := 1000);
#ready;
ReadObject(peer) eq A;

// Malformed calyx frames fail without allocating from untrusted lengths or
// recursing without a bound.
magic := [67, 65, 76, 89, 88, 79, 66, 74];
function Frame(payload)
    n := #payload;
    return BinaryString(magic cat [1, 0] cat [ (n div 256^i) mod 256 : i in [0..7] ] cat payload);
end function;
procedure Reject(data)
    name := Tempname("/tmp/calyx_bad_object_");
    WriteBinary(name, data : Overwrite := true);
    input := Open(name, "r");
    ok, _ := ReadObjectCheck(input);
    ok;
end procedure;
Reject(BinaryString(magic));
Reject(BinaryString(magic cat [1, 0, 1, 0, 0, 16, 0, 0, 0, 0]));
nested := [0];
for k := 1 to 130 do
    nested := [9, 0, 1, 0, 0, 0, 0, 0, 0, 0] cat nested;
end for;
Reject(Frame(nested));
Reject(Frame([22, 16, 0] cat [0, 0, 0, 0, 0, 0, 0, 128] cat [0, 0, 0, 0, 0, 0, 0, 128]));
Reject(Frame([18, 0, 0, 0, 0, 0, 0, 0, 128]));
Reject(Frame([9, 1, 16, 1, 0, 0, 0, 0, 0, 0, 0, 7, 1, 0, 0, 0, 0, 0, 0, 0, 120]));
