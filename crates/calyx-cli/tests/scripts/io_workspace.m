// Workspaces use calyx's own versioned format, not Magma's workspace format.
fn := Tempname("/tmp/calyx_workspace_test_");
bad := Tempname("/tmp/calyx_workspace_bad_");
a := 123;
s := [1, 2, 3];
R := RealField(20);
A := Matrix(R, 2, 2, [1/3, 2, -4, 5/7]);
save fn;
a := -1;
s := [];
later := "discard me";
restore fn;
a;
s;
A;
assigned later;
Parent(A) eq MatrixRing(R, 2);

// A failed restore validates before replacing any current globals.
WriteBinary(bad, BinaryString([1, 2, 3]) : Overwrite := true);
try
    restore bad;
catch e
    print "bad restore";
end try;
a;
