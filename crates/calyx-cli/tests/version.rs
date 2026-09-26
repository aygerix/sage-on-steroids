use std::process::Command;

#[test]
fn version_is_short_unless_verbose() {
    let short = Command::new(env!("CARGO_BIN_EXE_calyx")).arg("--version").output().unwrap();
    assert!(short.status.success());
    let short = String::from_utf8(short.stdout).unwrap();
    assert!(short.starts_with("calyx "));
    assert_eq!(short.lines().count(), 1);

    let verbose = Command::new(env!("CARGO_BIN_EXE_calyx")).args(["--version", "--verbose"]).output().unwrap();
    assert!(verbose.status.success());
    let verbose = String::from_utf8(verbose.stdout).unwrap();
    for label in ["Build target:", "FLINT:", "FLINT CFLAGS:", "BLAS:", "CPU dispatch:", "Cunningham tables:"] {
        assert!(verbose.contains(label), "missing {label:?} in:\n{verbose}");
    }
}
