//! Command-line environment and history integration tests.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn temp_dir(name: &str) -> PathBuf {
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = std::env::temp_dir().join(format!("calyx-{name}-{}-{stamp}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, text: &str) {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).unwrap();
    }
    std::fs::write(path, text).unwrap();
}

fn command() -> Command {
    let mut c = Command::new(env!("CARGO_BIN_EXE_calyx"));
    for name in ["CALYX_STARTUP_FILE", "CALYX_PATH", "CALYX_LIBRARY_ROOT", "CALYX_LIBRARIES", "CALYX_SYSTEM_SPEC", "CALYX_USER_SPEC", "CALYX_TEMP_DIR"] {
        c.env_remove(name);
    }
    c
}

fn run(mut c: Command, files: &[&str], input: &str) -> String {
    let mut child = c.arg("-b").args(files).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success());
    let mut text = String::from_utf8(out.stdout).unwrap();
    text.push_str(&String::from_utf8(out.stderr).unwrap());
    text
}

#[test]
fn calyx_environment_paths_and_specs() {
    let dir = temp_dir("environment");
    write(&dir.join("path/path_file.m"), "\"path-file\";\n");
    write(&dir.join("startup.m"), "startup_value := \"startup\";\n");
    write(&dir.join("root/lib/library_file.m"), "\"library-file\";\n");
    write(&dir.join("system/pkg.m"), "intrinsic SystemValue() -> MonStgElt\n{A system-spec marker}\nreturn \"system\";\nend intrinsic;\n");
    write(&dir.join("system/system.spec"), "{ pkg.m }\n");
    write(&dir.join("user/pkg.m"), "intrinsic UserValue() -> MonStgElt\n{A user-spec marker}\nreturn \"user\";\nend intrinsic;\n");
    write(&dir.join("user/user.spec"), "{ pkg.m }\n");
    let mut c = command();
    c.env("CALYX_STARTUP_FILE", dir.join("startup.m"))
        .env("CALYX_PATH", dir.join("path"))
        .env("CALYX_LIBRARY_ROOT", dir.join("root"))
        .env("CALYX_LIBRARIES", "lib")
        .env("CALYX_SYSTEM_SPEC", dir.join("system/system.spec"))
        .env("CALYX_USER_SPEC", dir.join("user/user.spec"))
        .env("CALYX_TEMP_DIR", &dir);
    // No line wrapping: temporary directories on macOS are long enough to wrap at 80 columns.
    let input = "SetColumns(0); startup_value; SystemValue(); UserValue();\nGetPath(); GetLibraryRoot(); GetLibraries(); GetTempDir();\nLoad(\"library_file.m\");\n";
    let out = run(c, &["path_file.m"], input);
    let expected = format!("path-file\nstartup\nsystem\nuser\n{}\n{}\nlib\n{}\nlibrary-file\n", dir.join("path").display(), dir.join("root").display(), dir.display());
    assert_eq!(out, expected);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn history_edit_reenters_changed_text() {
    let dir = temp_dir("history-edit");
    let editor = dir.join("editor.sh");
    write(&editor, "#!/bin/sh\nprintf '2;' > \"$1\"\n");
    #[cfg(unix)] {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&editor, std::fs::Permissions::from_mode(0o700)).unwrap();
    }
    let mut c = command();
    c.env("EDITOR", &editor).env("CALYX_TEMP_DIR", &dir);
    let out = run(c, &[], "1;\n%e\n%p\n");
    assert_eq!(out, "1\n>> 2;\n2\n/*  1 */   1;\n/*  2 */   2;\n");
    std::fs::remove_dir_all(dir).unwrap();
}
