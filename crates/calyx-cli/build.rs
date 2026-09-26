use std::env;
use std::process::Command;

fn pkg_config_variable(name: &str) -> Option<String> {
    let pkg_config = env::var_os("PKG_CONFIG").unwrap_or_else(|| "pkg-config".into());
    let output = Command::new(pkg_config).args(["--variable", name, "flint"]).output().ok()?;
    let value = String::from_utf8(output.stdout).ok()?;
    (output.status.success() && !value.trim().is_empty()).then(|| value.trim().to_string())
}

fn metadata(env_name: &str, pkg_name: &str) -> String {
    env::var(env_name).ok().filter(|s| !s.is_empty()).or_else(|| pkg_config_variable(pkg_name)).unwrap_or_else(|| "not recorded".into())
}

fn main() {
    println!("cargo::rerun-if-env-changed=CALYX_FLINT_CFLAGS");
    println!("cargo::rerun-if-env-changed=CALYX_FLINT_BLAS");
    println!("cargo::rerun-if-env-changed=PKG_CONFIG");
    println!("cargo::rerun-if-env-changed=PKG_CONFIG_PATH");
    println!("cargo::rerun-if-env-changed=PKG_CONFIG_LIBDIR");
    println!("cargo::rerun-if-env-changed=PKG_CONFIG_SYSROOT_DIR");
    if let Some(dir) = pkg_config_variable("pcfiledir") {
        println!("cargo::rerun-if-changed={dir}/flint.pc");
    }
    println!("cargo::rustc-env=CALYX_BUILD_TARGET={}", env::var("TARGET").unwrap());
    println!("cargo::rustc-env=CALYX_FLINT_CFLAGS={}", metadata("CALYX_FLINT_CFLAGS", "calyx_cflags"));
    println!("cargo::rustc-env=CALYX_FLINT_BLAS={}", metadata("CALYX_FLINT_BLAS", "calyx_blas"));
}
