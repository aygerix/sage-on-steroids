const TARGET: &str = env!("CALYX_BUILD_TARGET");
const FLINT_CFLAGS: &str = env!("CALYX_FLINT_CFLAGS");
const FLINT_BLAS: &str = env!("CALYX_FLINT_BLAS");
const FLINT_AVX2_CFLAGS: Option<&str> = option_env!("CALYX_FLINT_AVX2_CFLAGS");

fn flint_cflags() -> &'static str {
    let avx2 = calyx_flint::library_path().map(|p| p.components().any(|part| part.as_os_str() == "x86-64-v3")).unwrap_or(false);
    if avx2 { FLINT_AVX2_CFLAGS.unwrap_or(FLINT_CFLAGS) } else { FLINT_CFLAGS }
}

fn cpu_dispatch() -> String {
    let mut features = Vec::new();
    #[cfg(target_arch = "x86_64")]
    {
        if std::arch::is_x86_feature_detected!("avx2") {
            features.push("AVX2");
        }
        if std::arch::is_x86_feature_detected!("pclmulqdq") {
            features.push("PCLMULQDQ");
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        features.push("NEON");
        if std::arch::is_aarch64_feature_detected!("aes") {
            features.push("PMULL");
        }
    }
    if features.is_empty() { "portable".into() } else { features.join(", ") }
}

pub fn verbose(version: &str) -> String {
    use calyx_runtime::intrinsics::factoring::cunningham;
    let cunningham = match (cunningham::data_file(), cunningham::data_bases()) {
        (Some(p), Some((lo, hi))) => format!("{} (bases {lo} to {hi})", p.display()),
        _ => "not found".into(),
    };
    format!(
        "calyx {version}\nBuild target: {TARGET}\nFLINT: {}\nFLINT CFLAGS: {}\nBLAS: {FLINT_BLAS}\nCPU dispatch: {}\nCunningham tables: {cunningham}",
        calyx_flint::version(), flint_cflags(), cpu_dispatch()
    )
}
