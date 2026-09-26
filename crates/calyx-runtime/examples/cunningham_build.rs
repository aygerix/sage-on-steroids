//! Builds a data file of the Cunningham tables from lines "b n- p" or
//! "b n+ p" on standard input, each giving a prime p > 10^9 that divides
//! b^n - 1 or b^n + 1:
//!
//!     cargo run --release --example cunningham_build -- [--bases LO-HI] [--check] OUT
//!
//! The file covers the bases from LO to HI (by default all those listed).
//! With --check, the primes are checked to be probable primes.

use std::io::{self, BufWriter};

use calyx_runtime::intrinsics::factoring::cunningham;

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let usage = || -> ! {
        eprintln!("usage: cunningham_build [--bases LO-HI] [--check] OUT < factors");
        std::process::exit(2)
    };
    let (mut bases, mut check, mut out) = ((2, 1 << 30), false, None);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--check" => check = true,
            "--bases" => {
                let r = it.next().unwrap_or_else(|| usage());
                let (lo, hi) = r.split_once('-').unwrap_or_else(|| usage());
                bases = (lo.parse().unwrap_or_else(|_| usage()), hi.parse().unwrap_or_else(|_| usage()));
            }
            _ if out.is_none() && !a.starts_with("--") => out = Some(a),
            _ => usage(),
        }
    }
    let out = out.unwrap_or_else(|| usage());
    let stats = cunningham::build(io::stdin().lock(), BufWriter::new(std::fs::File::create(out)?), bases, check)?;
    println!("{} lines, {} primes of {} bases, {} bytes", stats.lines, stats.primes, stats.bases, stats.bytes);
    println!("{} repeated", stats.repeated);
    for (what, lines) in [("malformed", &stats.malformed), ("not dividing", &stats.not_dividing), ("not prime", &stats.not_prime)] {
        println!("{} {what}", lines.len());
        for l in lines.iter().take(20) {
            println!("  {l}");
        }
    }
    Ok(())
}
