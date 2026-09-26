//! The tables of known factors of b^n - 1 and b^n + 1 (the Cunningham
//! project's tables and their extension to all bases below 10000), and the
//! factorization of such numbers with them.
//!
//! The tables are a data file, read on first use and never embedded in the
//! binary. It lists, for each base b, the known primes p > 10^9 that divide
//! the cyclotomic values Phi_d(b), keyed by d, the order of b mod p. Such a
//! prime is 1 mod d, and odd, so it is stored as (p - 1)/lcm(d, 2). The layout,
//! with every u32 little-endian:
//!
//! - the magic bytes `calyxCUN`;
//! - a u32: the version of the layout, 1;
//! - two u32: the smallest base the file covers, and one more than the
//!   largest;
//! - a u32: the number of primes;
//! - a u32 for each base from 0 to the largest covered and one more: where
//!   the base's block starts, counted from the end of this directory;
//! - the blocks: for each prime, sorted by d and then p, d less the previous
//!   prime's d (0 for the first), then (p - 1)/lcm(d, 2).
//!
//! Numbers are LEB128 varints: 7 bits a byte, least significant first, with
//! the top bit set on every byte but the last.
//!
//! There are two data files: `cunningham.bin` with all the bases below 10000,
//! and `cunningham-small.bin` with the bases below 100. The first one found
//! is used, looking for the full file and then the small one in the
//! directory `$CALYX_DATA`, in `share/calyx` next to the directory of the
//! calyx binary, and in `data/cunningham` in the source tree. Without them,
//! or for bases a file doesn't cover, the factors are found by computation
//! alone, with the same results.

use std::collections::{BTreeMap, HashMap};
use std::fs::File;
use std::io::{self, BufRead, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use calyx_flint::Integer;

const MAGIC: &[u8; 8] = b"calyxCUN";
const VERSION: u32 = 1;
const HEADER: u64 = 24;
const FILE_NAMES: [&str; 2] = ["cunningham.bin", "cunningham-small.bin"];

/// lcm(d, 2), which divides p - 1 for the odd primes p of order d.
fn lcm2(d: u64) -> u64 {
    if d % 2 == 0 { d } else { 2 * d }
}

// ----- Varints ---------------------------------------------------------------------------------------------

fn put_u64(out: &mut Vec<u8>, mut x: u64) {
    while x >= 0x80 {
        out.push(x as u8 | 0x80);
        x >>= 7;
    }
    out.push(x as u8);
}

fn put_int(out: &mut Vec<u8>, v: &Integer) {
    if let Some(x) = v.to_u64() {
        return put_u64(out, x);
    }
    let limbs = v.to_limbs();
    let bits = v.bits();
    let mut i = 0;
    while i < bits {
        let (w, o) = ((i / 64) as usize, i % 64);
        let mut x = limbs[w] >> o;
        if o > 57 && w + 1 < limbs.len() {
            x |= limbs[w + 1] << (64 - o);
        }
        i += 7;
        out.push(x as u8 & 0x7f | if i < bits { 0x80 } else { 0 });
    }
}

fn get_u64(buf: &[u8], pos: &mut usize) -> Option<u64> {
    let mut x = 0u64;
    for shift in (0..64).step_by(7) {
        let b = *buf.get(*pos)?;
        *pos += 1;
        x |= ((b & 0x7f) as u64) << shift;
        if b < 0x80 {
            return Some(x);
        }
    }
    None
}

fn get_int(buf: &[u8], pos: &mut usize) -> Option<Integer> {
    let len = buf.get(*pos..)?.iter().position(|&b| b < 0x80)? + 1;
    if len <= 9 {
        return get_u64(buf, pos).map(Integer::from_u64);
    }
    let mut limbs = vec![0u64; (len * 7).div_ceil(64)];
    for (k, &b) in buf[*pos..*pos + len].iter().enumerate() {
        let (i, x) = (k * 7, (b & 0x7f) as u64);
        limbs[i / 64] |= x << (i % 64);
        if i % 64 > 57 {
            limbs[i / 64 + 1] |= x >> (64 - i % 64);
        }
    }
    *pos += len;
    Some(Integer::from_limbs(&limbs, false))
}

/// Skips a varint.
fn skip(buf: &[u8], pos: &mut usize) -> Option<()> {
    *pos += buf.get(*pos..)?.iter().position(|&b| b < 0x80)? + 1;
    Some(())
}

// ----- Reading ---------------------------------------------------------------------------------------------

/// The data file, opened on first use.
pub struct Table {
    path: PathBuf,
    /// The bases covered: from the first to one before the second.
    bases: (u32, u32),
    file: Mutex<File>,
    /// Where the blocks start in the file.
    start: u64,
    /// The offsets of the bases' blocks from `start`.
    dir: Vec<u32>,
    /// The blocks read so far.
    blocks: Mutex<HashMap<u32, Arc<[u8]>>>,
}

/// The tables in use, or None when no data file is found or readable.
pub fn table() -> Option<&'static Table> {
    static TABLE: OnceLock<Option<Table>> = OnceLock::new();
    TABLE
        .get_or_init(|| {
            let mut dirs = Vec::new();
            if let Some(d) = std::env::var_os("CALYX_DATA") {
                dirs.push(PathBuf::from(d));
            }
            if let Some(bin) = std::env::current_exe().ok().and_then(|e| e.parent().map(Path::to_path_buf)) {
                dirs.push(bin.join("../share/calyx"));
            }
            dirs.push(PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/cunningham")));
            FILE_NAMES.iter().flat_map(|f| dirs.iter().map(move |d| d.join(f))).find_map(|f| Table::open(&f).ok())
        })
        .as_ref()
}

/// The path of the data file in use, if any.
pub fn data_file() -> Option<PathBuf> {
    table().map(|t| t.path.clone())
}

/// The smallest and largest bases the data file in use covers.
pub fn data_bases() -> Option<(u64, u64)> {
    table().map(|t| (t.bases.0 as u64, t.bases.1 as u64 - 1))
}

impl Table {
    pub fn open(path: &Path) -> io::Result<Table> {
        let bad = || io::Error::new(io::ErrorKind::InvalidData, "not a Cunningham data file");
        let mut file = File::open(path)?;
        let mut head = [0u8; HEADER as usize];
        file.read_exact(&mut head)?;
        let word = |i: usize| u32::from_le_bytes(head[i..i + 4].try_into().unwrap());
        let (first, end) = (word(12), word(16));
        if &head[..8] != MAGIC || word(8) != VERSION || first > end || end > 1 << 30 {
            return Err(bad());
        }
        let mut raw = vec![0u8; 4 * (end as usize + 1)];
        file.read_exact(&mut raw)?;
        let dir: Vec<u32> = raw.chunks_exact(4).map(|c| u32::from_le_bytes(c.try_into().unwrap())).collect();
        if dir.windows(2).any(|w| w[0] > w[1]) {
            return Err(bad());
        }
        let start = HEADER + raw.len() as u64;
        let blocks = Mutex::new(HashMap::new());
        let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
        Ok(Table { path, bases: (first, end), file: Mutex::new(file), start, dir, blocks })
    }

    /// The block of base b, read once.
    fn block(&self, b: u64) -> Option<Arc<[u8]>> {
        let b = u32::try_from(b).ok().filter(|&b| (b as usize) + 1 < self.dir.len())?;
        if let Some(blk) = self.blocks.lock().ok()?.get(&b) {
            return Some(blk.clone());
        }
        let (lo, hi) = (self.dir[b as usize], self.dir[b as usize + 1]);
        let mut buf = vec![0u8; (hi - lo) as usize];
        if lo < hi {
            let mut f = self.file.lock().ok()?;
            f.seek(SeekFrom::Start(self.start + lo as u64)).ok()?;
            f.read_exact(&mut buf).ok()?;
        }
        let blk: Arc<[u8]> = buf.into();
        self.blocks.lock().ok()?.insert(b, blk.clone());
        Some(blk)
    }

    /// The known primes above 10^9 that divide Phi_d(b), for each d in ds.
    pub fn lookup(&self, b: u64, ds: &[u64]) -> Vec<Vec<Integer>> {
        let mut out = vec![Vec::new(); ds.len()];
        let Some(blk) = self.block(b) else { return out };
        let (mut pos, mut d) = (0, 0u64);
        while pos < blk.len() {
            let Some(dd) = get_u64(&blk, &mut pos) else { break };
            d += dd;
            match ds.iter().position(|&e| e == d) {
                Some(i) => {
                    let Some(v) = get_int(&blk, &mut pos) else { break };
                    out[i].push(&(&v * lcm2(d) as i64) + &Integer::one());
                }
                None if skip(&blk, &mut pos).is_none() => break,
                None => {}
            }
        }
        out
    }
}

// ----- Building --------------------------------------------------------------------------------------------

/// What `build` found in its input.
#[derive(Debug, Default)]
pub struct BuildStats {
    /// The lines read.
    pub lines: u64,
    /// The primes written.
    pub primes: u64,
    /// The bases with primes.
    pub bases: u64,
    /// The lines whose number is not divisible by its factor.
    pub not_dividing: Vec<String>,
    /// The lines whose factor is not a probable prime (when checked).
    pub not_prime: Vec<String>,
    /// The lines that repeat a prime of the same base.
    pub repeated: u64,
    /// The lines not of the form "b n- p" or "b n+ p".
    pub malformed: Vec<String>,
    /// The size of the file written.
    pub bytes: u64,
}

fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    ((a as u128 * b as u128) % m as u128) as u64
}

fn powmod(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1 % m;
    b %= m;
    while e > 0 {
        if e & 1 == 1 {
            r = mulmod(r, b, m);
        }
        b = mulmod(b, b, m);
        e >>= 1;
    }
    r
}

/// The distinct primes dividing n, which must be small.
fn prime_divisors(n: u64) -> Vec<u64> {
    factor_small(n).into_iter().map(|(q, _)| q).collect()
}

/// The order of b mod p, given that it divides n; None if it doesn't.
fn order(b: u64, n: u64, p: &Integer) -> Option<u64> {
    let one = |e: u64| match p.to_u64() {
        Some(q) => powmod(b, e, q) == 1,
        None => Integer::from_u64(b).powm(&Integer::from_u64(e), p).is_some_and(|x| x.is_one()),
    };
    if !one(n) {
        return None;
    }
    let mut d = n;
    for q in prime_divisors(n) {
        while d % q == 0 && one(d / q) {
            d /= q;
        }
    }
    Some(d)
}

/// Writes the data file for the bases from lo to hi of the factors listed in
/// `input`, a line "b n- p" or "b n+ p" for each prime p > 10^9 dividing
/// b^n - 1 or b^n + 1. The primes are checked to be probable primes when
/// `check` is set.
pub fn build(input: impl BufRead, mut out: impl Write, (lo, hi): (u32, u32), check: bool) -> io::Result<BuildStats> {
    let mut stats = BuildStats::default();
    let mut bases: BTreeMap<u32, Vec<(u32, Integer)>> = BTreeMap::new();
    for line in input.lines() {
        let line = line?;
        stats.lines += 1;
        let parsed = (|| {
            let mut w = line.split_whitespace();
            let b: u32 = w.next()?.parse().ok()?;
            let e = w.next()?;
            let (n, plus) = match e.strip_suffix('+') {
                Some(n) => (n, true),
                None => (e.strip_suffix('-')?, false),
            };
            let n: u32 = n.parse().ok()?;
            let p = Integer::parse(w.next()?)?;
            (w.next().is_none() && b >= 2 && n >= 1 && p > Integer::from_u64(1_000_000_000))
                .then_some((b, n as u64 * if plus { 2 } else { 1 }, p))
        })();
        let Some((b, n, p)) = parsed else {
            stats.malformed.push(line);
            continue;
        };
        if b < lo || b > hi {
            continue;
        }
        let Some(d) = order(b as u64, n, &p) else {
            stats.not_dividing.push(line);
            continue;
        };
        if check && !p.is_probable_prime() {
            stats.not_prime.push(line);
            continue;
        }
        bases.entry(b).or_default().push((d as u32, p));
    }
    let top = hi.min(bases.keys().next_back().map_or(lo, |&b| b)) + 1;
    let mut dir = Vec::with_capacity(top as usize + 1);
    let mut blocks = Vec::new();
    for b in 0..top {
        dir.push(blocks.len() as u32);
        let Some(ps) = bases.get_mut(&b) else { continue };
        ps.sort();
        let before = ps.len();
        ps.dedup_by(|x, y| x.1 == y.1);
        stats.repeated += (before - ps.len()) as u64;
        stats.primes += ps.len() as u64;
        stats.bases += 1;
        let mut prev = 0;
        for (d, p) in ps.iter() {
            put_u64(&mut blocks, (d - prev) as u64);
            prev = *d;
            put_int(&mut blocks, &(p - &Integer::one()).divexact(&Integer::from_u64(lcm2(*d as u64))));
        }
        if blocks.len() > u32::MAX as usize {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "the tables are too large"));
        }
    }
    dir.push(blocks.len() as u32);
    out.write_all(MAGIC)?;
    for w in [VERSION, lo, top, stats.primes as u32].into_iter().chain(dir.iter().copied()) {
        out.write_all(&w.to_le_bytes())?;
    }
    out.write_all(&blocks)?;
    out.flush()?;
    stats.bytes = HEADER + 4 * dir.len() as u64 + blocks.len() as u64;
    Ok(stats)
}

// ----- Factoring -------------------------------------------------------------------------------------------

/// The factorization of n by trial division; n must be small.
fn factor_small(mut n: u64) -> Vec<(u64, u32)> {
    let mut out = Vec::new();
    let mut q = 2;
    while q * q <= n {
        let mut e = 0;
        while n % q == 0 {
            n /= q;
            e += 1;
        }
        if e > 0 {
            out.push((q, e));
        }
        q += 1;
    }
    if n > 1 {
        out.push((n, 1));
    }
    out
}

fn divisors(n: u64) -> Vec<u64> {
    let mut out = vec![1];
    for (q, e) in factor_small(n) {
        let len = out.len();
        let mut qk = 1;
        for _ in 0..e {
            qk *= q;
            for i in 0..len {
                out.push(out[i] * qk);
            }
        }
    }
    out.sort();
    out
}

/// Phi_d(a), the d-th cyclotomic polynomial at a: with r the product of the
/// primes dividing d, it is Phi_r(a^(d/r)), the product of (x^e - 1)^mu(r/e)
/// over the e dividing r.
pub fn cyclotomic_value(d: u64, a: &Integer) -> Integer {
    let qs = prime_divisors(d);
    let r: u64 = qs.iter().product();
    let x = a.pow(d / r);
    let (mut num, mut den) = (Integer::one(), Integer::one());
    for mask in 0..1u32 << qs.len() {
        // e = r divided by the primes in the mask, whose number is the sign.
        let e = qs.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 0).map(|(_, q)| q).product::<u64>();
        let t = &x.pow(e) - &Integer::one();
        if mask.count_ones() % 2 == 0 {
            num = &num * &t;
        } else {
            den = &den * &t;
        }
    }
    num.divexact(&den)
}

/// The primes below 10^9 that divide v, a divisor of Phi_d(a) prime to d,
/// for d with lcm(d, 2) at least 64. Such primes are 1 mod lcm(d, 2), so
/// the candidates are sieved by the small primes and tested for a^d = 1.
fn small_primes(a: &Integer, d: u64, v: &Integer) -> Vec<u64> {
    const TOP: u64 = 1_000_000_000;
    const SEG: u64 = 1 << 15;
    let m = lcm2(d);
    let sieve: Vec<(u64, u64)> = (3..1000u64)
        .filter(|&q| m % q != 0 && prime_divisors(q) == [q])
        .map(|q| {
            // m j + 1 = 0 mod q for j = -1/m mod q.
            let inv = powmod(m % q, q - 2, q);
            (q, (q - inv) % q)
        })
        .collect();
    let mut out = Vec::new();
    let jmax = (TOP - 1) / m;
    let mut composite = vec![false; SEG as usize];
    let mut lo = 1;
    while lo <= jmax {
        let hi = (lo + SEG - 1).min(jmax);
        composite.fill(false);
        for &(q, j0) in &sieve {
            // The first j >= lo with j = j0 mod q, keeping the candidate q itself.
            let mut j = lo + (j0 + q - lo % q) % q;
            if m * j + 1 == q {
                j += q;
            }
            while j <= hi {
                composite[(j - lo) as usize] = true;
                j += q;
            }
        }
        for j in lo..=hi {
            if !composite[(j - lo) as usize] {
                let p = m * j + 1;
                if powmod32(a.mod_u64(p), d, p) == 1 && v.mod_u64(p) == 0 {
                    out.push(p);
                }
            }
        }
        lo = hi + 1;
    }
    out
}

/// b^e mod m for m < 2^32.
fn powmod32(mut b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % m;
        }
        b = b * b % m;
        e >>= 1;
    }
    r
}

fn mod_mul(x: &Integer, y: &Integer, c: &Integer) -> Integer {
    (x * y).fdiv_qr(c).unwrap().1
}

/// A proper divisor of c that separates its primes in the Aurifeuillian
/// factors L and M of Phi_d(a), if Phi_d(a) has them, and c has primes in
/// both. c must divide Phi_d(a) and be prime to d.
///
/// With a = s t^2 and s squarefree, Phi_d(a) = L M when s = 1 mod 4 and d is
/// an odd multiple of s, or s = 2 or 3 mod 4 and d is an odd multiple of 2s.
/// The primes p of L are told from those of M by where a Gauss sum for the
/// quadratic character of discriminant D = s, -s or 4s lands mod p, once a
/// primitive root of unity of order d (or 2d) mod p is fixed. The powers of a
/// mod p are such roots, so the sums are computed mod c, and the gcd with c
/// gathers the primes of one factor.
fn aurifeuillian(a: &Integer, d: u64, c: &Integer) -> Option<Integer> {
    if c.bits() < 2 {
        return None;
    }
    // s is the squarefree divisor of d with a/s a square.
    let qs = prime_divisors(d);
    let (s, t) = (1..1u32 << qs.len()).find_map(|mask| {
        let s: u64 = qs.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 1).map(|(_, q)| q).product();
        let (q, r) = a.tdiv_qr(&Integer::from_u64(s))?;
        let t = q.isqrt()?;
        (r.is_zero() && &t * &t == q).then_some((s, t))
    })?;
    let int = |x: i64| Integer::from_i64(x);
    let big_s = int(s as i64);
    let z = match s % 4 {
        // D = s and x = a, or for s = 3 mod 4, D = -s and x = -a with d/2 in
        // place of d, as Phi_d(a) = Phi_(d/2)(-a). Then p is in L when
        // t (sum of (D/i) w^i for 0 < i < s) = x^((d+1)/2), with w = x^(d/s).
        1 | 3 => {
            let (dd, disc, x) = if s % 4 == 1 {
                if d % (2 * s) != s {
                    return None;
                }
                (d, big_s.clone(), a.fdiv_qr(c)?.1)
            } else {
                if d % (4 * s) != 2 * s {
                    return None;
                }
                (d / 2, -&big_s, (-a).fdiv_qr(c)?.1)
            };
            let w = x.powm(&int((dd / s) as i64), c)?;
            let (mut wi, mut sum) = (Integer::one(), Integer::zero());
            for i in 1..s {
                wi = mod_mul(&wi, &w, c);
                match disc.kronecker(&int(i as i64)) {
                    1 => sum = &sum + &wi,
                    -1 => sum = &sum - &wi,
                    _ => {}
                }
            }
            &mod_mul(&sum, &t, c) - &x.powm(&int(dd.div_ceil(2) as i64), c)?
        }
        // s = 2r: in (Z/c)[W]/(W^2 - a), W has order 2d mod each p, and p is
        // in L when t (sum of (8r/i) W^(ie) for 0 < i < 8r) = 2W, with
        // e = d/4r.
        _ => {
            if d % (4 * s) != 2 * s {
                return None;
            }
            let a = a.fdiv_qr(c)?.1;
            let mul = |x: &(Integer, Integer), y: &(Integer, Integer)| {
                let (x0, x1) = x;
                let (y0, y1) = y;
                let r0 = &(x0 * y0) + &(&(x1 * y1) * &a);
                let r1 = &(x0 * y1) + &(x1 * y0);
                (r0.fdiv_qr(c).unwrap().1, r1.fdiv_qr(c).unwrap().1)
            };
            let (mut w, mut e) = ((Integer::one(), Integer::zero()), d / (2 * s));
            let mut base = (Integer::zero(), Integer::one());
            while e > 0 {
                if e & 1 == 1 {
                    w = mul(&w, &base);
                }
                base = mul(&base, &base);
                e >>= 1;
            }
            let disc = int(4 * s as i64);
            let mut wi = (Integer::one(), Integer::zero());
            let mut sum = (Integer::zero(), Integer::zero());
            for i in 1..4 * s {
                wi = mul(&wi, &w);
                match disc.kronecker(&int(i as i64)) {
                    1 => sum = (&sum.0 + &wi.0, &sum.1 + &wi.1),
                    -1 => sum = (&sum.0 - &wi.0, &sum.1 - &wi.1),
                    _ => {}
                }
            }
            let z0 = mod_mul(&sum.0, &t, c);
            let z1 = &mod_mul(&sum.1, &t, c) - &int(2);
            z0.gcd(&z1)
        }
    };
    let g = z.gcd(c);
    (!g.is_one() && &g != c).then_some(g)
}

/// The factorization of b^k - 1 (plus false) or b^k + 1 (plus true), k > 0,
/// as the product of the cyclotomic values Phi_d(a) at the base a with
/// b = a^j, over the d dividing jk, or dividing 2jk but not jk. Each value
/// loses its primes dividing d, the primes above 10^9 the tables list, and
/// those below 10^9 (which the tables leave out), then splits into its
/// Aurifeuillian factors. `prime` tests what is left, and `rest` factors
/// what is composite.
pub fn factor_power(
    b: &Integer,
    k: u64,
    plus: bool,
    prime: &dyn Fn(&Integer) -> bool,
    rest: &mut dyn FnMut(&Integer) -> Vec<(Integer, u64)>,
) -> Vec<(Integer, u64)> {
    factor_with(table(), b, k, plus, prime, rest)
}

fn factor_with(
    table: Option<&Table>,
    b: &Integer,
    k: u64,
    plus: bool,
    prime: &dyn Fn(&Integer) -> bool,
    rest: &mut dyn FnMut(&Integer) -> Vec<(Integer, u64)>,
) -> Vec<(Integer, u64)> {
    let (a, j) = b.perfect_power().unwrap_or((b.clone(), 1));
    let n = j * k;
    let ds: Vec<u64> = if plus { divisors(2 * n).into_iter().filter(|d| n % d != 0).collect() } else { divisors(n) };
    let listed = match (table, a.to_u64()) {
        (Some(t), Some(a)) => t.lookup(a, &ds),
        _ => vec![Vec::new(); ds.len()],
    };
    let mut out = Vec::new();
    for (&d, listed) in ds.iter().zip(listed) {
        let mut v = cyclotomic_value(d, &a);
        if d <= 2 {
            if !v.is_one() {
                out.extend(rest(&v));
            }
            continue;
        }
        let mut take = |v: &mut Integer, p: &Integer, known: bool| {
            let (e, r) = v.remove(p);
            if e > 0 {
                *v = r;
                if known || prime(p) {
                    out.push((p.clone(), e));
                } else {
                    out.extend(rest(p).into_iter().map(|(q, f)| (q, f * e)));
                }
            }
        };
        for q in prime_divisors(d) {
            take(&mut v, &Integer::from_u64(q), true);
        }
        for p in &listed {
            take(&mut v, p, false);
        }
        // On smaller values, ECM finds the primes below 10^9 faster.
        if lcm2(d) >= 64 && v.bits() > 1024 {
            for p in small_primes(&a, d, &v) {
                take(&mut v, &Integer::from_u64(p), true);
            }
        }
        let parts = match aurifeuillian(&a, d, &v) {
            Some(g) => vec![v.divexact(&g), g],
            None => vec![v],
        };
        for v in parts {
            if v.is_one() {
            } else if prime(&v) {
                out.push((v, 1));
            } else {
                out.extend(rest(&v));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(s: &str) -> Integer {
        Integer::parse(s).unwrap()
    }

    fn small_table() -> Table {
        Table::open(Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/cunningham/cunningham-small.bin"))).unwrap()
    }

    /// The factorization of b^k + c, checked to be one into probable primes.
    fn factor(table: Option<&Table>, b: u64, k: u64, c: i64) -> Vec<(Integer, u64)> {
        let mut stages = super::super::Stages { proof: false, ..Default::default() };
        let (mut rng, mut stored) = (crate::random::Rng::new(1), Vec::new());
        let b = Integer::from_u64(b);
        let mut f = factor_with(table, &b, k, c > 0, &|p| p.is_probable_prime(), &mut |m| stages.factor_general(m, &mut rng, &mut stored).0);
        f.sort();
        assert!(f.iter().all(|(p, _)| p.is_probable_prime()), "{b}^{k} + {c}");
        assert_eq!(f.iter().fold(Integer::one(), |x, (p, e)| &x * &p.pow(*e)), &b.pow(k) + c, "{b}^{k} + {c}");
        f
    }

    #[test]
    fn varints_round_trip() {
        let xs = ["0", "1", "127", "128", "16383", "16384", "18446744073709551615", "18446744073709551616", "340282366920938463463374607431768211457"];
        let mut buf = Vec::new();
        let mut xs: Vec<Integer> = xs.iter().map(|x| int(x)).collect();
        xs.push(&Integer::from_u64(3).pow(500) + &Integer::from_u64(12345));
        for x in &xs {
            put_int(&mut buf, x);
        }
        let mut pos = 0;
        for x in &xs {
            assert_eq!(&get_int(&buf, &mut pos).unwrap(), x);
        }
        assert_eq!(pos, buf.len());
        assert!(get_int(&[0x80, 0x80], &mut 0).is_none());
    }

    #[test]
    fn built_files_read_back() {
        let lines = "2 67- 761838257287\n2 101- 7432339208719\n2 103+ 415141630193\n10 50+ 14103673319201\n10 50+ 1680588011350901\n\
                     3 5- 1000000007\n7 5+ 761838257287\n12 2+ 5\nx\n200 3- 1000000007\n";
        let path = std::env::temp_dir().join(format!("calyx-cunningham-{}.bin", std::process::id()));
        let stats = build(lines.as_bytes(), File::create(&path).unwrap(), (2, 99), true).unwrap();
        assert_eq!((stats.lines, stats.primes, stats.bases), (10, 5, 2));
        assert_eq!((stats.not_dividing.len(), stats.malformed.len()), (2, 2));
        let t = Table::open(&path).unwrap();
        std::fs::remove_file(&path).unwrap();
        assert_eq!(t.bases, (2, 11));
        assert_eq!(t.lookup(2, &[67, 101, 206, 1]), [vec![int("761838257287")], vec![int("7432339208719")], vec![int("415141630193")], vec![]]);
        let ds = divisors(100);
        let found: Vec<Integer> = t.lookup(10, &ds).into_iter().flatten().collect();
        assert_eq!(found, [int("14103673319201"), int("1680588011350901")]);
        assert!(t.lookup(3, &[1, 2, 5]).iter().all(|v| v.is_empty()));
        assert!(t.lookup(1000, &[1]).iter().all(|v| v.is_empty()));
    }

    #[test]
    fn cyclotomic_values() {
        let two = Integer::from_u64(2);
        assert_eq!(cyclotomic_value(1, &two), Integer::one());
        assert_eq!(cyclotomic_value(12, &Integer::from_u64(10)), Integer::from_u64(9901));
        assert_eq!(cyclotomic_value(105, &two), int("473474689919911"));
    }

    /// The Aurifeuillian factors of 2^(2m) + 1, 3^(3m) + 1 and 5^(5m) - 1
    /// for odd m, from their classical formulas, gather the same primes as
    /// the split.
    #[test]
    fn aurifeuillian_splits() {
        for m in (1..60u64).step_by(2) {
            let one = Integer::one();
            let pw = |a: u64, e: u64| Integer::from_u64(a).pow(e);
            let halves = |x: Integer, y: Integer| (&x - &y, &x + &y);
            let cases = [
                (2, 2 * m, true, halves(&pw(2, m) + &one, pw(2, m.div_ceil(2)))),
                (3, 3 * m, true, halves(&pw(3, m) + &one, pw(3, m.div_ceil(2)))),
                (5, 5 * m, false, {
                    let t = pw(5, m);
                    halves(&(&(&t * &t) + &(&t * 3)) + &one, &pw(5, m.div_ceil(2)) * &(&t + &one))
                }),
            ];
            for (a, n, plus, (l, r)) in cases {
                let ai = Integer::from_u64(a);
                for d in divisors(if plus { 2 * n } else { n }).into_iter().filter(|d| !plus || n % d != 0) {
                    let mut c = cyclotomic_value(d, &ai);
                    for q in prime_divisors(d) {
                        c = c.remove(&Integer::from_u64(q)).1;
                    }
                    let (gl, gr) = (c.gcd(&l), c.gcd(&r));
                    if &gl * &gr != c {
                        // Phi_d(a) is not one of the Aurifeuillian values.
                        assert!(gl.is_one() || gr.is_one() || gl == c || gr == c, "{a} {d}");
                        continue;
                    }
                    match aurifeuillian(&ai, d, &c) {
                        Some(g) => assert!(g == gl || g == gr, "{a} {d}"),
                        None => assert!(gl.is_one() || gr.is_one(), "{a} {d}"),
                    }
                }
            }
        }
    }

    /// The small table and computation alone agree.
    #[test]
    fn small_table_and_computation_agree() {
        let t = small_table();
        assert_eq!(t.bases, (2, 100));
        for (b, k, c) in [(2, 360, -1), (2, 330, 1), (3, 150, 1), (10, 90, 1), (6, 66, 1), (12, 105, 1), (97, 30, -1), (4, 75, 1), (99, 33, 1)] {
            assert_eq!(factor(Some(&t), b, k, c), factor(None, b, k, c), "{b}^{k} + {c}");
        }
    }

    /// Numbers only the small table factors quickly, and the prime below
    /// 10^9 that it leaves out of Phi_157(5).
    #[test]
    fn small_table_factors_large_powers() {
        let t = small_table();
        for (b, k, c) in [(2, 1001, -1), (2, 1150, 1), (3, 999, 1), (5, 875, -1), (6, 546, 1), (7, 497, 1), (99, 55, 1), (97, 100, -1), (8, 350, -1)] {
            factor(Some(&t), b, k, c);
        }
        assert!(factor(Some(&t), 5, 157, -1).iter().any(|(p, _)| p == &Integer::from_u64(5129819)));
    }

    /// With all the bases below 10000, when that file is installed.
    #[test]
    fn full_table() {
        let Some(t) = table().filter(|t| t.bases.1 > 9999) else {
            eprintln!("skipped: the full Cunningham table is not installed");
            return;
        };
        for (b, k, c) in [(1001, 100, 1), (1001, 210, -1), (3001, 180, -1), (7919, 90, 1), (9999, 60, 1), (9999, 120, -1)] {
            factor(Some(t), b, k, c);
        }
    }
}
