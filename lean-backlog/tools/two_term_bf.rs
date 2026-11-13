// Exhaustive search for two-term operators with a code of full size, over GF(2) or GF(3)
// (lean-backlog/notes/two-term-equality.md, Theorem 1).  Driver: two_term_equality.py in the same folder.
//
// Usage:  two_term_bf P D THREADS A0 A1
//   P        2 or 3
//   D        the size d of the matrices (d*d*2 digits are enumerated: 3^18 = 3.9e8 at d = 3, 2^32 = 4.3e9 at d = 4)
//   THREADS  number of worker threads
//   A0, A1   the two row factors, each as a string of d*d digits, row by row
// Output: one line "B0 B1" (two strings of d*d digits) for every pair (B_0, B_1) such that
//   rank(swap - A0 (x) B0 - A1 (x) B1) <= d(d-1)/2,   i.e. the code {X : X^T = sum_a A_a X B_a^T} has dimension
//   at least d(d+1)/2; then a line "done COUNT CANDIDATES".
// The operator matrix has the entry  [i = l][j = k] - sum_a A_a[i][k] B_a[j][l]  in row (i, j), column (k, l).
// Compile: rustc -O -o two_term_bf two_term_bf.rs   (no dependencies).

use std::env;
use std::thread;

fn digits(s: &str) -> Vec<u8> {
    s.bytes().map(|c| c - b'0').collect()
}

// p = 2: rows as bit masks, rank by insertion into an XOR basis, stop as soon as the rank exceeds maxrank
fn run_p2(d: usize, a0: &[u8], a1: &[u8], lo: u64, hi: u64, maxrank: usize) -> Vec<(u64, u64)> {
    let n = d * d;
    let rowmask: u64 = (1u64 << d) - 1;
    let nmask: u64 = (1u64 << n) - 1;
    // for each i: list of (a, shift) with A_a[i][k] = 1, shift = k*d
    let mut terms: Vec<Vec<(usize, usize)>> = vec![Vec::new(); d];
    for i in 0..d {
        for k in 0..d {
            if a0[i * d + k] == 1 {
                terms[i].push((0, k * d));
            }
            if a1[i * d + k] == 1 {
                terms[i].push((1, k * d));
            }
        }
    }
    let mut out = Vec::new();
    let mut basis = vec![0u32; n];
    for c in lo..hi {
        let b = [c & nmask, (c >> n) & nmask];
        for x in basis.iter_mut() {
            *x = 0;
        }
        let mut rank = 0usize;
        let mut ok = true;
        'rows: for i in 0..d {
            for j in 0..d {
                let mut v: u32 = 1u32 << (j * d + i);
                for &(a, sh) in &terms[i] {
                    v ^= (((b[a] >> (j * d)) & rowmask) as u32) << sh;
                }
                while v != 0 {
                    let h = 31 - v.leading_zeros() as usize;
                    if basis[h] == 0 {
                        basis[h] = v;
                        rank += 1;
                        break;
                    }
                    v ^= basis[h];
                }
                if rank > maxrank {
                    ok = false;
                    break 'rows;
                }
            }
        }
        if ok {
            out.push((b[0], b[1]));
        }
    }
    out
}

// general small prime: entries as u8, Gaussian elimination, stop as soon as the rank exceeds maxrank
fn run_gen(p: u8, d: usize, a0: &[u8], a1: &[u8], lo: u64, hi: u64, maxrank: usize) -> Vec<(Vec<u8>, Vec<u8>)> {
    let n = d * d;
    let mut inv = vec![0u8; p as usize];
    for x in 1..p {
        for y in 1..p {
            if (x as u32 * y as u32) % p as u32 == 1 {
                inv[x as usize] = y;
            }
        }
    }
    // for each i: list of (a, k, coefficient = -A_a[i][k] mod p)
    let mut terms: Vec<Vec<(usize, usize, u8)>> = vec![Vec::new(); d];
    for i in 0..d {
        for k in 0..d {
            if a0[i * d + k] != 0 {
                terms[i].push((0, k, (p - a0[i * d + k]) % p));
            }
            if a1[i * d + k] != 0 {
                terms[i].push((1, k, (p - a1[i * d + k]) % p));
            }
        }
    }
    let mut out = Vec::new();
    // the digits of the candidate index, least significant first: B_0 then B_1, each row by row
    let mut dig = vec![0u8; 2 * n];
    let mut c = lo;
    for t in 0..2 * n {
        dig[t] = (c % p as u64) as u8;
        c /= p as u64;
    }
    let mut m = vec![0u8; n * n];
    for _ in lo..hi {
        for x in m.iter_mut() {
            *x = 0;
        }
        for i in 0..d {
            for j in 0..d {
                let r = (i * d + j) * n;
                m[r + j * d + i] = 1;
                for &(a, k, coef) in &terms[i] {
                    for l in 0..d {
                        let idx = r + k * d + l;
                        m[idx] = ((m[idx] as u32 + coef as u32 * dig[a * n + j * d + l] as u32) % p as u32) as u8;
                    }
                }
            }
        }
        let mut rank = 0usize;
        let mut ok = true;
        for col in 0..n {
            let mut piv = n;
            for r in rank..n {
                if m[r * n + col] != 0 {
                    piv = r;
                    break;
                }
            }
            if piv == n {
                continue;
            }
            if rank == maxrank {
                ok = false;
                break;
            }
            if piv != rank {
                for t in 0..n {
                    m.swap(piv * n + t, rank * n + t);
                }
            }
            let iv = inv[m[rank * n + col] as usize];
            for r in rank + 1..n {
                let f = m[r * n + col];
                if f != 0 {
                    let g = (p as u32 - (f as u32 * iv as u32) % p as u32) % p as u32;
                    for t in col..n {
                        m[r * n + t] = ((m[r * n + t] as u32 + g * m[rank * n + t] as u32) % p as u32) as u8;
                    }
                }
            }
            rank += 1;
        }
        if ok {
            out.push((dig[..n].to_vec(), dig[n..].to_vec()));
        }
        // next candidate
        for t in 0..2 * n {
            dig[t] += 1;
            if dig[t] < p {
                break;
            }
            dig[t] = 0;
        }
    }
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 6 {
        eprintln!("usage: two_term_bf P D THREADS A0 A1");
        std::process::exit(2);
    }
    let p: u8 = args[1].parse().unwrap();
    let d: usize = args[2].parse().unwrap();
    let nthreads: u64 = args[3].parse().unwrap();
    let a0 = digits(&args[4]);
    let a1 = digits(&args[5]);
    let n = d * d;
    assert!(p == 2 || p == 3);
    assert!(a0.len() == n && a1.len() == n);
    assert!(a0.iter().chain(a1.iter()).all(|&x| x < p));
    let total: u64 = (p as u64).pow(2 * n as u32);
    let maxrank = d * (d - 1) / 2;
    let chunk = (total + nthreads - 1) / nthreads;
    let mut count = 0u64;
    thread::scope(|s| {
        let mut handles = Vec::new();
        for t in 0..nthreads {
            let lo = t * chunk;
            let hi = std::cmp::min(total, lo + chunk);
            let (a0, a1) = (&a0, &a1);
            handles.push(s.spawn(move || {
                let mut lines = Vec::new();
                if lo >= hi {
                    return lines;
                }
                if p == 2 {
                    for (b0, b1) in run_p2(d, a0, a1, lo, hi, maxrank) {
                        let f = |x: u64| (0..n).map(|t| if (x >> t) & 1 == 1 { '1' } else { '0' }).collect::<String>();
                        lines.push(format!("{} {}", f(b0), f(b1)));
                    }
                } else {
                    for (b0, b1) in run_gen(p, d, a0, a1, lo, hi, maxrank) {
                        let f = |x: &Vec<u8>| x.iter().map(|&v| (b'0' + v) as char).collect::<String>();
                        lines.push(format!("{} {}", f(&b0), f(&b1)));
                    }
                }
                lines
            }));
        }
        for h in handles {
            for line in h.join().unwrap() {
                println!("{}", line);
                count += 1;
            }
        }
    });
    println!("done {} {}", count, total);
}
