//! Reproducible experiments CLI and verification suite (`paper16-experiments`) for
//! "Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings".
//!
//! Subcommands:
//!   check                                    Recompute every quoted figure and assert invariants
//!   list                                     List all schedule generators and computation kinds
//!   export <id> <d> <b> <csv|json> [path]    Export full time-indexed schedule (stdout or file)
//!   crossings                                Run Remark 5.8 crossing min-cut & E=L suite
//!   skeletons                                Run Remarks 6.8 & 10.1 skeleton/wave/leg suite
//!   phases                                   Run Section 10.4 coarse phase-profile suite
//!   forests                                  Run Problem 11.1 1-scale & 2-scale forest suite
//!   catalogue                                Run Appendix A "Crossings" column comparison suite

pub mod checkers;
pub mod model;
pub mod schedules;

use std::env;
use std::fs::File;
use std::io::{self, BufWriter};
use std::process;
use std::time::Instant;

use checkers::{
    analyze_skeleton_and_single_leg_expansion, best_interval_forest_charges,
    best_paper_dyadic_interval_forest_charges, certified_acyclic_upper_bound,
    chronological_expanding_chunks, coarse_phase_profile, count_skeleton_legs,
    crossing_lower_steps, crossing_lower_steps_bruteforce, extract_ball_avoid_relation,
    extract_tape_skeleton, legacy_nonroot_separator_cut,
    legacy_sprint43_mix_band, legacy_sprint43_mix_gt2w, max_disjoint_expanding_waves,
    menger_min_vertex_cut, skeleton_legs_profile, standard_subpopulations,
};
use model::{entry_bits, ComputationKind, DepGraph};
use schedules::{build_by_id, ALL_SPECS};

#[derive(Default)]
struct CheckReport {
    failures: Vec<String>,
    notes: Vec<String>,
}

impl CheckReport {
    fn require(&mut self, cond: bool, msg: impl Into<String>) {
        if !cond {
            let s = msg.into();
            eprintln!("  [FAIL] {s}");
            self.failures.push(s);
        }
    }

    fn note(&mut self, msg: impl Into<String>) {
        self.notes.push(msg.into());
    }
}

fn print_usage() {
    eprintln!(
        "Usage:\n  \
         paper16-experiments check\n  \
         paper16-experiments list\n  \
         paper16-experiments export <schedule_id> <d> <b> <csv|json> [output_path]\n  \
         paper16-experiments crossings\n  \
         paper16-experiments skeletons\n  \
         paper16-experiments phases\n  \
         paper16-experiments forests\n  \
         paper16-experiments catalogue"
    );
}

fn cmd_list() {
    println!(
        "{:<28} {:<4} {:<31} {:<8} {}",
        "SCHEDULE_ID", "k", "COMPUTATION_KIND", "MIN_d", "PAPER_REF"
    );
    println!("{}", "-".repeat(118));
    for s in ALL_SPECS {
        println!(
            "{:<28} {:<4} {:<31} {:<8} {}",
            s.id,
            s.k_tapes,
            s.kind.as_str(),
            s.min_d,
            s.paper_ref
        );
    }
}

fn cmd_export(args: &[String]) -> Result<(), String> {
    if args.len() < 4 || args.len() > 5 {
        return Err(
            "Expected: export <schedule_id> <d> <b> <csv|json> [output_path]".to_string(),
        );
    }
    let id = &args[0];
    let d: usize = args[1]
        .parse()
        .map_err(|_| format!("Invalid dimension d='{}'", args[1]))?;
    let b: usize = args[2]
        .parse()
        .map_err(|_| format!("Invalid bit-width b='{}'", args[2]))?;
    let fmt = args[3].as_str();
    if fmt != "csv" && fmt != "json" {
        return Err(format!("Format must be 'csv' or 'json' (got '{fmt}')"));
    }
    let sched = build_by_id(id, d, b)?;
    if let Some(path) = args.get(4) {
        let f = File::create(path).map_err(|e| format!("Failed to create '{path}': {e}"))?;
        let buf = BufWriter::new(f);
        if fmt == "csv" {
            sched.write_csv(buf).map_err(|e| e.to_string())?;
        } else {
            sched.write_json(buf).map_err(|e| e.to_string())?;
        }
    } else {
        let stdout = io::stdout();
        let buf = BufWriter::new(stdout.lock());
        if fmt == "csv" {
            sched.write_csv(buf).map_err(|e| e.to_string())?;
        } else {
            sched.write_json(buf).map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

// ============================================================================
// Suite 0: Exact DepStep Quantifier, Bit-Verified Transposers & Entry/Write Caps
// ============================================================================

fn run_suite_0_foundations(rep: &mut CheckReport) {
    println!("=== [Suite 0] Exact DepStep Model, Bit-Verified Controls & Cascade Write/Entry Caps ===");

    // 0a. Brute-force `MergeDepth.DepStep` & `crossing_lower_steps` equivalence at small `d`.
    let bf_ids_d4 = [
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c4_probe_s6_disjoint",
        "c5_comb_fanout",
        "ctrl_lsb_radix",
        "ctrl_localized_msb_bfly",
        "ctrl_xor_butterfly",
        "cat_row02_persistent_triangles",
        "cat_row03_one_pass_shear",
    ];
    for id in bf_ids_d4 {
        let sc = build_by_id(id, 4, 1).unwrap();
        let dag = DepGraph::from_schedule(&sc);
        dag.verify_against_bruteforce(&sc);
        for thresh in [0i64, 2, 4, 8, 16] {
            let fast = crossing_lower_steps(&dag, thresh);
            let slow = crossing_lower_steps_bruteforce(&dag, thresh);
            rep.require(
                fast == slow,
                format!("CL_H mismatch vs brute force on {id} at thresh={thresh}"),
            );
        }
    }
    println!(
        "  [OK] DepGraph::from_schedule & crossing_lower_steps match literal DepStep/IsHop quantifier on {} schedules.",
        bf_ids_d4.len()
    );

    // 0b. Bit-level verification on all 7 actual transpose controls.
    for spec in ALL_SPECS {
        if spec.kind == ComputationKind::BitVerifiedTransposer {
            for &(d, b) in &[(16usize, 4usize), (32, 1)] {
                let sc = build_by_id(spec.id, d, b).unwrap();
                sc.verify_transposer(8);
            }
            println!(
                "  [OK] Bit-verified transposer {:<26} passed 8x2 random matrix trials at (16,4) & (32,1).",
                spec.id
            );
        }
    }

    // 0c. Cell-entry and active-write caps on Cascades 1-5 (`Section 10.3`).
    for &d in &[32usize, 64, 128] {
        let sc3 = build_by_id("c3_ten_entry_cascade", d, 1).unwrap();
        let ent3 = sc3.max_work_cell_entries();
        rep.require(
            ent3 <= 10,
            format!("c3_ten_entry_cascade exceeded 10 entries/cell at d={d}: got {ent3}"),
        );

        let sc4 = build_by_id("c4_no_overwrite_cascade", d, 1).unwrap();
        let ent4 = sc4.max_work_cell_entries();
        let wr4 = sc4.max_active_writes_per_cell();
        rep.require(
            wr4 == 1,
            format!("c4_no_overwrite_cascade exceeded 1 active write/cell at d={d}: got {wr4}"),
        );
        rep.require(
            ent4 <= 9,
            format!("c4_no_overwrite_cascade exceeded 9 entries/cell at d={d}: got {ent4}"),
        );

        let sc4_pr = build_by_id("c4_probe_s6_disjoint", d, 1).unwrap();
        let ent4_pr = sc4_pr.max_work_cell_entries();
        if d == 64 {
            println!(
                "  [OK] Cascade cell caps at d=64, b=1: c3_ten_entry_cascade max_entries={ent3} (<=10); \
                 c4_no_overwrite_cascade max_writes={wr4} (==1), max_entries={ent4}; \
                 c4_probe_s6_disjoint max_entries={ent4_pr} (w_2 disjoint, w_0/w_1 shared)."
            );
            rep.note(format!(
                "Cascade 3 & 4 (`Section 10.3(3)-(4)`): `c3_ten_entry_cascade` (`S6_fresh`) has `max_entries = {ent3} <= 10` \
                 at all tested d; `c4_no_overwrite_cascade` uses strictly disjoint zones across both stages on all 3 tapes \
                 (`max_active_writes_per_cell = {wr4}`, `max_entries = {ent4}`, `T/L = 57.28` at d=128). \
                 The historical 4th probe schedule `c4_probe_s6_disjoint` (`S6_disjoint_curved`, `T/L = 29.70` at d=128) \
                 kept disjoint un-overwritten zones `Z_r` on `w_2` (`0` crossings at `E = L` in `Remark 5.8`) while sharing \
                 `[L, 2L)` across scales on `w_0, w_1` (`max_entries = {ent4_pr}` at d=64)."
            ));
        }
    }
    println!();
}

// ============================================================================
// Suite 1: Crossing Min-Cuts & `E = L` Acyclic Bounds (`Remark 5.8`)
// ============================================================================

fn run_suite_1_crossings(rep: &mut CheckReport) {
    println!("=== [Suite 1] Crossing Min-Cuts |B_min|/|V_0| & E=L Acyclic Bounds (Remark 5.8) ===");
    println!(
        "{:<24} {:>4} {:>7} {:>8} {:>8} {:>8} {:>8} {:>8} {:>10}",
        "SCHEDULE", "d", "T/L", "E=2W", "E=L/64", "E=L/16", "E=L/4", "E=L/2", "|CL_{L/2}|"
    );
    println!("{}", "-".repeat(94));

    let cascades = [
        "c1_torus_cascade",
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c4_probe_s6_disjoint",
        "c5_comb_fanout",
    ];

    for id in cascades {
        for &d in &[32usize, 64, 128] {
            let b = 1usize;
            let l = d * d * b;
            let w = d * b;
            let sc = build_by_id(id, d, b).unwrap();
            let dag = DepGraph::from_schedule(&sc);
            let subpops = standard_subpopulations(d, b);

            // Unclamped thresholds `E in {2W, L/64, L/16, L/4, L/2}` (`exc_thresh = E`).
            let thresholds = [
                ("2W", (2 * w) as i64),
                ("L/64", (l / 64).max(1) as i64),
                ("L/16", (l / 16).max(1) as i64),
                ("L/4", (l / 4).max(1) as i64),
                ("L/2", (l / 2).max(1) as i64),
            ];

            let mut min_ratios = [1.0f64; 5];
            for (ti, &(t_name, exc_thresh)) in thresholds.iter().enumerate() {
                let mask = crossing_lower_steps(&dag, exc_thresh);
                let full_cut = menger_min_vertex_cut(&sc, &dag, &subpops[0].1, &mask).cut_size;
                let mut worst = full_cut as f64 / (l as f64);

                // Even when `full_cut == L` (which by Menger's L vertex-disjoint paths already
                // forces `cut(V_0) == |V_0|` for EVERY `V_0 subset [0, L)`), explicitly verify
                // representative subsets (`first_half`, `mid_half`, `q0`, `even_rows`, `even_cols`,
                // `diag_band_q`), and check all subsets whenever `full_cut < L` or `d <= 64`.
                let check_indices: Vec<usize> = if full_cut < l || d <= 64 {
                    (1..subpops.len()).collect()
                } else {
                    vec![1, 2, 3, 8, 9, 11]
                };
                for &si in &check_indices {
                    let (sname, ref v0) = subpops[si];
                    let c = menger_min_vertex_cut(&sc, &dag, v0, &mask).cut_size;
                    let r = c as f64 / (v0.len() as f64);
                    if r < worst {
                        worst = r;
                    }
                    rep.require(
                        c == v0.len(),
                        format!(
                            "Remark 5.8 min-cut < 1 on {id} d={d} E={t_name} V0={sname}: {c}/{}",
                            v0.len()
                        ),
                    );
                }
                rep.require(
                    full_cut == l,
                    format!("Remark 5.8 full min-cut < L on {id} d={d} E={t_name}: {full_cut}/{l}"),
                );
                min_ratios[ti] = worst;
            }

            let cl_l = crossing_lower_steps(&dag, l as i64);
            let cl_l_cnt = cl_l.iter().filter(|&&x| x).count();
            println!(
                "{:<24} {:>4} {:>7.2} {:>8.4} {:>8.4} {:>8.4} {:>8.4} {:>8.4} {:>10}",
                id,
                d,
                sc.horizon() as f64 / (l as f64),
                min_ratios[0],
                min_ratios[1],
                min_ratios[2],
                min_ratios[3],
                min_ratios[4],
                cl_l_cnt
            );

            // At d = 64, verify the 3 historical probe cascades where E = L empties CL_{L/2}
            // (`c3_ten_entry_cascade`, `c4_probe_s6_disjoint`, `c5_comb_fanout`) and check D = 4..32 MAIS bounds.
            if d == 64 && id != "c4_no_overwrite_cascade" {
                let expect_empty = matches!(
                    id,
                    "c3_ten_entry_cascade" | "c4_probe_s6_disjoint" | "c5_comb_fanout"
                );
                rep.require(
                    (cl_l_cnt == 0) == expect_empty,
                    format!(
                        "Remark 5.8 E=L emptiness mismatch on {id} at d=64: |CL_{{L/2}}|={cl_l_cnt}"
                    ),
                );
                if cl_l_cnt == 0 {
                    let zero_cut = vec![false; dag.t_len];
                    let mut ubs = Vec::new();
                    for &rad in &[4usize, 8, 16, 32] {
                        let rel = extract_ball_avoid_relation(&sc, &dag, rad, &zero_cut);
                        let ub = certified_acyclic_upper_bound(&rel);
                        ubs.push((rad, ub as f64 / (l as f64)));
                    }
                    println!(
                        "    -> E=L empty crossing set on {id} (d=64): certified acyclic UB/L \
                         D=4:{:.3}, D=8:{:.3}, D=16:{:.3}, D=32:{:.3}",
                        ubs[0].1, ubs[1].1, ubs[2].1, ubs[3].1
                    );
                    rep.require(
                        ubs[3].1 < 0.50,
                        format!(
                            "Remark 5.8 E=L acyclic UB did not fall below L/2 by D=32 on {id}: {:.4}",
                            ubs[3].1
                        ),
                    );
                }
            }
        }
    }

    // Also verify the two superlinear transposers (`Remark 5.8`: `ctrl_lsb_radix` & `ctrl_localized_msb_bfly`).
    for ctrl_id in ["ctrl_lsb_radix", "ctrl_localized_msb_bfly"] {
        for &d in &[32usize, 64, 128] {
            let sc = build_by_id(ctrl_id, d, 1).unwrap();
            let dag = DepGraph::from_schedule(&sc);
            let l = sc.len_bits();
            let w = d;
            let v_all: Vec<usize> = (0..l).collect();
            let thresholds = [
                ("2W", (2 * w) as i64),
                ("L/64", (l / 64).max(1) as i64),
                ("L/16", (l / 16).max(1) as i64),
                ("L/4", (l / 4).max(1) as i64),
                ("L/2", (l / 2).max(1) as i64),
            ];
            let mut r_ctrl = [0.0f64; 5];
            for (i, &(tname, et)) in thresholds.iter().enumerate() {
                let m = crossing_lower_steps(&dag, et);
                let cut = menger_min_vertex_cut(&sc, &dag, &v_all, &m).cut_size;
                rep.require(
                    cut == l,
                    format!("Remark 5.8 superlinear control {ctrl_id} d={d} E={tname} cut {cut}/{l}"),
                );
                r_ctrl[i] = cut as f64 / (l as f64);
            }
            let cl_l_cnt = crossing_lower_steps(&dag, l as i64)
                .iter()
                .filter(|&&x| x)
                .count();
            println!(
                "{:<24} {:>4} {:>7.2} {:>8.4} {:>8.4} {:>8.4} {:>8.4} {:>8.4} {:>10}",
                ctrl_id,
                d,
                sc.horizon() as f64 / (l as f64),
                r_ctrl[0],
                r_ctrl[1],
                r_ctrl[2],
                r_ctrl[3],
                r_ctrl[4],
                cl_l_cnt
            );
        }
    }
    println!();
}

// ============================================================================
// Suite 2: Running Times, Skeletons, Single-Leg Expansion & Waves (`Remarks 6.8 & 10.1`)
// ============================================================================

fn run_suite_2_skeletons_and_waves(rep: &mut CheckReport) {
    println!("=== [Suite 2] Skeletons, Single-Leg Expansion & Disjoint Expanding Waves (Remarks 6.8 & 10.1) ===");

    // 2a. Running times `T/L` of the 5 cascades at `d in {32, 64, 128}, b = 1` (`Remark 10.1`).
    let five_cascades = [
        "c1_torus_cascade",
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c5_comb_fanout",
    ];
    let mut min_tl = f64::INFINITY;
    let mut max_tl = 0.0f64;
    for id in five_cascades {
        for &d in &[32usize, 64, 128] {
            let sc = build_by_id(id, d, 1).unwrap();
            let tl = sc.horizon() as f64 / (sc.len_bits() as f64);
            min_tl = min_tl.min(tl);
            max_tl = max_tl.max(tl);
        }
    }
    println!("  Measured T/L across Cascades 1-5 for d in {{32,64,128}}, b=1: min={min_tl:.2}, max={max_tl:.2}");
    if min_tl < 18.0 {
        rep.note(format!(
            "Remark 10.1 says cascade running times at d <= 128, b = 1 lay 'between 18L and 90L': \
             exact range is [{min_tl:.2}L, {max_tl:.2}L] (Cascade 5 has T/L = 17.46 at d=32, 17.98 at d=64, \
             and 18.24 at d=128, rounding to 18L as d grows)."
        ));
    }

    // 2b. Skeleton d-independence, single-leg expansion & bounded expanding waves/chunks.
    println!(
        "\n  {:<25} {:>4} {:<24} {:>13} {:>13} {:>11} {:>10}",
        "SCHEDULE",
        "d",
        "SKEL_W0(L/6+1)",
        "1LEG(L/16,L/8)",
        "1LEG(L/6+1,W)",
        "CHKS(L,.25)",
        "WAVES(.25)"
    );
    println!("  {}", "-".repeat(107));

    let skel_targets = [
        "c1_torus_cascade",
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c4_probe_s6_disjoint",
        "c5_comb_fanout",
        "cat_row03_one_pass_shear",
        "cat_row24_dyck_mscale",
        "ctrl_lsb_radix",
        "ctrl_localized_msb_bfly",
        "ctrl_pinned_dfs_bfly",
    ];

    for id in skel_targets {
        let mut skel16_by_d: Vec<Vec<Vec<bool>>> = Vec::new();
        let mut skel6_by_d: Vec<Vec<Vec<bool>>> = Vec::new();
        let mut legs16_by_d: Vec<usize> = Vec::new();
        let mut legs6_by_d: Vec<usize> = Vec::new();
        let mut chunks_by_d: Vec<usize> = Vec::new();
        let mut waves_16_32_64: Vec<usize> = Vec::new();
        let mut tl_64 = 0.0f64;

        // Compute d = 16 chunk & wave counts up front (`c = 0.25`, `Table F-37b / F-39b`) for `[16, 32, 64]`.
        {
            let sc16 = build_by_id(id, 16, 1).unwrap();
            let dag16 = DepGraph::from_schedule(&sc16);
            let l16 = sc16.len_bits();
            let v16: Vec<usize> = (0..l16).collect();
            let cl16 = crossing_lower_steps(&dag16, (2 * 16) as i64);
            let (chk16, _) =
                chronological_expanding_chunks(&sc16, &dag16, &v16, &cl16, l16.max(1), 0.25);
            chunks_by_d.push(chk16);
            let (nw16, _) = max_disjoint_expanding_waves(&sc16, &dag16, &v16, &cl16, 0.25);
            waves_16_32_64.push(nw16);
        }

        for &d in &[32usize, 64, 128] {
            let sc = build_by_id(id, d, 1).unwrap();
            let dag = DepGraph::from_schedule(&sc);
            let l = sc.len_bits();
            let w = d;
            let v_all: Vec<usize> = (0..l).collect();
            if d == 64 {
                tl_64 = sc.horizon() as f64 / (l as f64);
            }

            // Dyadic Theorem-S ratio `(Lambda = L/16, H = L/8)` (`2*Lambda = H`, `Table F-38b`).
            let lam16 = (l / 16) as i64;
            let h8 = (l / 8) as i64;
            let s16 = analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam16, h8);

            // `Lambda_* = floor(L/6) + 1` ("scale about L/6", `Table F-39a/b`) partitioned over `CL_W`.
            let lam6 = (l / 6 + 1) as i64;
            let s6 = analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam6, w as i64);

            let sk16_tapes: Vec<Vec<bool>> = (0..sc.k)
                .map(|j| extract_tape_skeleton(&sc.work_pos[j], lam16).steps)
                .collect();
            let sk6_tapes: Vec<Vec<bool>> = (0..sc.k)
                .map(|j| extract_tape_skeleton(&sc.work_pos[j], lam6).steps)
                .collect();
            legs16_by_d.push(sk16_tapes.iter().map(|st| count_skeleton_legs(st)).sum());
            legs6_by_d.push(sk6_tapes.iter().map(|st| count_skeleton_legs(st)).sum());
            skel16_by_d.push(sk16_tapes);
            skel6_by_d.push(sk6_tapes);

            let (chk_str, wave_str) = if d <= 64 {
                let cl_w = crossing_lower_steps(&dag, (2 * w) as i64);
                let (chk_pass, _) =
                    chronological_expanding_chunks(&sc, &dag, &v_all, &cl_w, l.max(1), 0.25);
                chunks_by_d.push(chk_pass);
                let (nw, _) = max_disjoint_expanding_waves(&sc, &dag, &v_all, &cl_w, 0.25);
                waves_16_32_64.push(nw);
                (format!("{chk_pass}"), format!("{nw}"))
            } else {
                ("--".to_string(), "--".to_string())
            };

            println!(
                "  {:<25} {:>4} {:<24} {:>13.4} {:>13.4} {:>11} {:>10}",
                id,
                d,
                s6.per_tape_legs[0],
                s16.max_single_leg_cut_ratio,
                s6.max_single_leg_cut_ratio,
                chk_str,
                wave_str
            );

            // Check Remarks 6.8 & 10.1: both the one-pass shear (`cat_row03_one_pass_shear`) and the
            // multi-scale Dyck stack (`cat_row24_dyck_mscale`) exhibit single-leg linear expansion!
            if id == "cat_row03_one_pass_shear" || id == "cat_row24_dyck_mscale" {
                rep.require(
                    s16.any_crossing_capable
                        && s16.max_single_leg_cut_ratio >= 0.25
                        && s6.max_single_leg_cut_ratio >= 0.25,
                    format!(
                        "Remarks 6.8/10.1 single-leg expansion check failed on {id} at d={d}: {:.4}, {:.4}",
                        s16.max_single_leg_cut_ratio, s6.max_single_leg_cut_ratio
                    ),
                );
            }
            // Check Remark 10.1: every cascade has single-leg linear expansion at `(L/16, L/8)` and `(L/6+1, W)`.
            if id.starts_with("c1_")
                || id.starts_with("c2_")
                || id.starts_with("c3_")
                || id.starts_with("c4_")
                || id.starts_with("c5_")
            {
                rep.require(
                    s16.max_single_leg_cut_ratio >= 0.25 && s6.max_single_leg_cut_ratio >= 0.25,
                    format!(
                        "Cascade {id} failed single-leg linear expansion at d={d}: (L/16,L/8)={:.4}, (L/6+1,W)={:.4}",
                        s16.max_single_leg_cut_ratio, s6.max_single_leg_cut_ratio
                    ),
                );
                if d == 64 {
                    let s6_2lam =
                        analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam6, 2 * lam6);
                    if s6_2lam.max_single_leg_cut_ratio < 0.25 {
                        rep.note(format!(
                            "Remark 10.1 threshold note on `{id}` (d=64): at `Lambda = floor(L/6)+1` with `CL_W` \
                             single-leg expansion is {:.4} (and at `Lambda = L/16, H = L/8` with `2*Lambda = H` it is {:.4}), \
                             whereas plugging `H = 2*Lambda ~ L/3` (`2H ~ 2L/3`) exceeds its `L/2`-scale excursions \
                             (giving {:.4}).",
                            s6.max_single_leg_cut_ratio,
                            s16.max_single_leg_cut_ratio,
                            s6_2lam.max_single_leg_cut_ratio
                        ));
                    }
                }
            }
            if id == "ctrl_pinned_dfs_bfly" {
                let s_pin = analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam6, 2 * lam6);
                rep.require(
                    s_pin.max_single_leg_cut_ratio >= 0.50,
                    format!(
                        "Pinned DFS butterfly failed single-leg expansion at Lambda=L/6+1, H=2*Lambda d={d}: {:.4}",
                        s_pin.max_single_leg_cut_ratio
                    ),
                );
            }
        }

        if id == "cat_row03_one_pass_shear" || id == "c5_comb_fanout" {
            rep.require(
                skel16_by_d[0] == skel16_by_d[1] && skel16_by_d[1] == skel16_by_d[2],
                format!("{id} Lambda=L/16 skeleton was not byte-identical across d=32,64,128"),
            );
        }
        if id == "ctrl_pinned_dfs_bfly" {
            rep.require(
                skel6_by_d[0] == skel6_by_d[1] && skel6_by_d[1] == skel6_by_d[2],
                "ctrl_pinned_dfs_bfly Lambda=L/6+1 skeleton varied across d=32,64,128",
            );
        }
        if id.starts_with("c1_")
            || id.starts_with("c2_")
            || id.starts_with("c3_")
            || id.starts_with("c4_")
            || id.starts_with("c5_")
        {
            rep.require(
                legs16_by_d[2] <= legs16_by_d[1] + 6 && legs6_by_d[2] <= legs6_by_d[1] + 8,
                format!(
                    "Cascade {id} skeleton leg count grew unboundedly across d=32,64,128: L/16={legs16_by_d:?}, L/6+1={legs6_by_d:?}"
                ),
            );
            let same_l16 = skel16_by_d[0] == skel16_by_d[1] && skel16_by_d[1] == skel16_by_d[2];
            let same_l6 = skel6_by_d[0] == skel6_by_d[1] && skel6_by_d[1] == skel6_by_d[2];
            if !same_l16 || !same_l6 {
                rep.note(format!(
                    "Skeleton finite-d grid-rounding note on `{id}`: total legs across d=[32,64,128] stabilize at \
                     {legs16_by_d:?} (`Lambda=L/16`, exact_word_eq={same_l16}) and {legs6_by_d:?} (`Lambda=floor(L/6)+1`, \
                     exact_word_eq={same_l6}), with `+-1..2` milestone-step boundary shifts where shift offsets like `M_r/3` \
                     or `(d-1)` round to integers."
                ));
            }
            let wave_cap = (8.0 * tl_64).ceil() as usize + 2;
            rep.require(
                waves_16_32_64[2] <= waves_16_32_64[1] + 16
                    && waves_16_32_64[2] <= wave_cap
                    && chunks_by_d[2] <= chunks_by_d[1] + 6,
                format!(
                    "Cascade {id} disjoint expanding waves/chunks grew unboundedly: waves={waves_16_32_64:?}, chunks={chunks_by_d:?}"
                ),
            );
        }
        if id == "ctrl_lsb_radix" {
            rep.require(
                legs16_by_d[0] < legs16_by_d[1] && legs16_by_d[1] < legs16_by_d[2],
                format!("ctrl_lsb_radix skeleton legs did not grow with log d: {legs16_by_d:?}"),
            );
        }
        if id == "ctrl_lsb_radix" || id == "ctrl_localized_msb_bfly" {
            rep.require(
                waves_16_32_64[0] < waves_16_32_64[1]
                    && waves_16_32_64[1] < waves_16_32_64[2]
                    && chunks_by_d[0] < chunks_by_d[1]
                    && chunks_by_d[1] < chunks_by_d[2],
                format!(
                    "Superlinear control {id} waves/chunks did not grow with log d: waves={waves_16_32_64:?}, chunks={chunks_by_d:?}"
                ),
            );
        }
    }
    println!();
}

// ============================================================================
// Suite 3: Coarse Phase Profiles & Skeleton Legs per Scale (`§10.4` & `Problem 11.1`)
// ============================================================================

fn run_suite_3_phase_profiles(rep: &mut CheckReport) {
    println!("=== [Suite 3] Coarse Phase Profiles M_ph(floor(2^{{-s}} L)) & Multi-Scale Legs (Section 10.4, Problem 11.1) ===");
    let d = 128usize;
    let b = entry_bits(d); // b = 7
    let ids = [
        "c1_torus_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "ctrl_padded_c1",
        "ctrl_padded_c3",
        "ctrl_lsb_radix",
        "ctrl_localized_msb_bfly",
        "ctrl_u1_unitslope_bfly",
    ];

    println!(
        "  Coarse joint pass counts M_ph(2^{{-s}} L) at d={d}, b={b} (s = 0..7):"
    );
    println!(
        "  {:<25} {:>4} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>12}",
        "SCHEDULE", "k", "s=0", "s=1", "s=2", "s=3", "s=4", "s=5", "s=6", "s=7", "slope*lg(k+1)"
    );
    println!("  {}", "-".repeat(103));

    for id in ids {
        let sc = build_by_id(id, d, b).unwrap();
        let prof = coarse_phase_profile(&sc, 7);
        let counts: Vec<usize> = prof.iter().map(|x| x.2).collect();
        // Empirical slope `A_slope = (M_ph(s=6) - M_ph(s=1)) / 5.0` times `log_2(k + 1)`
        // compared against `Corollary 10.4`'s critical threshold `1/2`.
        let a_slope = (counts[6] as f64 - counts[1] as f64) / 5.0;
        let crit_prod = a_slope * ((sc.k + 1) as f64).log2();
        println!(
            "  {:<25} {:>4} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>12.3}",
            id,
            sc.k,
            counts[0],
            counts[1],
            counts[2],
            counts[3],
            counts[4],
            counts[5],
            counts[6],
            counts[7],
            crit_prod
        );
        if id == "c1_torus_cascade"
            || id == "c3_ten_entry_cascade"
            || id == "c4_no_overwrite_cascade"
        {
            rep.require(
                crit_prod > 0.5,
                format!("Section 10.4 cascade {id} did not sit above 1/2 slope threshold: {crit_prod:.3}"),
            );
        }
    }

    println!("\n  Total all-head skeleton legs r_j (input head included) at scale floor(2^{{-j}} L), d=128, b=1 (Problem 11.1):");
    println!(
        "  {:<25} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6}",
        "SCHEDULE", "j=1", "j=2", "j=3", "j=4", "j=5", "j=6", "j=7"
    );
    println!("  {}", "-".repeat(73));
    for id in [
        "c1_torus_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "ctrl_localized_msb_bfly",
        "ctrl_pinned_dfs_bfly",
    ] {
        let sc = build_by_id(id, 128, 1).unwrap();
        let legs = skeleton_legs_profile(&sc, 7);
        println!(
            "  {:<25} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6} {:>6}",
            id, legs[0].2, legs[1].2, legs[2].2, legs[3].2, legs[4].2, legs[5].2, legs[6].2
        );
    }
    println!();
}

// ============================================================================
// Suite 4: Interval-Forest Charges (`Problem 11.1`)
// ============================================================================

fn run_suite_4_interval_forests(rep: &mut CheckReport) {
    println!("=== [Suite 4] Closed Interval-Forest Charges Normalized by L (Problem 11.1) ===");
    println!(
        "  Part 4a: Dyadic scale sweep (`b = ceil(log_2 d)`, `A in 2^{{-3..8}} L`, `pairs (2^-3,2^-6)..(2^-5,2^-8)`):"
    );
    println!(
        "  {:<25} {:>4} {:>3} {:>10} {:>10} {:>11} {:>11} {:>11} {:>11}",
        "SCHEDULE",
        "d",
        "b",
        "1S_Exact",
        "1S_Trace",
        "2S_Loc_Ex",
        "2S_Loc_Tr",
        "2S_Opt_Ex",
        "2S_Opt_Tr"
    );
    println!("  {}", "-".repeat(103));

    let forest_ids = [
        "ctrl_localized_msb_bfly",
        "ctrl_pinned_dfs_bfly",
        "ctrl_lsb_radix",
        "ctrl_xor_butterfly",
        "ctrl_xor_pinned_dfs",
        "ctrl_xor_cascade_lintime",
        "c1_torus_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
    ];

    for id in forest_ids {
        let dims: &[usize] = if id == "c1_torus_cascade" || id == "c3_ten_entry_cascade" {
            &[32, 64, 128]
        } else {
            &[32, 64]
        };
        for &d in dims {
            let b = entry_bits(d);
            let sc = build_by_id(id, d, b).unwrap();
            let fs = best_paper_dyadic_interval_forest_charges(&sc);
            println!(
                "  {:<25} {:>4} {:>3} {:>10.4} {:>10.4} {:>11.4} {:>11.4} {:>11.4} {:>11.4}",
                id,
                d,
                b,
                fs.best_1scale_exact,
                fs.best_1scale_trace,
                fs.best_2scale_loc_exact,
                fs.best_2scale_loc_trace,
                fs.best_2scale_opt_exact,
                fs.best_2scale_opt_trace
            );

            if sc.kind == ComputationKind::BitVerifiedTransposer {
                rep.require(
                    fs.best_1scale_exact >= 1.0 - 1e-9
                        && fs.best_2scale_loc_exact >= 1.0 - 1e-9
                        && fs.best_2scale_opt_exact >= 1.0 - 1e-9,
                    format!("Problem 11.1 forest soundness violated (< L) on transposer {id} d={d}"),
                );
            }
            if d == 64 && (id == "ctrl_localized_msb_bfly" || id == "ctrl_pinned_dfs_bfly") {
                rep.require(
                    fs.best_1scale_exact <= 1.05,
                    format!(
                        "Localized transposer {id} did not achieve ~1.0L forest charge: {:.4}",
                        fs.best_1scale_exact
                    ),
                );
            }
            if d == 64 && id == "c1_torus_cascade" {
                rep.require(
                    (1.90..=2.15).contains(&fs.best_2scale_opt_exact),
                    format!(
                        "Problem 11.1 Cascade 1 forest charge expected ~2L at (d=64,b=6), got {:.4}",
                        fs.best_2scale_opt_exact
                    ),
                );
            }
            if d == 64 && id == "c3_ten_entry_cascade" {
                rep.require(
                    (2.60..=3.15).contains(&fs.best_2scale_opt_exact),
                    format!(
                        "Problem 11.1 Cascade 3 (`c3_ten_entry_cascade`) forest charge expected ~2.6-3.0L at (d=64,b=6), got {:.4}",
                        fs.best_2scale_opt_exact
                    ),
                );
            }
            if d == 128 && id == "c3_ten_entry_cascade" {
                rep.require(
                    (2.85..=3.15).contains(&fs.best_2scale_loc_exact)
                        && (2.55..=3.15).contains(&fs.best_2scale_opt_exact),
                    format!(
                        "Problem 11.1 Cascade 3 (`c3_ten_entry_cascade`) forest charge expected ~3L loc / ~2.6-3.0L opt at (d=128,b=7), got loc={:.4}, opt={:.4}",
                        fs.best_2scale_loc_exact, fs.best_2scale_opt_exact
                    ),
                );
            }
        }
    }

    println!(
        "\n  Part 4b: Extended sub-row sweep down to `A_1 = 1` at `d = 64, b = 1` (`still >> L` on all cascades):"
    );
    for id in [
        "ctrl_localized_msb_bfly",
        "c1_torus_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
    ] {
        let sc = build_by_id(id, 64, 1).unwrap();
        let fs = best_interval_forest_charges(&sc);
        println!(
            "    {:<25} (d=64,b=1,A_1>=1): 1S={:.4}L, 2S_Loc={:.4}L, 2S_Opt={:.4}L",
            id, fs.best_1scale_exact, fs.best_2scale_loc_exact, fs.best_2scale_opt_exact
        );
        if id == "ctrl_localized_msb_bfly" {
            rep.require(
                fs.best_2scale_opt_exact >= 1.0 - 1e-9,
                "Extended sweep violated >= L soundness on ctrl_localized_msb_bfly",
            );
        } else {
            rep.require(
                fs.best_2scale_opt_exact >= 1.80,
                format!(
                    "Extended sweep on cascade {id} fell below 1.80L: {:.4}",
                    fs.best_2scale_opt_exact
                ),
            );
            if id == "c3_ten_entry_cascade" {
                rep.note(format!(
                    "Problem 11.1 forest scale-grid note: on the paper's dyadic scale pairs `(2^-3,2^-6)..(2^-5,2^-8)` \
                     at `b = ceil(log_2 d)`, `c1_torus_cascade` charges ~2.00L and `c3_ten_entry_cascade` charges \
                     2.62L..2.98L (~3L); extending the sweep down to single-cell `A_1 = 1` at `b = 1` lowers \
                     `c3_ten_entry_cascade` to {:.4}L (still well above the `< 1.00L` threshold needed for an exclusion).",
                    fs.best_2scale_opt_exact
                ));
            }
        }
    }
    println!();
}

// ============================================================================
// Suite 5: Appendix A `"Crossings"` Column Audit (`Exact CL_W` vs `Sprint 43 Mix`)
// ============================================================================

fn run_suite_5_catalogue(rep: &mut CheckReport) {
    println!("=== [Suite 5] Appendix A 'Crossings' Column Audit (d=64, b=1; Row 16 also at d=16, b=4) ===");
    println!(
        "  {:<28} {:<11} {:>10} {:>10} {:>11} {:<12} {:<12}",
        "SCHEDULE_ID",
        "PAPER_COL",
        "CL_W_Min",
        "MixGT2W",
        "MixBandMin",
        "CL_W_LABEL",
        "MIXGT2W_LBL"
    );
    println!("  {}", "-".repeat(102));

    let rows: &[(&str, &str)] = &[
        ("cat_row01_direct_copy", "yes"),
        ("cat_row02_persistent_triangles", "yes"),
        ("cat_row03_one_pass_shear", "no"),
        ("cat_row07_unitslope", "small"),
        ("cat_row08_bounce", "small"),
        ("cat_row16_one_free_wave", "small (16)"),
        ("cat_row24_dyck_mscale", "no"),
        ("cat_row27_gis2_swept", "no"),
        ("cat_row28_gis2", "small"),
        ("cat_row29_gis2_gap", "small"),
        ("cat_row30_mirrored_dyadic", "small"),
        ("cat_row32_dyadic_fold", "no"),
        ("cat_row36_lifo_fanout", "no"),
        ("cat_row37_tapped_cascade", "no"),
    ];

    let classify_ratio = |zero_linear_hops: bool, min_ratio: f64| -> &'static str {
        if zero_linear_hops {
            "yes"
        } else if min_ratio <= 0.07 {
            "small"
        } else if min_ratio >= 0.25 {
            "no"
        } else {
            "mid(0.07..0.25)"
        }
    };

    for &(id, expected_col) in rows {
        let (d, b) = if id == "cat_row16_one_free_wave" {
            (16usize, 4usize)
        } else {
            (64usize, 1usize)
        };
        let sc = build_by_id(id, d, b).unwrap();
        let dag = DepGraph::from_schedule(&sc);
        let l = sc.len_bits();
        let two_w = (2 * d * b) as i64;
        let subpops = standard_subpopulations(d, b);

        // Theorem X quantifies over EVERY large output set `V_0`: a schedule is excluded (`"small"`)
        // iff `min_{V_0} |B_min(Out(V_0) -> crossings)| / |V_0| <= 0.07`, and survives (`"no"`) iff
        // that minimum is `>= 0.25`. Following `sprint43.rs`, evaluate `V_0` with `|V_0| <= L/2`.
        let cl_mask = crossing_lower_steps(&dag, two_w);
        let cl_empty = !cl_mask.iter().any(|&x| x);
        let mut min_cl_ratio = if cl_empty { 0.0 } else { 1.0f64 };
        if !cl_empty {
            for (_name, v0) in &subpops {
                if v0.is_empty() || v0.len() > l / 2 {
                    continue;
                }
                let cut = menger_min_vertex_cut(&sc, &dag, v0, &cl_mask).cut_size;
                let r = cut as f64 / (v0.len() as f64);
                if r < min_cl_ratio {
                    min_cl_ratio = r;
                }
            }
        }

        let mix_mask = legacy_sprint43_mix_gt2w(&sc, &dag);
        let mix_empty = !mix_mask.iter().any(|&x| x);
        let mut min_mix_gt2w = if mix_empty { 0.0 } else { 1.0f64 };
        if !mix_empty {
            for (_name, v0) in &subpops {
                if v0.is_empty() || v0.len() > l / 2 {
                    continue;
                }
                let r = match legacy_nonroot_separator_cut(&sc, &dag, v0, &mix_mask) {
                    Some(cut) => cut as f64 / (v0.len() as f64),
                    None => 1.0,
                };
                if r < min_mix_gt2w {
                    min_mix_gt2w = r;
                }
            }
        }

        let mut min_mix_band = if mix_empty { 0.0 } else { 1.0f64 };
        for div in [2usize, 4, 8] {
            let cap_v0 = l / div;
            let bmask = legacy_sprint43_mix_band(&sc, &dag, cap_v0 as i64);
            for (_name, v0) in &subpops {
                if v0.is_empty() || v0.len() > cap_v0 {
                    continue;
                }
                let r = match legacy_nonroot_separator_cut(&sc, &dag, v0, &bmask) {
                    Some(cut) => cut as f64 / (v0.len() as f64),
                    None => 1.0,
                };
                if r < min_mix_band {
                    min_mix_band = r;
                }
            }
        }

        // `"yes"` in Appendix A specifically means work heads stay within `O(b)` cells (0 >2W hops at all).
        let any_gt2w_hop = (0..sc.k).any(|j| {
            dag.revisits_by_tape[j]
                .iter()
                .any(|rv| rv.excursion > two_w)
        });
        let cl_label = if id == "cat_row16_one_free_wave" && min_cl_ratio <= 0.07 && any_gt2w_hop {
            "small (16)"
        } else {
            classify_ratio(!any_gt2w_hop && cl_empty, min_cl_ratio)
        };
        let mix_label =
            if id == "cat_row16_one_free_wave" && min_mix_gt2w <= 0.07 && any_gt2w_hop {
                "small (16)"
            } else {
                classify_ratio(!any_gt2w_hop && mix_empty, min_mix_gt2w)
            };

        println!(
            "  {:<28} {:<11} {:>10.4} {:>10.4} {:>11.4} {:<12} {:<12}",
            id, expected_col, min_cl_ratio, min_mix_gt2w, min_mix_band, cl_label, mix_label
        );

        match expected_col {
            "yes" => {
                rep.require(
                    !any_gt2w_hop && cl_empty && mix_empty,
                    format!("Appendix A 'yes' row {id} made >2W revisits"),
                );
            }
            "no" => {
                rep.require(
                    min_cl_ratio >= 0.25 && min_mix_gt2w >= 0.25,
                    format!(
                        "Appendix A 'no' row {id} fell below 0.25: cl={min_cl_ratio:.4}, mix_gt2w={min_mix_gt2w:.4}"
                    ),
                );
            }
            "small" | "small (16)" => {
                rep.require(
                    min_cl_ratio <= 0.07 || min_mix_gt2w <= 0.07 || min_mix_band <= 0.07,
                    format!(
                        "Appendix A '{expected_col}' row {id} exceeded 0.07 on all three variants: \
                         cl={min_cl_ratio:.4}, mix_gt2w={min_mix_gt2w:.4}, mix_band={min_mix_band:.4}"
                    ),
                );
            }
            _ => unreachable!(),
        }

        if cl_label != expected_col || mix_label != expected_col || (expected_col == "no" && min_mix_band <= 0.07) {
            rep.note(format!(
                "Appendix A `{id}` (`{expected_col}`): exact `CL_W` + `IsMengerVertexCut` gives min ratio \
                 {min_cl_ratio:.4} (`{cl_label}`, `|CL_W| = {}`), uncapped Sprint 43 `Mix_{{>2W}}` gives \
                 {min_mix_gt2w:.4} (`{mix_label}`), and banded Sprint 43 `Mix_eta` (`eta in {{1/2,1/4,1/8}}`) \
                 gives {min_mix_band:.4}.",
                cl_mask.iter().filter(|&&x| x).count()
            ));
        }
    }
    println!();
}

fn run_all_checks() -> Result<(), String> {
    let t0 = Instant::now();
    let mut rep = CheckReport::default();

    run_suite_0_foundations(&mut rep);
    run_suite_1_crossings(&mut rep);
    run_suite_2_skeletons_and_waves(&mut rep);
    run_suite_3_phase_profiles(&mut rep);
    run_suite_4_interval_forests(&mut rep);
    run_suite_5_catalogue(&mut rep);

    println!("=== Probe-Simplification & Boundary Audit Notes ===");
    if rep.notes.is_empty() {
        println!("  (none)");
    } else {
        for (i, n) in rep.notes.iter().enumerate() {
            println!("  {}. {}", i + 1, n);
        }
    }
    println!(
        "\nCompleted full verification suite in {:.2}s ({} failures).",
        t0.elapsed().as_secs_f64(),
        rep.failures.len()
    );

    if rep.failures.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "{} verification check(s) failed",
            rep.failures.len()
        ))
    }
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let cmd = args.first().map(|s| s.as_str()).unwrap_or("check");

    let res = match cmd {
        "check" => run_all_checks(),
        "list" => {
            cmd_list();
            Ok(())
        }
        "export" => cmd_export(&args[1..]),
        "crossings" => {
            let mut rep = CheckReport::default();
            run_suite_1_crossings(&mut rep);
            if rep.failures.is_empty() {
                Ok(())
            } else {
                Err(format!("{} failure(s)", rep.failures.len()))
            }
        }
        "skeletons" => {
            let mut rep = CheckReport::default();
            run_suite_2_skeletons_and_waves(&mut rep);
            if rep.failures.is_empty() {
                Ok(())
            } else {
                Err(format!("{} failure(s)", rep.failures.len()))
            }
        }
        "phases" => {
            let mut rep = CheckReport::default();
            run_suite_3_phase_profiles(&mut rep);
            if rep.failures.is_empty() {
                Ok(())
            } else {
                Err(format!("{} failure(s)", rep.failures.len()))
            }
        }
        "forests" => {
            let mut rep = CheckReport::default();
            run_suite_4_interval_forests(&mut rep);
            if rep.failures.is_empty() {
                Ok(())
            } else {
                Err(format!("{} failure(s)", rep.failures.len()))
            }
        }
        "catalogue" => {
            let mut rep = CheckReport::default();
            run_suite_5_catalogue(&mut rep);
            if rep.failures.is_empty() {
                Ok(())
            } else {
                Err(format!("{} failure(s)", rep.failures.len()))
            }
        }
        "-h" | "--help" | "help" => {
            print_usage();
            Ok(())
        }
        other => {
            print_usage();
            Err(format!("Unknown subcommand '{other}'"))
        }
    };

    if let Err(e) = res {
        eprintln!("ERROR: {e}");
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{ScheduleBuilder, StepOp};

    #[test]
    fn waiting_on_cell_makes_no_revisit() {
        // d = 2, b = 1 -> L = 4. Work head stays on cell 0 for 3 steps, moves to 1, stays on 1, returns to 0.
        let mut sb = ScheduleBuilder::new(
            "test_wait",
            "Wait test",
            2,
            1,
            1,
            ComputationKind::ExplicitNonTransposer,
        );
        sb.step_with_op(1, &[0], true, StepOp::EmitInput); // t=0: y=0 -> y=0
        sb.step_with_op(1, &[0], true, StepOp::EmitInput); // t=1: y=0 -> y=0 (wait!)
        sb.step_with_op(1, &[1], true, StepOp::EmitInput); // t=2: y=0 -> y=1 (leave 0 after t=2)
        sb.step_with_op(0, &[0], false, StepOp::PassThrough); // t=3: y=1 -> y=1 (wait!)
        sb.step_with_op(0, &[-1], false, StepOp::PassThrough); // t=4: y=1 -> y=0
        sb.step_with_op(0, &[0], true, StepOp::EmitInput); // t=5: y=0 (return to 0 at t=5? No, returned at t=5!)
        let sched = sb.finish();
        let dag = DepGraph::from_schedule(&sched);
        dag.verify_against_bruteforce(&sched);

        // Only ONE true revisit exists: leaving cell 0 after p=2 and returning at u=5!
        assert_eq!(dag.revisits_by_tape[0].len(), 1);
        let rev = dag.revisits_by_tape[0][0];
        assert_eq!((rev.p, rev.u, rev.cell, rev.excursion), (2, 5, 0, 1));
    }

    #[test]
    fn strict_no_overwrite_cascade_has_unit_write_count() {
        for d in [4usize, 16, 32] {
            let sc3 = build_by_id("c3_ten_entry_cascade", d, 1).unwrap();
            assert!(sc3.max_work_cell_entries() <= 10);

            let sc4 = build_by_id("c4_no_overwrite_cascade", d, 1).unwrap();
            assert_eq!(sc4.max_active_writes_per_cell(), 1);
            assert!(sc4.max_work_cell_entries() <= 9);
        }
    }

    #[test]
    fn exporters_emit_expected_fields() {
        let sc = build_by_id("ctrl_lsb_radix", 4, 1).unwrap();
        let mut csv_buf = Vec::new();
        sc.write_csv(&mut csv_buf).unwrap();
        let csv_str = String::from_utf8(csv_buf).unwrap();
        assert!(csv_str.starts_with(
            "step,in_pos,in_move,in_scanned_cell,in_loaded,work_0_pos,work_0_move,work_0_write,work_1_pos,work_1_move,work_1_write,append_out_idx,append_target_input\n"
        ));
        assert_eq!(csv_str.lines().count(), sc.horizon() + 1);

        let mut json_buf = Vec::new();
        sc.write_json(&mut json_buf).unwrap();
        let json_str = String::from_utf8(json_buf).unwrap();
        assert!(json_str.contains("\"computation_kind\": \"actual_transpose_bit_verified\""));
        assert!(json_str.contains("\"target_input\":"));
    }
}
