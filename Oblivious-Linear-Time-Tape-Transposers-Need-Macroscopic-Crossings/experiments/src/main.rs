//! Reproducible experiments CLI and verification suite (`paper16-experiments`) for
//! "Oblivious Linear-Time Tape Transposers Need Macroscopic Crossings".
//!
//! Subcommands:
//!   check                                    Recompute every quoted figure and assert invariants
//!   list                                     List all schedule generators and computation kinds
//!   export <id> <d> <b> <csv|json> [path]    Export full time-indexed schedule (stdout or file)
//!   crossings                                Run Remark 5.8 crossing min-cut & E=L suite
//!   skeletons                                Run Remarks 6.8 & 10.1 skeleton & single-leg suite
//!   phases                                   Run Section 10.4 coarse phase-profile suite
//!   forests                                  Run Problem 11.1 1-scale & 2-scale forest suite
//!   catalogue                                Run Appendix A "Crossings" column & control suite

mod checkers;
mod model;
mod schedules;

use std::env;
use std::fs::File;
use std::io::{self, BufWriter};
use std::process;
use std::time::Instant;

use checkers::{
    analyze_skeleton_and_single_leg_expansion, best_interval_forest_charges,
    best_paper_dyadic_interval_forest_charges, certified_acyclic_upper_bound, coarse_phase_profile,
    crossing_lower_steps, crossing_lower_steps_bruteforce, extract_ball_avoid_relation,
    extract_tape_skeleton, legacy_banded_mix_steps, legacy_mix_gt2w_steps,
    legacy_nonroot_separator_cut, menger_min_vertex_cut, skeleton_legs_profile,
    standard_subpopulations,
};
use model::{entry_bits, ComputationKind, DepGraph};
use schedules::{build_by_id, ALL_SPECS};

#[derive(Default)]
struct CheckReport {
    failures: Vec<String>,
}

impl CheckReport {
    fn require(&mut self, cond: bool, msg: impl Into<String>) {
        if !cond {
            let s = msg.into();
            eprintln!("  [FAIL] {s}");
            self.failures.push(s);
        }
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
        "{:<28} {:<4} {:<31} {:<12} {}",
        "SCHEDULE_ID", "k", "COMPUTATION_KIND", "DOMAIN", "PAPER_REF"
    );
    println!("{}", "-".repeat(122));
    for s in ALL_SPECS {
        println!(
            "{:<28} {:<4} {:<31} {:<12} {}\n    {}",
            s.id,
            s.k_tapes,
            s.kind.as_str(),
            s.domain.label(s.min_d),
            s.paper_ref,
            s.title
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
// Suite 0: Exact DepStep Check, Exact-Basis Bit-Verified Transposers & Cell Caps
// ============================================================================

fn run_suite_0_foundations(rep: &mut CheckReport) {
    println!("=== [Suite 0] Exact DepStep Model, Unit-Basis Transposers & Cascade Cell Caps ===");

    // 0a. Nested-loop reference check of `DepGraph::from_schedule` & `crossing_lower_steps` at d = 4.
    let bf_ids_d4 = [
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c4_shared_w01_probe",
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
                format!("CL_H mismatch vs reference check on {id} at thresh={thresh}"),
            );
        }
    }
    println!(
        "  [OK] DepGraph::from_schedule & crossing_lower_steps match reference nested-loop checks on {} schedules.",
        bf_ids_d4.len()
    );

    // 0b. Exact F_2-basis verification (zero vector + all L unit vectors) on all 7 transpose controls.
    for spec in ALL_SPECS {
        if spec.kind == ComputationKind::BitVerifiedTransposer {
            for &(d, b) in &[(16usize, 4usize), (32, 1)] {
                let sc = build_by_id(spec.id, d, b).unwrap();
                sc.verify_transposer_exact_basis();
            }
            println!(
                "  [OK] Bit-verified transposer {:<26} exact on 0 and all L unit vectors at (16,4) & (32,1).",
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

        let sc4_pr = build_by_id("c4_shared_w01_probe", d, 1).unwrap();
        let ent4_pr = sc4_pr.max_work_cell_entries();
        if d == 64 {
            println!(
                "  [OK] Cascade cell caps at d=64, b=1: c3_ten_entry_cascade max_entries={ent3} (<=10); \
                 c4_no_overwrite_cascade max_writes={wr4} (==1), max_entries={ent4}; \
                 c4_shared_w01_probe (historical comparator) max_entries={ent4_pr}."
            );
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

    let cascades_and_comparator = [
        "c1_torus_cascade",
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c5_comb_fanout",
        "c4_shared_w01_probe",
    ];

    for id in cascades_and_comparator {
        let is_five_cascade = id != "c4_shared_w01_probe";
        for &d in &[32usize, 64, 128] {
            let b = 1usize;
            let l = d * d * b;
            let w = d * b;
            let sc = build_by_id(id, d, b).unwrap();
            let dag = DepGraph::from_schedule(&sc);
            let subpops = standard_subpopulations(d, b);

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

            // Remark 5.8: among the five cascades of Section 10.3, exactly two (Cascades 3 and 5)
            // make no crossings of excursion > L; the historical comparator `c4_shared_w01_probe`
            // also makes none because it shares `[L, 2L)` on `w_0, w_1`.
            let expect_empty_at_l = matches!(
                id,
                "c3_ten_entry_cascade" | "c5_comb_fanout" | "c4_shared_w01_probe"
            );
            rep.require(
                (cl_l_cnt == 0) == expect_empty_at_l,
                format!(
                    "Remark 5.8 E=L crossing-emptiness mismatch on {id} at d={d}: |CL_{{L/2}}|={cl_l_cnt}"
                ),
            );

            if d == 64 && cl_l_cnt == 0 {
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
                if is_five_cascade {
                    if id == "c3_ten_entry_cascade" {
                        rep.require(
                            (0.24..=0.26).contains(&ubs[3].1),
                            format!(
                                "Remark 5.8 Cascade 3 D=32 acyclic UB expected ~0.25L at d=64, got {:.4}",
                                ubs[3].1
                            ),
                        );
                    } else if id == "c5_comb_fanout" {
                        rep.require(
                            (0.07..=0.09).contains(&ubs[3].1),
                            format!(
                                "Remark 5.8 Cascade 5 D=32 acyclic UB expected ~0.08L at d=64, got {:.4}",
                                ubs[3].1
                            ),
                        );
                    }
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
// Suite 2: Running Times, Skeletons & Single-Leg Expansion (`Remarks 6.8 & 10.1`)
// ============================================================================

fn run_suite_2_skeletons(rep: &mut CheckReport) {
    println!("=== [Suite 2] Running Times, Skeletons & Single-Leg Expansion (Remarks 6.8 & 10.1) ===");

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
    println!(
        "  Measured T/L across Cascades 1-5 for d in {{32,64,128}}, b=1: min={min_tl:.2}, max={max_tl:.2}"
    );
    rep.require(
        (17.0..18.0).contains(&min_tl) && (89.0..90.0).contains(&max_tl),
        format!(
            "Remark 10.1 cascade running-time span expected between about 17L and 90L, got [{min_tl:.2}L, {max_tl:.2}L]"
        ),
    );

    // 2b. Skeleton stability at `Lambda_* = floor(L/6) + 1` and single-leg expansion.
    println!(
        "\n  {:<25} {:>4} {:<24} {:>8} {:>15} {:>13} {:>13}",
        "SCHEDULE",
        "d",
        "SKEL_W0(L/6+1)",
        "TOT_LEGS",
        "1LEG(L/6+1,2L*)",
        "1LEG(L/6+1,W)",
        "1LEG(L/16,L/8)"
    );
    println!("  {}", "-".repeat(109));

    let skel_targets = [
        "c1_torus_cascade",
        "c2_bfly_cascade",
        "c3_ten_entry_cascade",
        "c4_no_overwrite_cascade",
        "c5_comb_fanout",
        "c4_shared_w01_probe",
        "cat_row03_one_pass_shear",
        "cat_row24_dyck_mscale",
        "ctrl_lsb_radix",
        "ctrl_localized_msb_bfly",
        "ctrl_pinned_dfs_bfly",
    ];

    for id in skel_targets {
        let mut skel6_by_d: Vec<Vec<Vec<bool>>> = Vec::new();
        let mut legs6_by_d: Vec<usize> = Vec::new();

        for &d in &[32usize, 64, 128] {
            let sc = build_by_id(id, d, 1).unwrap();
            let dag = DepGraph::from_schedule(&sc);
            let l = sc.len_bits();
            let w = d;

            let lam16 = (l / 16) as i64;
            let h8 = (l / 8) as i64;
            let s16 = analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam16, h8);

            // `Lambda_* = floor(L/6) + 1` ("scale about L/6") at both Theorem S's exact
            // `H = 2 * Lambda_*` and row-scale `H = W`.
            let lam6 = (l / 6 + 1) as i64;
            let s6_2lam = analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam6, 2 * lam6);
            let s6_w = analyze_skeleton_and_single_leg_expansion(&sc, &dag, lam6, w as i64);

            let sk6_tapes: Vec<Vec<bool>> = (0..sc.k)
                .map(|j| extract_tape_skeleton(&sc.work_pos[j], lam6).steps)
                .collect();
            let tot_legs6 = s6_w.total_legs;
            let (win_j, _win_leg) = s6_w.best_tape_and_leg;
            rep.require(win_j < sc.k, format!("Invalid winning tape index on {id}"));
            legs6_by_d.push(tot_legs6);
            skel6_by_d.push(sk6_tapes);

            println!(
                "  {:<25} {:>4} {:<24} {:>8} {:>15.4} {:>13.4} {:>13.4}",
                id,
                d,
                s6_w.per_tape_legs[0],
                tot_legs6,
                s6_2lam.max_single_leg_cut_ratio,
                s6_w.max_single_leg_cut_ratio,
                s16.max_single_leg_cut_ratio
            );

            // Remarks 6.8 & 10.1: single-leg linear expansion on Cascades 1-5 (`== 1.0` at
            // `H = W`, and linear `>= 2/3 - o(1)` at Theorem S's exact `H = 2*Lambda_*` where
            // `2H = 4*Lambda_* ~ 2L/3`), and linear expansion on `cat_row03_one_pass_shear` and
            // `cat_row24_dyck_mscale`.
            if five_cascades.contains(&id) || id == "c4_shared_w01_probe" {
                let ok_2lam = match id {
                    "c3_ten_entry_cascade" => s6_2lam.max_single_leg_cut_ratio >= 0.999,
                    "c5_comb_fanout" => (0.66..=0.67).contains(&s6_2lam.max_single_leg_cut_ratio),
                    _ => (s6_2lam.max_single_leg_cut_ratio - 1.0).abs() < 1e-9,
                };
                rep.require(
                    ok_2lam
                        && (s6_w.max_single_leg_cut_ratio - 1.0).abs() < 1e-9
                        && s16.max_single_leg_cut_ratio >= 0.85,
                    format!(
                        "Cascade {id} failed single-leg linear expansion at d={d}: \
                         (L/6+1,2L*)={:.4}, (L/6+1,W)={:.4}, (L/16,L/8)={:.4}",
                        s6_2lam.max_single_leg_cut_ratio,
                        s6_w.max_single_leg_cut_ratio,
                        s16.max_single_leg_cut_ratio
                    ),
                );
            }
            if id == "cat_row03_one_pass_shear" || id == "cat_row24_dyck_mscale" {
                rep.require(
                    s16.any_crossing_capable
                        && s16.max_single_leg_cut_ratio >= 0.35
                        && s6_w.max_single_leg_cut_ratio >= 0.50,
                    format!(
                        "Remarks 6.8/10.1 single-leg expansion check failed on {id} at d={d}: \
                         (L/16,L/8)={:.4}, (L/6+1,W)={:.4}",
                        s16.max_single_leg_cut_ratio, s6_w.max_single_leg_cut_ratio
                    ),
                );
            }
            if id == "ctrl_pinned_dfs_bfly" {
                rep.require(
                    (0.66..=0.67).contains(&s6_2lam.max_single_leg_cut_ratio)
                        && (s6_w.max_single_leg_cut_ratio - 1.0).abs() < 1e-9,
                    format!(
                        "Pinned DFS butterfly failed single-leg expansion at Lambda=L/6+1 d={d}: \
                         2*Lambda={:.4}, W={:.4}",
                        s6_2lam.max_single_leg_cut_ratio, s6_w.max_single_leg_cut_ratio
                    ),
                );
            }
        }

        // Strict skeleton stability assertions matching Remarks 6.8 & 10.1:
        // - Identical across d = 32, 64, 128 on Cascade 5, `cat_row03_one_pass_shear`, and `ctrl_pinned_dfs_bfly`.
        // - Within 8 legs and <= 13% ("within 8 legs (about 12%)") across d = 32, 64, 128 on Cascades 1-4.
        if id == "c5_comb_fanout"
            || id == "cat_row03_one_pass_shear"
            || id == "ctrl_pinned_dfs_bfly"
        {
            rep.require(
                skel6_by_d[0] == skel6_by_d[1] && skel6_by_d[1] == skel6_by_d[2],
                format!(
                    "{id} skeleton at Lambda=floor(L/6)+1 was not identical across d=32,64,128: legs={legs6_by_d:?}"
                ),
            );
        }
        if matches!(
            id,
            "c1_torus_cascade"
                | "c2_bfly_cascade"
                | "c3_ten_entry_cascade"
                | "c4_no_overwrite_cascade"
        ) {
            let min_legs = *legs6_by_d.iter().min().unwrap();
            let max_legs = *legs6_by_d.iter().max().unwrap();
            let diff = max_legs - min_legs;
            let rel = diff as f64 / (min_legs.max(1) as f64);
            rep.require(
                diff <= 8 && rel <= 0.13,
                format!(
                    "Cascade {id} skeleton legs at Lambda=floor(L/6)+1 varied by more than 8 legs / 13%: \
                     legs={legs6_by_d:?} (diff={diff}, rel={:.3})",
                    rel
                ),
            );
        }
        if id == "ctrl_lsb_radix" {
            rep.require(
                legs6_by_d[0] < legs6_by_d[1] && legs6_by_d[1] < legs6_by_d[2],
                format!("ctrl_lsb_radix skeleton legs did not grow with log d: {legs6_by_d:?}"),
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

    println!("  Coarse joint pass counts M_ph(2^{{-s}} L) at d={d}, b={b} (s = 0..7):");
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
        if matches!(
            id,
            "c1_torus_cascade" | "c3_ten_entry_cascade" | "c4_no_overwrite_cascade"
        ) {
            rep.require(
                (25.0..=40.0).contains(&crit_prod),
                format!(
                    "Section 10.4 cascade {id} slope product expected in [25, 40] at (d=128,b=7), got {crit_prod:.3}"
                ),
            );
        }
        if sc.kind == ComputationKind::BitVerifiedTransposer {
            rep.require(
                crit_prod > 0.5,
                format!(
                    "Section 10.4 superlinear transposer {id} violated > 0.5 slope bound: {crit_prod:.3}"
                ),
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
        if sc.kind == ComputationKind::BitVerifiedTransposer {
            rep.require(
                legs[6].2 >= 700 && legs[6].2 >= (legs[5].2 * 19) / 10,
                format!(
                    "Localized butterfly {id} did not exhibit exponential r_j doubling: j=6 got {}, j=7 got {}",
                    legs[5].2, legs[6].2
                ),
            );
        } else {
            let linear_steps = legs
                .windows(2)
                .all(|w| w[1].2 >= w[0].2 && w[1].2 - w[0].2 <= 40);
            rep.require(
                linear_steps && legs[6].2 <= 240,
                format!(
                    "Cascade {id} r_j violated linear O(j) leg growth: {:?}",
                    legs.iter().map(|x| x.2).collect::<Vec<_>>()
                ),
            );
        }
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
            if id == "c1_torus_cascade" {
                rep.require(
                    (1.95..=2.05).contains(&fs.best_1scale_exact)
                        && (1.95..=2.05).contains(&fs.best_2scale_opt_exact),
                    format!(
                        "Problem 11.1 Cascade 1 dyadic forest charge expected ~2L at (d={d},b={b}), got 1S={:.4}, 2S_Opt={:.4}",
                        fs.best_1scale_exact, fs.best_2scale_opt_exact
                    ),
                );
            }
            if id == "c3_ten_entry_cascade" {
                rep.require(
                    (2.45..=2.60).contains(&fs.best_1scale_exact)
                        && (2.55..=3.05).contains(&fs.best_2scale_opt_exact)
                        && (2.90..=3.05).contains(&fs.best_2scale_loc_exact),
                    format!(
                        "Problem 11.1 Cascade 3 dyadic forest charge expected ~2.5L (1S) and 2.6-3.0L (2S) at (d={d},b={b}), \
                         got 1S={:.4}, 2S_Loc={:.4}, 2S_Opt={:.4}",
                        fs.best_1scale_exact, fs.best_2scale_loc_exact, fs.best_2scale_opt_exact
                    ),
                );
            }
            if id == "c4_no_overwrite_cascade" {
                rep.require(
                    (3.99..=4.01).contains(&fs.best_1scale_exact)
                        && (3.99..=4.01).contains(&fs.best_2scale_opt_exact),
                    format!(
                        "Problem 11.1 Cascade 4 dyadic forest charge expected 4L at (d={d},b={b}), got 1S={:.4}, 2S_Opt={:.4}",
                        fs.best_1scale_exact, fs.best_2scale_opt_exact
                    ),
                );
            }
        }
    }

    println!(
        "\n  Part 4b: Extended sub-row sweep down to single cells (`A_1 = 1`) at `d = 64, b = 1`:"
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
                fs.best_1scale_exact >= 1.0 - 1e-9 && fs.best_2scale_opt_exact >= 1.0 - 1e-9,
                "Extended sweep violated >= L soundness on ctrl_localized_msb_bfly",
            );
        } else if id == "c1_torus_cascade" {
            rep.require(
                (1.62..=1.64).contains(&fs.best_1scale_exact) && fs.best_2scale_opt_exact >= 1.62,
                format!(
                    "Problem 11.1 Cascade 1 single-cell sweep expected ~1.63L (1S), got 1S={:.4}, 2S_Opt={:.4}",
                    fs.best_1scale_exact, fs.best_2scale_opt_exact
                ),
            );
        } else if id == "c3_ten_entry_cascade" {
            rep.require(
                (1.63..=1.65).contains(&fs.best_1scale_exact) && fs.best_2scale_opt_exact >= 1.63,
                format!(
                    "Problem 11.1 Cascade 3 single-cell sweep expected ~1.64L (1S), got 1S={:.4}, 2S_Opt={:.4}",
                    fs.best_1scale_exact, fs.best_2scale_opt_exact
                ),
            );
        } else if id == "c4_no_overwrite_cascade" {
            rep.require(
                (3.99..=4.01).contains(&fs.best_1scale_exact)
                    && (3.99..=4.01).contains(&fs.best_2scale_opt_exact),
                format!(
                    "Problem 11.1 Cascade 4 single-cell sweep expected 4.00L, got 1S={:.4}, 2S_Opt={:.4}",
                    fs.best_1scale_exact, fs.best_2scale_opt_exact
                ),
            );
        }
    }
    println!();
}

// ============================================================================
// Suite 5: Appendix A `"Crossings"` Column & Superlinear Control Audit
// ============================================================================

fn run_suite_5_catalogue(rep: &mut CheckReport) {
    println!("=== [Suite 5] Appendix A 'Crossings' Column Audit (d=64, b=1; Row 16 at d=16, b=4) ===");
    println!(
        "  {:<28} {:<11} {:>10} {:>12} {:>12} {:<12}",
        "SCHEDULE_ID",
        "PAPER_COL",
        "CL_W_Min",
        "DiagMixGT2W",
        "DiagMixBand",
        "CL_W_LABEL"
    );
    println!("  {}", "-".repeat(91));

    let rows: &[(&str, &str)] = &[
        ("cat_row01_direct_copy", "yes"),
        ("cat_row02_persistent_triangles", "yes"),
        ("cat_row03_one_pass_shear", "no"),
        ("cat_row07_unitslope", "no"),
        ("cat_row08_bounce", "no"),
        ("cat_row16_one_free_wave", "small (16)"),
        ("cat_row24_dyck_mscale", "no"),
        ("cat_row27_gis2_swept", "no"),
        ("cat_row28_gis2", "small"),
        ("cat_row29_gis2_gap", "small"),
        ("cat_row30_mirrored_dyadic", "no"),
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

        // Exact paper definition (`Definition 2.2` + `Definition 2.4`): minimum vertex cut
        // `|B_min(Out(V_0) -> CL_W)| / |V_0|` across tested output sets `V_0` with `|V_0| <= L/2`.
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

        // Labelled legacy diagnostics only (NOT used as pass criteria).
        let mix_mask = legacy_mix_gt2w_steps(&sc, &dag);
        let mix_empty = !mix_mask.iter().any(|&x| x);
        let mut diag_mix_gt2w = if mix_empty { 0.0 } else { 1.0f64 };
        if !mix_empty {
            for (_name, v0) in &subpops {
                if v0.is_empty() || v0.len() > l / 2 {
                    continue;
                }
                let r = match legacy_nonroot_separator_cut(&sc, &dag, v0, &mix_mask) {
                    Some(cut) => cut as f64 / (v0.len() as f64),
                    None => 1.0,
                };
                if r < diag_mix_gt2w {
                    diag_mix_gt2w = r;
                }
            }
        }

        let mut diag_mix_band = if mix_empty { 0.0 } else { 1.0f64 };
        for div in [2usize, 4, 8] {
            let cap_v0 = l / div;
            let bmask = legacy_banded_mix_steps(&sc, &dag, cap_v0 as i64);
            for (_name, v0) in &subpops {
                if v0.is_empty() || v0.len() > cap_v0 {
                    continue;
                }
                let r = match legacy_nonroot_separator_cut(&sc, &dag, v0, &bmask) {
                    Some(cut) => cut as f64 / (v0.len() as f64),
                    None => 1.0,
                };
                if r < diag_mix_band {
                    diag_mix_band = r;
                }
            }
        }

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

        println!(
            "  {:<28} {:<11} {:>10.4} {:>12.4} {:>12.4} {:<12}",
            id, expected_col, min_cl_ratio, diag_mix_gt2w, diag_mix_band, cl_label
        );

        // Strict assertion: `CL_W` + `IsMengerVertexCut` ALONE must match the paper's column!
        rep.require(
            cl_label == expected_col,
            format!(
                "Appendix A 'Crossings' mismatch on {id}: expected '{expected_col}', \
                 exact CL_W gave '{cl_label}' (min_cl_ratio={min_cl_ratio:.4}, any_gt2w_hop={any_gt2w_hop})"
            ),
        );
    }

    // Part 5b: Crossing separator check on all 7 explicit omega(L) transposers (`Appendix A` final paragraph).
    println!("\n  Part 5b: Crossing separator check on all 7 bit-verified omega(L) transposers (d=32, b=1):");
    for spec in ALL_SPECS {
        if spec.kind != ComputationKind::BitVerifiedTransposer {
            continue;
        }
        let sc = build_by_id(spec.id, 32, 1).unwrap();
        let dag = DepGraph::from_schedule(&sc);
        let l = sc.len_bits();
        let two_w = (2 * 32) as i64;
        let subpops = standard_subpopulations(32, 1);
        let cl_mask = crossing_lower_steps(&dag, two_w);
        let cl_cnt = cl_mask.iter().filter(|&&x| x).count();
        let mut min_cl_ratio = if cl_cnt == 0 { 0.0 } else { 1.0f64 };
        if cl_cnt > 0 {
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
        println!(
            "    {:<28} T/L={:>6.2}  |CL_W|={:>7}  CL_W_Min={:.4}",
            spec.id,
            sc.horizon() as f64 / (l as f64),
            cl_cnt,
            min_cl_ratio
        );
        rep.require(
            (min_cl_ratio - 1.0).abs() < 1e-9,
            format!(
                "Expected CL_W separator ratio 1.0 on omega(L) transposer {}, got {:.4}",
                spec.id, min_cl_ratio
            ),
        );
    }
    println!();
}

fn run_all_checks() -> Result<(), String> {
    let t0 = Instant::now();
    let mut rep = CheckReport::default();

    run_suite_0_foundations(&mut rep);
    run_suite_1_crossings(&mut rep);
    run_suite_2_skeletons(&mut rep);
    run_suite_3_phase_profiles(&mut rep);
    run_suite_4_interval_forests(&mut rep);
    run_suite_5_catalogue(&mut rep);

    println!(
        "Completed full verification suite in {:.2}s ({} failures).",
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
            run_suite_2_skeletons(&mut rep);
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
    use crate::model::{tpos, ScheduleBuilder, StepOp};
    use crate::schedules::DomainRule;

    #[test]
    fn waiting_on_cell_makes_no_revisit() {
        let mut sb = ScheduleBuilder::new(
            "test_wait",
            "Wait test",
            2,
            1,
            1,
            ComputationKind::ExplicitNonTransposer,
        );
        sb.step_with_op(1, &[0], true, StepOp::EmitInput); // t=0: y=0 -> y=0
        sb.step_with_op(1, &[0], true, StepOp::EmitInput); // t=1: y=0 -> y=0 (wait)
        sb.step_with_op(1, &[1], true, StepOp::EmitInput); // t=2: y=0 -> y=1 (leave 0 after t=2)
        sb.step_with_op(0, &[0], false, StepOp::PassThrough); // t=3: y=1 -> y=1 (wait)
        sb.step_with_op(0, &[-1], false, StepOp::PassThrough); // t=4: y=1 -> y=0
        sb.step_with_op(0, &[0], true, StepOp::EmitInput); // t=5: y=0 (return to 0 at t=5)
        let sched = sb.finish();
        let dag = DepGraph::from_schedule(&sched);
        dag.verify_against_bruteforce(&sched);

        assert_eq!(dag.revisits_by_tape[0].len(), 1);
        let rev = dag.revisits_by_tape[0][0];
        assert_eq!((rev.p, rev.u, rev.cell, rev.excursion), (2, 5, 0, 1));
    }

    #[test]
    fn ball_relation_exempts_root_even_when_root_in_cut() {
        // Output r=0 (target p = tpos(2,1,0) = 0) is emitted at t=1 while scanning input cell 0,
        // and state edge 1 -> 0 reaches t=0 scanning input cell 0.
        // If t=1 lies in `cut_mask` while t=0 does not, `GFree` (`Definition 2.5`) exempts the
        // root `t_r = 1`, so both t=1 and t=0 remain reachable within radius 1!
        let sc = build_by_id("cat_row01_direct_copy", 2, 1).unwrap();
        let dag = DepGraph::from_schedule(&sc);
        let mut cut = vec![false; dag.t_len];
        let root0 = sc.append_times[0];
        let root1 = sc.append_times[1];
        cut[root0] = true;
        cut[root1] = true;

        let rel_d0 = extract_ball_avoid_relation(&sc, &dag, 0, &cut);
        // At radius 0, root `t_r` itself is reached (exempt from `cut`), scanning input cell `r`.
        assert_eq!(rel_d0[tpos(2, 1, 0)], vec![0]);
        assert_eq!(rel_d0[tpos(2, 1, 1)], vec![1]);

        // Blocking an interior non-root step DOES cut paths through it:
        let mut cut_interior = vec![false; dag.t_len];
        cut_interior[root0] = true; // root0 is interior on the path from root1 = root0 + 1 to root0!
        let rel_d1 = extract_ball_avoid_relation(&sc, &dag, 1, &cut_interior);
        // From root1 (`r = 1`, `p = tpos(2,1,1) = 2`), `root1` is exempt so cell `1` is reached,
        // while `root0` is NOT the root for `r = 1` and lies in `cut_interior`, so cell `0` is blocked!
        assert_eq!(rel_d1[tpos(2, 1, 1)], vec![1]);
    }

    #[test]
    fn all_schedule_specs_match_domain_without_panicking() {
        for spec in ALL_SPECS {
            for d in [1usize, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 64] {
                if spec.k_tapes >= 9 && d == 64 {
                    // Tested at d=64 below once; skip nothing — 64 is fast (~5ms).
                }
                let in_domain = d >= spec.min_d
                    && match spec.domain {
                        DomainRule::Any => true,
                        DomainRule::EvenOnly => d % 2 == 0,
                        DomainRule::PowerOfTwo => d.is_power_of_two(),
                    };
                let res = build_by_id(spec.id, d, 1);
                assert_eq!(
                    res.is_ok(),
                    in_domain,
                    "Domain mismatch for {} at d={d}: in_domain={in_domain}, err={:?}",
                    spec.id,
                    res.err()
                );
                if let Ok(sc) = res {
                    assert_eq!(sc.title, spec.title);
                }
            }
        }
    }

    #[test]
    fn exact_basis_verifier_and_u64_simulator_match_scalar() {
        let sc = build_by_id("ctrl_xor_butterfly", 4, 2).unwrap();
        sc.verify_transposer_exact_basis();
        let l = sc.len_bits();
        let mut x_lanes = vec![0u64; l];
        for lane in 0..64usize {
            for p in 0..l {
                if ((p * 37 + lane * 13 + 5) & 1) == 1 {
                    x_lanes[p] |= 1u64 << lane;
                }
            }
        }
        let y_lanes = sc.simulate_bits_u64(&x_lanes);
        for lane in 0..64usize {
            let x_scalar: Vec<u8> = (0..l).map(|p| ((x_lanes[p] >> lane) & 1) as u8).collect();
            let y_scalar = sc.simulate_bits(&x_scalar);
            for r in 0..l {
                assert_eq!(((y_lanes[r] >> lane) & 1) as u8, y_scalar[r]);
            }
        }
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
