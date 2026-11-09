//! Schedule generators for Paper 16's finite experiments:
//! - Five two-sided linear-time cascades (`Section 10.3`: `c1_torus_cascade`, `c2_bfly_cascade`,
//!   `c3_ten_entry_cascade`, `c4_no_overwrite_cascade` + historical probe `c4_probe_s6_disjoint`,
//!   and `c5_comb_fanout`);
//! - Seven bit-verified superlinear transpose controls (`O(L log d)` and `O(d^{1/3} L)`);
//! - Three padded / `F_2`-algebraic non-transpose comparison controls;
//! - Fourteen excluded linear-time comparison schedules (`Remark 6.8`, `Remark 10.1`,
//!   and every numerical row of `Appendix A`'s `"Crossings"` column).

use std::collections::{HashMap, HashSet};

use crate::model::{tpos, ComputationKind, Schedule, ScheduleBuilder, StepOp};

/// Metadata entry for a schedule generator in the curated suite.
#[derive(Clone, Copy, Debug)]
pub struct ScheduleSpec {
    pub id: &'static str,
    pub title: &'static str,
    pub group: &'static str,
    pub k_tapes: usize,
    pub kind: ComputationKind,
    pub min_d: usize,
    pub power_of_two_only: bool,
    pub paper_ref: &'static str,
}

pub const ALL_SPECS: &[ScheduleSpec] = &[
    // --- Section 10.3: Five Two-Sided Linear-Time Cascades (+ strict no-overwrite Cascade 4) ---
    ScheduleSpec {
        id: "c1_torus_cascade",
        title: "Cascade 1: Two-tape 2D torus-shift + global frame cascade (Adv2b)",
        group: "cascade",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 16,
        power_of_two_only: true,
        paper_ref: "Section 10.3 (1), Remarks 5.8 & 10.1, Section 10.4, Problem 11.1",
    },
    ScheduleSpec {
        id: "c2_bfly_cascade",
        title: "Cascade 2: Two-tape reflection/butterfly + global frame cascade (Adv1)",
        group: "cascade",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.3 (2), Remarks 5.8 & 10.1",
    },
    ScheduleSpec {
        id: "c3_ten_entry_cascade",
        title: "Cascade 3: Three-tape <=10-entry cascade with monotone w_2 zones (S6_fresh)",
        group: "cascade",
        k_tapes: 3,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.3 (3), Remarks 5.8 & 10.1, Section 10.4, Problem 11.1",
    },
    ScheduleSpec {
        id: "c4_no_overwrite_cascade",
        title: "Cascade 4: Three-tape strict no-overwrite cascade (disjoint zones, <=1 write/cell)",
        group: "cascade",
        k_tapes: 3,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.3 (4), Remarks 5.8 & 10.1, Section 10.4, Problem 11.1",
    },
    ScheduleSpec {
        id: "c4_probe_s6_disjoint",
        title: "Cascade 4 (historical probe): Three-tape disjoint-pyramid on w_2 (S6_disjoint_curved)",
        group: "cascade",
        k_tapes: 3,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.3 (4) historical probe, Remark 5.8 E=L row",
    },
    ScheduleSpec {
        id: "c5_comb_fanout",
        title: "Cascade 5: Two-tape multi-scale comb + 1-to-2 fan-out cascade (S5_fanout_rawrow)",
        group: "cascade",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.3 (5), Remarks 5.8 & 10.1",
    },
    // --- Superlinear Bit-Verified Transpose Controls ---
    ScheduleSpec {
        id: "ctrl_lsb_radix",
        title: "Control: Global LSB pure-stack binary-radix transposer, O(L log d)",
        group: "transposer_control",
        k_tapes: 2,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Remark 10.1, Section 10.4, Problem 11.1",
    },
    ScheduleSpec {
        id: "ctrl_localized_msb_bfly",
        title: "Control: Block-localized MSB butterfly transposer, O(L log d)",
        group: "transposer_control",
        k_tapes: 2,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Remark 5.8, Remark 10.1, Section 10.4, Problem 11.1",
    },
    ScheduleSpec {
        id: "ctrl_pinned_dfs_bfly",
        title: "Control: Pinned-skeleton single-leg DFS butterfly transposer, O(L log d)",
        group: "transposer_control",
        k_tapes: 2,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 16,
        power_of_two_only: true,
        paper_ref: "Remark 6.8, Remark 10.1, Problem 11.1",
    },
    ScheduleSpec {
        id: "ctrl_xor_butterfly",
        title: "Control: Global 3-XOR F_2 butterfly transposer, O(L log d)",
        group: "transposer_control",
        k_tapes: 2,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Problem 11.1",
    },
    ScheduleSpec {
        id: "ctrl_xor_pinned_dfs",
        title: "Control: Pinned-skeleton single-leg 3-XOR F_2 transposer, O(L log d)",
        group: "transposer_control",
        k_tapes: 2,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 16,
        power_of_two_only: true,
        paper_ref: "Problem 11.1",
    },
    ScheduleSpec {
        id: "ctrl_u1_unitslope_bfly",
        title: "Control: Three-tape unit-slope 3-shift butterfly transposer, O(L log d)",
        group: "transposer_control",
        k_tapes: 3,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.4",
    },
    ScheduleSpec {
        id: "ctrl_d13_one_excursion",
        title: "Control: One-excursion pure-stack transposer, O(d^{1/3} L)",
        group: "transposer_control",
        k_tapes: 2,
        kind: ComputationKind::BitVerifiedTransposer,
        min_d: 4,
        power_of_two_only: false,
        paper_ref: "Remark 10.1, Appendix A Row 23 note",
    },
    // --- Padded & Explicit Non-Transpose Controls ---
    ScheduleSpec {
        id: "ctrl_padded_c1",
        title: "Control: Cascade 1 padded with log_2(d) full-bank sweeps, O(L log d)",
        group: "padded_or_algebraic_control",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 16,
        power_of_two_only: true,
        paper_ref: "Section 10.4",
    },
    ScheduleSpec {
        id: "ctrl_padded_c3",
        title: "Control: Cascade 3 padded with log_2(d) full-bank sweeps, O(L log d)",
        group: "padded_or_algebraic_control",
        k_tapes: 3,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Section 10.4",
    },
    ScheduleSpec {
        id: "ctrl_xor_cascade_lintime",
        title: "Control: Explicit F_2 linear-time multi-scale XOR-mixing cascade (non-transpose)",
        group: "padded_or_algebraic_control",
        k_tapes: 3,
        kind: ComputationKind::ExplicitNonTransposer,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Problem 11.1 / Section 10.3 F_2 control",
    },
    // --- Excluded Linear-Time Schedules (Remarks 6.8 & 10.1, Appendix A "Crossings" rows) ---
    ScheduleSpec {
        id: "cat_row01_direct_copy",
        title: "Catalogue Row 1: Direct input-to-output identity copy (C1_identity)",
        group: "catalogue",
        k_tapes: 1,
        kind: ComputationKind::ExplicitNonTransposer,
        min_d: 2,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 1",
    },
    ScheduleSpec {
        id: "cat_row02_persistent_triangles",
        title: "Catalogue Row 2: Persistent-triangle schedule Y[j,i]=X[j,-j-i] (C2_triangles)",
        group: "catalogue",
        k_tapes: 1,
        kind: ComputationKind::ExplicitNonTransposer,
        min_d: 2,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 2",
    },
    ScheduleSpec {
        id: "cat_row03_one_pass_shear",
        title: "Catalogue Row 3: One-pass rotated row-shear schedule (S1_shear)",
        group: "catalogue",
        k_tapes: 3,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: false,
        paper_ref: "Remark 6.8, Remark 10.1, Appendix A Row 3",
    },
    ScheduleSpec {
        id: "cat_row07_unitslope",
        title: "Catalogue Row 7: Constant-phase unit-slope reflection+shift (B1_unitslope_const)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 7",
    },
    ScheduleSpec {
        id: "cat_row08_bounce",
        title: "Catalogue Row 8: Sub-row fresh-slot bounce + multi-pass input (Adv_IC2_bounce)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 8",
    },
    ScheduleSpec {
        id: "cat_row16_one_free_wave",
        title: "Catalogue Row 16: One free tape + sub-row strip wavefront (S6_1free_wave_sublinear)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Appendix A Row 16",
    },
    ScheduleSpec {
        id: "cat_row24_dyck_mscale",
        title: "Catalogue Row 24: Multi-scale free tape + sawtooth Dyck LIFO stack (Adv_Leaf1_dyck)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Remark 10.1, Appendix A Row 24",
    },
    ScheduleSpec {
        id: "cat_row27_gis2_swept",
        title: "Catalogue Row 27: Swept inverse-square two-exception geometry (G_IS2_swept)",
        group: "catalogue",
        k_tapes: 10,
        kind: ComputationKind::GeometryOnly,
        min_d: 64,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 27",
    },
    ScheduleSpec {
        id: "cat_row28_gis2",
        title: "Catalogue Row 28: Nine-head inverse-square two-exception geometry (G_IS2)",
        group: "catalogue",
        k_tapes: 9,
        kind: ComputationKind::GeometryOnly,
        min_d: 64,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 28",
    },
    ScheduleSpec {
        id: "cat_row29_gis2_gap",
        title: "Catalogue Row 29: Eleven-head small-gap inverse-square geometry (G_IS2_gap)",
        group: "catalogue",
        k_tapes: 11,
        kind: ComputationKind::GeometryOnly,
        min_d: 64,
        power_of_two_only: false,
        paper_ref: "Appendix A Row 29",
    },
    ScheduleSpec {
        id: "cat_row30_mirrored_dyadic",
        title: "Catalogue Row 30: Mirrored dyadic fold-back cascade (S2b_dyadic_fold)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Appendix A Row 30",
    },
    ScheduleSpec {
        id: "cat_row32_dyadic_fold",
        title: "Catalogue Row 32: Dyadic geometric + sub-row butterfly fold (S2_dyadic_fold)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Appendix A Row 32",
    },
    ScheduleSpec {
        id: "cat_row36_lifo_fanout",
        title: "Catalogue Row 36: Binary-tree LIFO pushdown fan-out cascade (Adv_Leaf1_lifo_fanout)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 8,
        power_of_two_only: true,
        paper_ref: "Appendix A Row 36",
    },
    ScheduleSpec {
        id: "cat_row37_tapped_cascade",
        title: "Catalogue Row 37: Equal-volume tapped mesoscopic cascade (Adv_BTL5_tapped)",
        group: "catalogue",
        k_tapes: 2,
        kind: ComputationKind::GeometryOnly,
        min_d: 4,
        power_of_two_only: true,
        paper_ref: "Appendix A Row 37",
    },
];

pub fn find_spec(id: &str) -> Option<&'static ScheduleSpec> {
    ALL_SPECS.iter().find(|s| s.id == id)
}

pub fn build_by_id(id: &str, d: usize, b: usize) -> Result<Schedule, String> {
    let spec = find_spec(id).ok_or_else(|| format!("Unknown schedule id '{id}'"))?;
    if d < spec.min_d {
        return Err(format!(
            "Schedule '{}' requires d >= {} (got d = {})",
            id, spec.min_d, d
        ));
    }
    if spec.power_of_two_only && !d.is_power_of_two() {
        return Err(format!(
            "Schedule '{}' requires d to be a power of two (got d = {})",
            id, d
        ));
    }
    if b == 0 {
        return Err("Entry bit-width b must be >= 1".to_string());
    }
    let sched = match id {
        "c1_torus_cascade" => build_c1_torus_cascade(d, b),
        "c2_bfly_cascade" => build_c2_bfly_cascade(d, b),
        "c3_ten_entry_cascade" => build_c3_ten_entry_cascade(d, b),
        "c4_no_overwrite_cascade" => build_c4_no_overwrite_cascade(d, b),
        "c4_probe_s6_disjoint" => build_c4_probe_s6_disjoint(d, b),
        "c5_comb_fanout" => build_c5_comb_fanout(d, b),
        "ctrl_lsb_radix" => build_ctrl_lsb_radix(d, b),
        "ctrl_localized_msb_bfly" => build_ctrl_localized_msb_bfly(d, b),
        "ctrl_pinned_dfs_bfly" => build_ctrl_pinned_dfs_bfly(d, b),
        "ctrl_xor_butterfly" => build_ctrl_xor_butterfly(d, b),
        "ctrl_xor_pinned_dfs" => build_ctrl_xor_pinned_dfs(d, b),
        "ctrl_u1_unitslope_bfly" => build_ctrl_u1_unitslope_bfly(d, b),
        "ctrl_d13_one_excursion" => build_ctrl_d13_one_excursion(d, b),
        "ctrl_padded_c1" => {
            let base = build_c1_torus_cascade(d, b);
            build_padded_cascade(
                &base,
                "ctrl_padded_c1",
                "Control: Cascade 1 padded with log_2(d) full-bank sweeps, O(L log d)",
            )
        }
        "ctrl_padded_c3" => {
            let base = build_c3_ten_entry_cascade(d, b);
            build_padded_cascade(
                &base,
                "ctrl_padded_c3",
                "Control: Cascade 3 padded with log_2(d) full-bank sweeps, O(L log d)",
            )
        }
        "ctrl_xor_cascade_lintime" => build_ctrl_xor_cascade_lintime(d, b),
        "cat_row01_direct_copy" => build_cat_row01_direct_copy(d, b),
        "cat_row02_persistent_triangles" => build_cat_row02_persistent_triangles(d, b),
        "cat_row03_one_pass_shear" => build_cat_row03_one_pass_shear(d, b),
        "cat_row07_unitslope" => build_cat_row07_unitslope(d, b),
        "cat_row08_bounce" => build_cat_row08_bounce(d, b),
        "cat_row16_one_free_wave" => build_cat_row16_one_free_wave(d, b),
        "cat_row24_dyck_mscale" => build_cat_row24_dyck_mscale(d, b),
        "cat_row27_gis2_swept" => build_cat_row27_gis2_swept(d, b),
        "cat_row28_gis2" => build_cat_row28_gis2(d, b),
        "cat_row29_gis2_gap" => build_cat_row29_gis2_gap(d, b),
        "cat_row30_mirrored_dyadic" => build_cat_row30_mirrored_dyadic(d, b),
        "cat_row32_dyadic_fold" => build_cat_row32_dyadic_fold(d, b),
        "cat_row36_lifo_fanout" => build_cat_row36_lifo_fanout(d, b),
        "cat_row37_tapped_cascade" => build_cat_row37_tapped_cascade(d, b),
        _ => unreachable!(),
    };
    Ok(sched)
}

// ============================================================================
// Part 1: Five Two-Sided Linear-Time Cascades (Section 10.3)
// ============================================================================

fn apply_k2_global_frame_cascade(
    sb: &mut ScheduleBuilder,
    d: usize,
    b: usize,
    cur0: &mut usize,
    cur1: &mut usize,
) {
    let m_log = d.trailing_zeros() as usize;
    let r_max = (m_log - 1).max(1);
    let l = d * d * b;

    let mut z_w1 = vec![0usize; r_max + 1];
    let mut scr_w1 = vec![0usize; r_max + 1];
    let mut comb_w1 = vec![0usize; r_max + 1];
    for r in 1..=r_max {
        let m_r = l >> r;
        scr_w1[r] = *cur1;
        *cur1 += m_r + 2;
        z_w1[r] = *cur1;
        *cur1 += m_r + 2;
        comb_w1[r] = *cur1;
        *cur1 += m_r + 2;
    }

    let mut a0_span = l;
    for r in 1..=r_max {
        let m_r = l >> r;
        let shift = (m_r / 3 + b) % m_r;
        let rem = m_r - shift;
        let a0 = *cur0;
        let next0 = a0 + a0_span + 4;

        sb.move_two_works_to(0, a0 as i64, 1, scr_w1[r] as i64);
        let mut c0 = 0usize;
        let mut c1 = 0usize;
        while c0 + 1 < m_r || c1 + 1 < m_r {
            let adv0 = c0 + 1 < m_r && (c0 < m_r / 3 || c1 <= (2 * c0) / 3 + m_r / 3);
            let adv1 = c1 + 1 < m_r && (c1 >= m_r / 3 || c0 >= 2 * c1);
            let mut dw0 = if adv0 {
                c0 += 1;
                1
            } else {
                0
            };
            let mut dw1 = if adv1 {
                c1 += 1;
                1
            } else {
                0
            };
            if dw0 == 0 && dw1 == 0 {
                if c0 + 1 < m_r {
                    c0 += 1;
                    dw0 = 1;
                }
                if c1 + 1 < m_r {
                    c1 += 1;
                    dw1 = 1;
                }
            }
            sb.step(0, &[dw0, dw1], false);
        }

        sb.move_two_works_to(0, (a0 + m_r) as i64, 1, (scr_w1[r] + m_r - 1) as i64);
        for idx in 0..m_r {
            let dw0 = if idx + 1 < m_r { 1 } else { 0 };
            let dw1 = if idx + 1 < m_r { -1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }

        sb.move_two_works_to(0, next0 as i64, 1, scr_w1[r] as i64);
        for idx in 0..m_r {
            let d01 = if idx + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }

        sb.move_two_works_to(0, (next0 + shift) as i64, 1, z_w1[r] as i64);
        for idx in 0..rem {
            let dw0 = if idx + 1 < rem { 1 } else { 0 };
            let dw1 = if idx + 1 < rem || shift > 0 { 1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }
        if shift > 0 {
            sb.move_work_to(0, next0 as i64);
            for idx in 0..shift {
                let d01 = if idx + 1 < shift { 1 } else { 0 };
                sb.step(0, &[d01, d01], false);
            }
        }

        *cur0 = next0;
        a0_span = m_r;
    }

    for r in (1..=r_max).rev() {
        let m_r = l >> r;
        let shift = (m_r / 3 + b) % m_r;
        let rem = m_r - shift;
        let b0_src = *cur0;
        let next0 = b0_src + a0_span + 4;

        sb.move_two_works_to(
            0,
            (b0_src + m_r - 1) as i64,
            1,
            (z_w1[r] + m_r - 1) as i64,
        );
        for idx in 0..m_r {
            let d01 = if idx + 1 < m_r { -1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }
        sb.move_two_works_to(0, b0_src as i64, 1, comb_w1[r] as i64);
        for idx in 0..m_r {
            let d01 = if idx + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }

        sb.move_two_works_to(0, next0 as i64, 1, comb_w1[r] as i64);
        for z in 0..m_r {
            sb.step(0, &[1, 0], false);
            let dw01 = if z + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[dw01, dw01], false);
        }

        sb.move_two_works_to(0, (next0 + 2 * m_r - 1) as i64, 1, comb_w1[r] as i64);
        for z in 0..m_r {
            sb.step(0, &[-1, 0], false);
            let dw0 = if z + 1 < m_r { -1 } else { 0 };
            let dw1 = if z + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }

        sb.move_two_works_to(0, next0 as i64, 1, (comb_w1[r] + shift) as i64);
        for z in 0..rem {
            sb.step(0, &[1, 0], false);
            let dw0 = if z + 1 < rem || shift > 0 { 1 } else { 0 };
            let dw1 = if z + 1 < rem { 1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }
        if shift > 0 {
            sb.move_work_to(1, comb_w1[r] as i64);
            for z in 0..shift {
                sb.step(0, &[1, 0], false);
                let dw01 = if z + 1 < shift { 1 } else { 0 };
                sb.step(0, &[dw01, dw01], false);
            }
        }

        *cur0 = next0;
        a0_span = 2 * m_r;
    }
    assert_eq!(a0_span, l);
}

#[allow(clippy::too_many_arguments)]
fn add_k2_torus_shift_to_bank1(
    sb: &mut ScheduleBuilder,
    d: usize,
    b: usize,
    raw0: usize,
    bank1: usize,
    cur0: &mut usize,
    cur1: &mut usize,
    u_row: usize,
    v_col: usize,
) {
    let l = d * d * b;
    let w = d * b;
    let u = u_row % d;
    let v = v_col % d;
    let tmp1 = *cur1;
    *cur1 += l + 4;
    let tmp0 = *cur0;
    *cur0 += l + 4;

    if v == 0 {
        sb.move_two_works_to(0, raw0 as i64, 1, tmp1 as i64);
        for idx in 0..l {
            let d01 = if idx + 1 < l { 1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }
    } else {
        let len1 = (d - v) * b;
        let len2 = v * b;
        sb.move_two_works_to(0, (raw0 + len2) as i64, 1, tmp1 as i64);
        for row in 0..d {
            let r_base0 = raw0 + row * w;
            for idx in 0..len1 {
                let dw0 = if idx + 1 < len1 { 1 } else { 0 };
                sb.step(0, &[dw0, 1], false);
            }
            sb.move_work_to(0, r_base0 as i64);
            for idx in 0..len2 {
                let dw0 = if idx + 1 < len2 { 1 } else { 0 };
                let dw1 = if idx + 1 < len2 || row + 1 < d { 1 } else { 0 };
                sb.step(0, &[dw0, dw1], false);
            }
            if row + 1 < d {
                sb.move_work_to(0, (raw0 + (row + 1) * w + len2) as i64);
            }
        }
    }

    sb.move_two_works_to(0, tmp0 as i64, 1, tmp1 as i64);
    for idx in 0..l {
        let d01 = if idx + 1 < l { 1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }

    let row_off = u * w;
    let rem_l = l - row_off;
    sb.move_two_works_to(0, (tmp0 + row_off) as i64, 1, bank1 as i64);
    for idx in 0..rem_l {
        let dw0 = if idx + 1 < rem_l { 1 } else { 0 };
        let dw1 = if idx + 1 < rem_l || row_off > 0 { 1 } else { 0 };
        sb.step(0, &[dw0, dw1], false);
    }
    if row_off > 0 {
        sb.move_work_to(0, tmp0 as i64);
        for idx in 0..row_off {
            let d01 = if idx + 1 < row_off { 1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }
    }
}

/// Cascade 1 (`Section 10.3 (1)` / `Adv2b_k2_torus_cascade`, `k = 2`).
pub fn build_c1_torus_cascade(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 16);
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "c1_torus_cascade",
        "Cascade 1: Two-tape 2D torus-shift + global frame cascade (Adv2b)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for u in 0..l {
        let d01 = if u + 1 < l { 1 } else { 0 };
        sb.step(1, &[d01, d01], false);
    }

    let mut cur0 = l + 4;
    let mut cur1 = l + 4;
    let scale = (d / 16).max(1);
    let pairs: [(usize, usize); 2] = [
        (
            (3 * scale + 1) % d,
            ((16 - ((3 * scale + 1) % 16) + 1) % d).max(1),
        ),
        (
            (7 * scale + 2) % d,
            ((16 - ((7 * scale + 2) % 16) + 8) % d).max(1),
        ),
    ];
    for &(u, v) in &pairs {
        add_k2_torus_shift_to_bank1(&mut sb, d, b, 0, 0, &mut cur0, &mut cur1, u, v);
        add_k2_torus_shift_to_bank1(
            &mut sb,
            d,
            b,
            0,
            0,
            &mut cur0,
            &mut cur1,
            (d - v) % d,
            (d - u) % d,
        );
    }

    let seed0 = cur0;
    sb.move_two_works_to(0, seed0 as i64, 1, 0);
    for idx in 0..l {
        let d01 = if idx + 1 < l { 1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }
    cur0 = seed0;

    apply_k2_global_frame_cascade(&mut sb, d, b, &mut cur0, &mut cur1);

    sb.move_two_works_to(0, cur0 as i64, 1, 0);
    for u in 0..l {
        let d01 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[d01, d01], true);
    }
    sb.finish()
}

/// Cascade 2 (`Section 10.3 (2)` / `Adv1_k2_bfly_sym`, `k = 2`).
pub fn build_c2_bfly_cascade(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m_log = d.trailing_zeros() as usize;
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "c2_bfly_cascade",
        "Cascade 2: Two-tape reflection/butterfly + global frame cascade (Adv1)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for u in 0..l {
        let d01 = if u + 1 < l { 1 } else { 0 };
        sb.step(1, &[d01, d01], false);
    }

    let delta_msb = (1usize << (m_log - 1)) * (d - 1) * b;
    let delta_lsb = (d - 1) * b;

    sb.move_two_works_to(0, 0, 1, (l - 1) as i64);
    for idx in 0..l {
        let dw0 = if idx + 1 < l { 1 } else { 0 };
        let dw1 = if idx + 1 < l { -1 } else { 0 };
        sb.step(0, &[dw0, dw1], false);
    }

    let span_msb = l - delta_msb;
    sb.move_two_works_to(0, delta_msb as i64, 1, 0);
    for idx in 0..span_msb {
        let d01 = if idx + 1 < span_msb { 1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }
    sb.move_two_works_to(0, (span_msb - 1) as i64, 1, (l - 1) as i64);
    for idx in (0..span_msb).rev() {
        let d01 = if idx > 0 { -1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }

    let span_lsb = l - delta_lsb;
    sb.move_two_works_to(0, delta_lsb as i64, 1, 0);
    for idx in 0..span_lsb {
        let d01 = if idx + 1 < span_lsb { 1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }
    sb.move_two_works_to(0, (span_lsb - 1) as i64, 1, (l - 1) as i64);
    for idx in (0..span_lsb).rev() {
        let d01 = if idx > 0 { -1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }

    let mut cur0 = l + 4;
    let mut cur1 = l + 4;
    sb.move_two_works_to(0, cur0 as i64, 1, 0);
    for idx in 0..l {
        let d01 = if idx + 1 < l { 1 } else { 0 };
        sb.step(0, &[d01, d01], false);
    }

    apply_k2_global_frame_cascade(&mut sb, d, b, &mut cur0, &mut cur1);

    sb.move_two_works_to(0, cur0 as i64, 1, 0);
    for u in 0..l {
        let d01 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[d01, d01], true);
    }
    sb.finish()
}

/// Historical 4th probe cascade (`S6_disjoint_curved`, `k = 3`, disjoint un-overwritten `Z_r` on `w_2`,
/// shared `[L, 2L)` arena on `w_0, w_1`, `0` crossings at `E = L` in `Remark 5.8`).
pub fn build_c4_probe_s6_disjoint(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m_log = d.trailing_zeros() as usize;
    let r_max = (m_log - 1).max(1);
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "c4_probe_s6_disjoint",
        "Cascade 4 (historical probe): Three-tape disjoint-pyramid on w_2 (S6_disjoint_curved)",
        d,
        b,
        3,
        ComputationKind::GeometryOnly,
    );

    let mut z_off = vec![0usize; r_max + 1];
    let mut acc = 0usize;
    for r in 1..=r_max {
        z_off[r] = acc;
        acc += l >> r;
    }

    sb.move_two_works_to(1, (l - 1) as i64, 2, l as i64);
    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        let dw1 = if u + 1 < l { -1 } else { 0 };
        let dw2 = if u < l / 3 {
            if u % 2 == 0 { 1 } else { 0 }
        } else if (sb.cur_work[2] as usize) + 1 < 2 * l {
            1
        } else {
            0
        };
        sb.step(1, &[dw0, dw1, dw2], false);
    }

    sb.move_two_works_to(0, l as i64, 2, l as i64);
    for u in 0..l {
        let d02 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[d02, 0, d02], false);
    }

    for r in 1..=r_max {
        let m_r = l >> r;
        let shift = (m_r / 3 + b) % m_r;
        let z_lo = z_off[r] as i64;

        sb.move_two_works_to(0, l as i64, 1, l as i64);
        sb.move_work_to(2, z_lo);
        let mut c0 = 0usize;
        let mut c2 = 0usize;
        while c0 + 1 < m_r || c2 + 1 < m_r {
            let advance0 = c0 + 1 < m_r && (c0 < m_r / 3 || c2 <= (2 * c0) / 3 + m_r / 3);
            let advance2 = c2 + 1 < m_r && (c2 >= m_r / 3 || c0 >= 2 * c2);
            let dw0 = if advance0 {
                c0 += 1;
                1
            } else {
                0
            };
            let dw2 = if advance2 {
                c2 += 1;
                1
            } else {
                0
            };
            if dw0 == 0 && dw2 == 0 {
                let s0 = if c0 + 1 < m_r {
                    c0 += 1;
                    1
                } else {
                    0
                };
                let s2 = if c2 + 1 < m_r {
                    c2 += 1;
                    1
                } else {
                    0
                };
                sb.step(0, &[s0, s2, s2], false);
            } else {
                sb.step(0, &[dw0, dw2, dw2], false);
            }
        }

        let rem = m_r - shift;
        sb.move_two_works_to(0, (l + m_r) as i64, 1, (l + shift) as i64);
        sb.move_work_to(2, z_lo + (shift as i64));
        for u in 0..rem {
            let dw0 = if u + 1 < m_r { 1 } else { 0 };
            let dw12 = if u + 1 < rem { 1 } else { 0 };
            sb.step(0, &[dw0, dw12, dw12], false);
        }
        if shift > 0 {
            sb.move_two_works_to(1, l as i64, 2, z_lo);
            for u in 0..shift {
                let dw0 = if rem + u + 1 < m_r { 1 } else { 0 };
                let dw12 = if u + 1 < shift { 1 } else { 0 };
                sb.step(0, &[dw0, dw12, dw12], false);
            }
        }

        sb.move_two_works_to(0, (l + m_r - 1) as i64, 1, (l + m_r - 1) as i64);
        for u in 0..m_r {
            let d01 = if u + 1 < m_r { -1 } else { 0 };
            sb.step(0, &[d01, d01, 0], false);
        }
    }

    for r in (1..=r_max).rev() {
        let m_r = l >> r;
        let num_blks = 1usize << r;
        let h_r = m_r / num_blks;
        let z_lo = z_off[r] as i64;

        sb.move_two_works_to(0, (l + m_r - 1) as i64, 1, (l + m_r - 1) as i64);
        sb.move_work_to(2, z_lo + (m_r as i64) - 1);
        for blk in (0..num_blks).rev() {
            for _ in 0..(h_r - 1) {
                sb.step(0, &[-1, -1, -1], false);
            }
            for _ in 0..(h_r - 1) {
                sb.step(0, &[0, 1, 0], false);
            }
            for _ in 0..(h_r - 1) {
                sb.step(0, &[0, -1, 0], false);
            }
            if blk > 0 {
                sb.step(0, &[-1, -1, -1], false);
            } else {
                sb.step(0, &[0, 0, 0], false);
            }
        }

        sb.move_two_works_to(0, l as i64, 1, l as i64);
        sb.move_work_to(2, z_lo);
        for z in 0..m_r {
            sb.step(0, &[1, 0, 0], false);
            let dw0 = if z + 1 < m_r { 1 } else { 0 };
            let dw12 = if z + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[dw0, dw12, dw12], false);
        }

        let shift = (m_r / 3 + b) % m_r;
        let rem = m_r - shift;
        if shift > 0 {
            sb.move_work_to(1, (l + shift - 1) as i64);
            for z in 0..shift {
                sb.step(0, &[-1, 0, 0], false);
                let dw1 = if z + 1 < shift { -1 } else { 0 };
                sb.step(0, &[-1, dw1, 0], false);
            }
        }
        sb.move_work_to(1, (l + m_r - 1) as i64);
        for z in 0..rem {
            sb.step(0, &[-1, 0, 0], false);
            let dw0 = if z + 1 < rem { -1 } else { 0 };
            let dw1 = if z + 1 < rem { -1 } else { 0 };
            sb.step(0, &[dw0, dw1, 0], false);
        }
    }

    sb.move_two_works_to(0, l as i64, 1, 0);
    for u in 0..l {
        let d01 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[d01, d01, 0], false);
    }

    sb.move_two_works_to(0, 0, 1, (l - 1) as i64);
    sb.move_work_to(2, 0);
    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        let dw1 = if u + 1 < l { -1 } else { 0 };
        let dw2 = if (sb.cur_work[2] as usize) + 1 < acc {
            1
        } else {
            0
        };
        sb.step(0, &[dw0, dw1, dw2], true);
    }
    sb.finish()
}

/// Cascade 3 (`Section 10.3 (3)` / `S6_fresh`, `k = 3`, every cell entered `<= 10` times,
/// disjoint scale zones `Z_r` on `w_2` traversed monotonically in each stage).
pub fn build_c3_ten_entry_cascade(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m_log = d.trailing_zeros() as usize;
    let r_max = (m_log - 1).max(1);
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "c3_ten_entry_cascade",
        "Cascade 3: Three-tape <=10-entry cascade with monotone w_2 zones (S6_fresh)",
        d,
        b,
        3,
        ComputationKind::GeometryOnly,
    );

    let mut z_off = vec![0usize; r_max + 1];
    let mut acc = 0usize;
    for r in 1..=r_max {
        z_off[r] = acc;
        acc += l >> r;
    }

    sb.move_work_to(2, l as i64);
    for u in 0..l {
        let dw01 = if u + 1 < l { 1 } else { 0 };
        let dw2 = if u < l / 3 {
            if u % 2 == 0 { 1 } else { 0 }
        } else if (sb.cur_work[2] as usize) + 1 < 2 * l {
            1
        } else {
            0
        };
        sb.step(1, &[dw01, dw01, dw2], false);
    }

    let mut cur_w0_base = l;
    let mut cur_w1_base = l;
    sb.move_work_to(0, (cur_w0_base + l - 1) as i64);
    for u in 0..l {
        let dw0 = if u + 1 < l { -1 } else { 0 };
        let dw2 = if sb.cur_work[2] > (l as i64) { -1 } else { 0 };
        sb.step(0, &[dw0, 0, dw2], false);
    }
    sb.move_work_to(2, 0);

    for r in 1..=r_max {
        let m_r = l >> r;
        let shift = (m_r / 3 + b) % m_r;
        let next_w0_base = cur_w0_base + (if r == 1 { l } else { 2 * m_r });
        let scratch_w1 = cur_w1_base;
        cur_w1_base += m_r + 2;

        sb.move_two_works_to(0, cur_w0_base as i64, 1, scratch_w1 as i64);
        let mut c0 = 0usize;
        let mut c1 = 0usize;
        while c0 + 1 < m_r || c1 + 1 < m_r {
            let adv0 = c0 + 1 < m_r && (c0 < m_r / 3 || c1 <= (2 * c0) / 3 + m_r / 3);
            let adv1 = c1 + 1 < m_r && (c1 >= m_r / 3 || c0 >= 2 * c1);
            let mut dw0 = if adv0 {
                c0 += 1;
                1
            } else {
                0
            };
            let mut dw1 = if adv1 {
                c1 += 1;
                1
            } else {
                0
            };
            if dw0 == 0 && dw1 == 0 {
                if c0 + 1 < m_r {
                    c0 += 1;
                    dw0 = 1;
                }
                if c1 + 1 < m_r {
                    c1 += 1;
                    dw1 = 1;
                }
            }
            sb.step(0, &[dw0, dw1, 0], false);
        }

        cur_w1_base += m_r + 2;
        let rem = m_r - shift;
        sb.move_two_works_to(0, (cur_w0_base + m_r + rem) as i64, 1, scratch_w1 as i64);
        sb.move_work_to(2, z_off[r] as i64);
        for u in 0..shift {
            let dw0 = if u + 1 < shift { 1 } else { 0 };
            let dw12 = if u + 1 < shift { 1 } else { 0 };
            sb.step(0, &[dw0, dw12, dw12], false);
        }
        if shift > 0 && rem > 0 {
            sb.step(0, &[0, 1, 1], false);
        }
        sb.move_work_to(0, (cur_w0_base + m_r) as i64);
        for u in 0..rem {
            let dw0 = if u + 1 < rem { 1 } else { 0 };
            let dw12 = if u + 1 < rem { 1 } else { 0 };
            sb.step(0, &[dw0, dw12, dw12], false);
        }

        sb.move_work_to(0, (next_w0_base + m_r - 1) as i64);
        for u in 0..m_r {
            let d02 = if u + 1 < m_r { -1 } else { 0 };
            sb.step(0, &[d02, 0, d02], false);
        }
        if r < r_max {
            sb.move_work_to(2, z_off[r + 1] as i64);
        }
        cur_w0_base = next_w0_base;
    }

    for r in (1..=r_max).rev() {
        let m_r = l >> r;
        let num_blks = 1usize << r;
        let h_r = (m_r / num_blks).max(1);
        let shift = (m_r / 3 + b) % m_r;
        let comb_w1 = cur_w1_base;
        cur_w1_base += m_r + 2;
        let next_w0_base = cur_w0_base + 2 * m_r + 2;

        sb.move_two_works_to(
            0,
            (cur_w0_base + m_r - 1) as i64,
            1,
            (comb_w1 + m_r - 1) as i64,
        );
        sb.move_work_to(2, (z_off[r] + m_r - 1) as i64);
        for blk in (0..num_blks).rev() {
            for _ in 0..(h_r - 1) {
                sb.step(0, &[-1, -1, -1], false);
            }
            for _ in 0..(h_r - 1) {
                sb.step(0, &[0, 1, 0], false);
            }
            for _ in 0..(h_r - 1) {
                sb.step(0, &[0, -1, 0], false);
            }
            if blk > 0 {
                sb.step(0, &[-1, -1, -1], false);
            }
        }

        sb.move_two_works_to(0, next_w0_base as i64, 1, comb_w1 as i64);
        for z in 0..m_r {
            sb.step(0, &[1, 0, 0], false);
            let dw0 = if z + 1 < m_r { 1 } else { 0 };
            let dw1 = if z + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[dw0, dw1, 0], false);
        }

        let rem = m_r - shift;
        if shift > 0 {
            sb.move_work_to(1, (comb_w1 + shift - 1) as i64);
            for z in 0..shift {
                sb.step(0, &[-1, 0, 0], false);
                let dw0 = if rem > 0 || z + 1 < shift { -1 } else { 0 };
                let dw1 = if z + 1 < shift { -1 } else { 0 };
                sb.step(0, &[dw0, dw1, 0], false);
            }
        }
        sb.move_work_to(1, (comb_w1 + m_r - 1) as i64);
        for z in 0..rem {
            sb.step(0, &[-1, 0, 0], false);
            let dw0 = if z + 1 < rem { -1 } else { 0 };
            let dw1 = if z + 1 < rem { -1 } else { 0 };
            sb.step(0, &[dw0, dw1, 0], false);
        }

        cur_w0_base = next_w0_base;
    }

    sb.move_two_works_to(0, cur_w0_base as i64, 1, 0);
    sb.move_work_to(2, 0);
    for u in 0..l {
        let dw01 = if u + 1 < l { 1 } else { 0 };
        let dw2 = if (sb.cur_work[2] as usize) + 1 < acc {
            1
        } else {
            0
        };
        sb.step(0, &[dw01, dw01, dw2], true);
    }
    sb.finish()
}

/// Cascade 4 (`Section 10.3 (4)` three-tape no-overwrite construction, `k = 3`, `<= 1` write/cell):
/// Allocates strictly fresh zones on `w_0`, `w_1`, and interleaved scale frames `[Z_r | B_scr_r]`
/// on `w_2` so that EVERY work cell across all 3 tapes is actively written at most ONCE
/// (`max_active_writes_per_cell() == 1`, zero overwrites) and entered `<= 9` times.
pub fn build_c4_no_overwrite_cascade(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m_log = d.trailing_zeros() as usize;
    let r_max = (m_log - 1).max(1);
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "c4_no_overwrite_cascade",
        "Cascade 4: Three-tape strict no-overwrite cascade (disjoint zones, <=1 write/cell)",
        d,
        b,
        3,
        ComputationKind::GeometryOnly,
    );

    // Interleaved scale frames `[z_w2[r] (M_r) | bscr_w2[r] (2*M_r)]` on `w_2[0 .. w2_frames_end)`:
    let mut z_w2 = vec![0usize; r_max + 1];
    let mut bscr_w2 = vec![0usize; r_max + 1];
    let mut cur_w2 = 0usize;
    for r in 1..=r_max {
        let m_r = l >> r;
        z_w2[r] = cur_w2;
        cur_w2 += m_r + 2;
        bscr_w2[r] = cur_w2;
        cur_w2 += 2 * m_r + 2;
    }
    let w2_frames_end = cur_w2;
    let seed_w2 = w2_frames_end + 2;

    // Stage 0a: Load input `[0, L)` onto `w_0[0..L)`, `w_1[0..L)`, and curved seed `w_2[seed_w2..)`.
    // On `w_2`, only write when entering a fresh cell (`u == 0` or `prev_dw2 != 0`) -> 1 write/cell!
    sb.move_work_to(2, seed_w2 as i64);
    let mut prev_dw2 = 1i64;
    for u in 0..l {
        let mask = if prev_dw2 != 0 {
            0b111u16
        } else {
            0b011u16
        };
        let dw01 = if u + 1 < l { 1 } else { 0 };
        let dw2 = if u < l / 3 {
            if u % 2 == 0 { 1 } else { 0 }
        } else if (sb.cur_work[2] as usize) + 1 < seed_w2 + l {
            1
        } else {
            0
        };
        sb.step_with_op(
            1,
            &[dw01, dw01, dw2],
            false,
            StepOp::LoadInputMask { dst_mask: mask },
        );
        prev_dw2 = dw2;
    }

    // Copy curved seed `w_2[end ..= seed_w2]` onto fresh `a_cur = w_0[L+2 .. 2L+2)` (`1` write/cell).
    let mut cur_w0 = l + 2;
    let mut cur_w1 = l + 2;
    let mut a_src = cur_w0;
    cur_w0 += l + 2;
    sb.move_work_to(0, (a_src + l - 1) as i64);
    for u in 0..l {
        let dw0 = if u + 1 < l { -1 } else { 0 };
        let dw2 = if sb.cur_work[2] > seed_w2 as i64 {
            -1
        } else {
            0
        };
        sb.step_with_op(0, &[dw0, 0, dw2], false, StepOp::StageWrite { write_mask: 1 << 0 });
    }
    sb.move_work_to(2, z_w2[1] as i64);

    // Stage 0b: Forward multi-scale compression `r = 1 ..= r_max` (zero cell overwrites).
    for r in 1..=r_max {
        let m_r = l >> r;
        let shift = (m_r / 3 + b) % m_r;
        let rem = m_r - shift;

        let h1_w1 = cur_w1;
        cur_w1 += m_r + 2;
        let h2_w1 = cur_w1;
        cur_w1 += m_r + 2;
        let h2_rev_w0 = cur_w0;
        cur_w0 += m_r + 2;
        let next_a0 = cur_w0;
        cur_w0 += m_r + 2;

        // 1. Variable-speed `2:1`/`1:2` copy of first half `a_src[0..m_r)` -> `h1_w1[0..m_r)` (`1` write/cell)
        sb.move_two_works_to(0, a_src as i64, 1, h1_w1 as i64);
        let mut c0 = 0usize;
        let mut c1 = 0usize;
        let mut need_write_w1 = true;
        loop {
            let wmask = if need_write_w1 { 1u16 << 1 } else { 0 };
            if c0 + 1 >= m_r && c1 + 1 >= m_r {
                sb.step_with_op(0, &[0, 0, 0], false, StepOp::StageWrite { write_mask: wmask });
                break;
            }
            let adv0 = c0 + 1 < m_r && (c0 < m_r / 3 || c1 <= (2 * c0) / 3 + m_r / 3);
            let adv1 = c1 + 1 < m_r && (c1 >= m_r / 3 || c0 >= 2 * c1);
            let mut dw0 = if adv0 {
                c0 += 1;
                1
            } else {
                0
            };
            let mut dw1 = if adv1 {
                c1 += 1;
                1
            } else {
                0
            };
            if dw0 == 0 && dw1 == 0 {
                if c0 + 1 < m_r {
                    c0 += 1;
                    dw0 = 1;
                }
                if c1 + 1 < m_r {
                    c1 += 1;
                    dw1 = 1;
                }
            }
            sb.step_with_op(
                0,
                &[dw0, dw1, 0],
                false,
                StepOp::StageWrite { write_mask: wmask },
            );
            need_write_w1 = dw1 != 0;
        }

        // 2. `(M_r/3 + b)` cyclically shifted copy of second half `a_src[m_r..2*m_r)` -> `h2_w1[0..m_r)` (`1` write/cell)
        sb.move_two_works_to(0, (a_src + m_r + shift) as i64, 1, h2_w1 as i64);
        for u in 0..rem {
            let dw0 = if u + 1 < rem { 1 } else { 0 };
            let dw1 = if u + 1 < rem || shift > 0 { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[dw0, dw1, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 1 },
            );
        }
        if shift > 0 {
            sb.move_work_to(0, (a_src + m_r) as i64);
            for u in 0..shift {
                let d01 = if u + 1 < shift { 1 } else { 0 };
                sb.step_with_op(
                    0,
                    &[d01, d01, 0],
                    false,
                    StepOp::StageWrite { write_mask: 1 << 1 },
                );
            }
        }

        // 3. Reversed copy `h2_w1[m_r-1..=0]` -> `h2_rev_w0[0..m_r)` (`1` write/cell, macroscopic crossing!)
        sb.move_two_works_to(0, h2_rev_w0 as i64, 1, (h2_w1 + m_r - 1) as i64);
        for u in 0..m_r {
            let dw0 = if u + 1 < m_r { 1 } else { 0 };
            let dw1 = if u + 1 < m_r { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[dw0, dw1, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 0 },
            );
        }

        // 4. Simultaneous 3-tape merge: `h2_rev_w0` (`w_0`) + `h1_w1` (`w_1`) -> `Z_r` (`w_2`, `1` write/cell!)
        sb.move_three_works_to(h2_rev_w0 as i64, h1_w1 as i64, z_w2[r] as i64);
        for u in 0..m_r {
            let d012 = if u + 1 < m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d012, d012, d012],
                false,
                StepOp::StageWrite { write_mask: 1 << 2 },
            );
        }

        // 5. Copy `Z_r` (`w_2`) onto fresh `next_a0` (`w_0`, `1` write/cell)
        sb.move_work_to(0, (next_a0 + m_r - 1) as i64);
        for u in 0..m_r {
            let d02 = if u + 1 < m_r { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[d02, 0, d02],
                false,
                StepOp::StageWrite { write_mask: 1 << 0 },
            );
        }
        if r < r_max {
            sb.move_work_to(2, z_w2[r + 1] as i64);
        }
        a_src = next_a0;
    }

    // Stage 1: Backward multi-scale expansion `r = r_max` down to `1` (zero cell overwrites).
    let mut b_src = a_src;
    for r in (1..=r_max).rev() {
        let m_r = l >> r;
        let num_blks = 1usize << r;
        let h_r = (m_r / num_blks).max(1);
        let shift = (m_r / 3 + b) % m_r;
        let rem = m_r - shift;

        let m_zone_w1 = cur_w1;
        cur_w1 += m_r + 2;
        let comb_w0 = cur_w0;
        cur_w0 += m_r + 2;
        let u1_w1 = cur_w1;
        cur_w1 += 2 * m_r + 2;
        let u2_w1 = cur_w1;
        cur_w1 += 2 * m_r + 2;
        let u2_rev_w0 = cur_w0;
        cur_w0 += 2 * m_r + 2;
        let next_b0 = cur_w0;
        cur_w0 += 2 * m_r + 2;

        // 1a. Combine `b_src` (`w_0`) + `Z_r` (`w_2`) -> fresh `m_zone_w1` (`w_1`, `1` write/cell)
        sb.move_three_works_to(
            (b_src + m_r - 1) as i64,
            (m_zone_w1 + m_r - 1) as i64,
            (z_w2[r] + m_r - 1) as i64,
        );
        for u in 0..m_r {
            let d012 = if u + 1 < m_r { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[d012, d012, d012],
                false,
                StepOp::StageWrite { write_mask: 1 << 1 },
            );
        }

        // 1b. Scale-`r` comb-tooth read passes on `m_zone_w1` (`w_1`, 0 writes) writing fresh `comb_w0` (`1` write/cell)
        sb.move_two_works_to(0, (comb_w0 + m_r - 1) as i64, 1, (m_zone_w1 + m_r - 1) as i64);
        for blk in (0..num_blks).rev() {
            for _ in 0..(h_r - 1) {
                sb.step_with_op(0, &[0, -1, 0], false, StepOp::PassThrough);
            }
            for _ in 0..(h_r - 1) {
                sb.step_with_op(0, &[0, 1, 0], false, StepOp::PassThrough);
            }
            for _ in 0..(h_r - 1) {
                sb.step_with_op(
                    0,
                    &[-1, -1, 0],
                    false,
                    StepOp::StageWrite { write_mask: 1 << 0 },
                );
            }
            let d01 = if blk > 0 { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[d01, d01, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 0 },
            );
        }

        // 2. Unshifted `1`-to-`2` doubling `comb_w0` (`w_0`) -> fresh `u1_w1` (`w_1`, `1` write/cell)
        sb.move_two_works_to(0, comb_w0 as i64, 1, u1_w1 as i64);
        for z in 0..m_r {
            sb.step_with_op(
                0,
                &[0, 1, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 1 },
            );
            let d01 = if z + 1 < m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d01, d01, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 1 },
            );
        }

        // 3. `(M_r/3 + b)`-shifted `1`-to-`2` doubling `comb_w0` (`w_0`) -> fresh `u2_w1` (`w_1`, `1` write/cell)
        sb.move_two_works_to(0, (comb_w0 + shift) as i64, 1, u2_w1 as i64);
        for z in 0..rem {
            sb.step_with_op(
                0,
                &[0, 1, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 1 },
            );
            let dw0 = if z + 1 < rem { 1 } else { 0 };
            let dw1 = if z + 1 < rem || shift > 0 { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[dw0, dw1, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 1 },
            );
        }
        if shift > 0 {
            sb.move_work_to(0, comb_w0 as i64);
            for z in 0..shift {
                sb.step_with_op(
                    0,
                    &[0, 1, 0],
                    false,
                    StepOp::StageWrite { write_mask: 1 << 1 },
                );
                let d01 = if z + 1 < shift { 1 } else { 0 };
                sb.step_with_op(
                    0,
                    &[d01, d01, 0],
                    false,
                    StepOp::StageWrite { write_mask: 1 << 1 },
                );
            }
        }

        // 4. Reversed copy `u2_w1[2*m_r-1..=0]` -> fresh `u2_rev_w0[0..2*m_r)` (`1` write/cell)
        sb.move_two_works_to(0, u2_rev_w0 as i64, 1, (u2_w1 + 2 * m_r - 1) as i64);
        for u in 0..(2 * m_r) {
            let dw0 = if u + 1 < 2 * m_r { 1 } else { 0 };
            let dw1 = if u + 1 < 2 * m_r { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[dw0, dw1, 0],
                false,
                StepOp::StageWrite { write_mask: 1 << 0 },
            );
        }

        // 5. Simultaneous 3-tape combine: `u2_rev_w0` (`w_0`) + `u1_w1` (`w_1`) -> `bscr_w2[r]` (`w_2`, `1` write/cell)
        sb.move_three_works_to(u2_rev_w0 as i64, u1_w1 as i64, bscr_w2[r] as i64);
        for u in 0..(2 * m_r) {
            let d012 = if u + 1 < 2 * m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d012, d012, d012],
                false,
                StepOp::StageWrite { write_mask: 1 << 2 },
            );
        }

        // 6. Copy `bscr_w2[r]` (`w_2`) -> fresh `next_b0` (`w_0`, `1` write/cell)
        sb.move_work_to(0, (next_b0 + 2 * m_r - 1) as i64);
        for u in 0..(2 * m_r) {
            let d02 = if u + 1 < 2 * m_r { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[d02, 0, d02],
                false,
                StepOp::StageWrite { write_mask: 1 << 0 },
            );
        }
        b_src = next_b0;
    }

    // Stage 2: Sweep `b_src[0..L)` (`w_0`), `R_0[0..L)` (`w_1`), and all scale frames `w_2[0..w2_frames_end)`
    // simultaneously at <= unit speed (`3*L` steps, emitting 1 output every 3 steps, 0 writes!).
    sb.move_three_works_to(b_src as i64, 0, 0);
    for u in 0..l {
        for sub in 0..3usize {
            let emit = sub == 2;
            let dw01 = if sub == 2 && u + 1 < l { 1 } else { 0 };
            let dw2 = if (sb.cur_work[2] as usize) + 1 < w2_frames_end {
                1
            } else {
                0
            };
            sb.step_with_op(
                0,
                &[dw01, dw01, dw2],
                emit,
                if emit {
                    StepOp::EmitXor3
                } else {
                    StepOp::PassThrough
                },
            );
        }
    }

    let sched = sb.finish();
    assert_eq!(
        sched.max_active_writes_per_cell(),
        1,
        "c4_strict_no_overwrite violated <=1 write/cell"
    );
    sched
}

/// Cascade 5 (`Section 10.3 (5)` / `S5_fanout_rawrow`, `k = 2`).
pub fn build_c5_comb_fanout(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m_log = d.trailing_zeros() as usize;
    let r_max = (m_log - 1).max(1);
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "c5_comb_fanout",
        "Cascade 5: Two-tape multi-scale comb + 1-to-2 fan-out cascade (S5_fanout_rawrow)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        sb.step(1, &[dw0, 0], false);
    }

    for r in 1..=r_max {
        let m_r = l >> r;
        let half_m = m_r / 2;
        sb.move_two_works_to(0, 0, 1, 0);
        for u in 0..m_r {
            let d01 = if u + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }
        sb.move_two_works_to(0, m_r as i64, 1, half_m as i64);
        for u in 0..half_m {
            let dw1 = if u + 1 < half_m { 1 } else { 0 };
            sb.step(0, &[1, dw1], false);
        }
        sb.move_work_to(1, 0);
        for u in 0..half_m {
            let dw0 = if half_m + u + 1 < m_r { 1 } else { 0 };
            let dw1 = if u + 1 < half_m { 1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }
        sb.move_two_works_to(0, (m_r - 1) as i64, 1, (m_r - 1) as i64);
        for u in 0..m_r {
            let d01 = if u + 1 < m_r { -1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }
    }

    for r in (1..=r_max).rev() {
        let m_r = l >> r;
        let num_blks = 1usize << r;
        let h_r = m_r / num_blks;

        sb.move_two_works_to(0, (m_r - 1) as i64, 1, (m_r - 1) as i64);
        for blk in (0..num_blks).rev() {
            for _ in 0..(h_r - 1) {
                sb.step(0, &[-1, -1], false);
            }
            for _ in 0..(h_r - 1) {
                sb.step(0, &[0, 1], false);
            }
            for _ in 0..(h_r - 1) {
                sb.step(0, &[0, -1], false);
            }
            if blk > 0 {
                sb.step(0, &[-1, -1], false);
            } else {
                sb.step(0, &[0, 0], false);
            }
        }

        for z in 0..m_r {
            sb.step(0, &[1, 0], false);
            let d01 = if z + 1 < m_r { 1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }

        let half_m = m_r / 2;
        sb.move_work_to(1, (half_m - 1) as i64);
        for z in 0..half_m {
            sb.step(0, &[-1, 0], false);
            let dw1 = if z + 1 < half_m { -1 } else { 0 };
            sb.step(0, &[-1, dw1], false);
        }
        sb.move_work_to(1, (m_r - 1) as i64);
        for z in 0..half_m {
            sb.step(0, &[-1, 0], false);
            let d01 = if z + 1 < half_m { -1 } else { 0 };
            sb.step(0, &[d01, d01], false);
        }
        sb.move_work_to(1, 0);
    }

    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[dw0, 0], true);
    }
    sb.finish()
}

// ============================================================================
// Part 2: Bit-Verified Superlinear Transpose Controls & Padded/XOR Controls
// ============================================================================

pub fn build_ctrl_lsb_radix(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let l = d * d * b;
    let k_passes = (d.ilog2() as usize).max(1);
    let mut sb = ScheduleBuilder::new(
        "ctrl_lsb_radix",
        "Control: Global LSB pure-stack binary-radix transposer, O(L log d)",
        d,
        b,
        2,
        ComputationKind::BitVerifiedTransposer,
    );

    for p in 0..l {
        let d_step = if p + 1 < l { 1 } else { 0 };
        sb.step_with_op(
            d_step,
            &[d_step, 0],
            false,
            StepOp::LoadInput { dst_tape: 0 },
        );
    }

    for pass in 0..k_passes {
        let is_last = pass + 1 == k_passes;
        while sb.cur_work[0] < (l - 1) as i64 {
            sb.step_with_op(0, &[1, 0], false, StepOp::PassThrough);
        }
        for pos in (0..l).rev() {
            let push_now = ((pos / b) % 2) == 1;
            let dw0 = if pos > 0 { -1 } else { 0 };
            let dw1 = if push_now { 1 } else { 0 };
            let op = if push_now {
                StepOp::CopyWork {
                    src_tape: 0,
                    dst_tape: 1,
                }
            } else {
                StepOp::PassThrough
            };
            sb.step_with_op(0, &[dw0, dw1], false, op);
        }
        for _ in 0..(l - 1) {
            sb.step_with_op(0, &[1, 0], false, StepOp::PassThrough);
        }
        for pos in (0..l).rev() {
            let push_now = ((pos / b) % 2) == 0;
            let dw0 = if pos > 0 { -1 } else { 0 };
            let dw1 = if push_now { 1 } else { 0 };
            let op = if push_now {
                StepOp::CopyWork {
                    src_tape: 0,
                    dst_tape: 1,
                }
            } else {
                StepOp::PassThrough
            };
            sb.step_with_op(0, &[dw0, dw1], false, op);
        }
        sb.step_with_op(0, &[0, -1], false, StepOp::PassThrough);
        for pos in 0..l {
            let dw0 = if pos + 1 < l { 1 } else { 0 };
            let dw1 = if pos + 1 < l { -1 } else { 0 };
            let op = if is_last {
                StepOp::EmitWork { src_tape: 1 }
            } else {
                StepOp::CopyWork {
                    src_tape: 1,
                    dst_tape: 0,
                }
            };
            sb.step_with_op(0, &[dw0, dw1], is_last, op);
        }
    }
    sb.finish()
}

fn emit_bfly_block_pass(
    sb: &mut ScheduleBuilder,
    perm0: &mut [usize],
    perm1: &mut [usize],
    d: usize,
    b: usize,
    base: usize,
    blk_len: usize,
    bit_pos: usize,
) {
    sb.move_two_works_to(0, base as i64, 1, base as i64);
    let mut w1_cnt = 0usize;
    for off in 0..blk_len {
        let orig = perm0[base + off];
        let col = (orig / b) % d;
        let take = ((col >> bit_pos) & 1) == 0;
        if take {
            perm1[base + w1_cnt] = orig;
            w1_cnt += 1;
        }
        let d0 = if off + 1 < blk_len { 1 } else { 0 };
        let d1 = if take && w1_cnt < blk_len { 1 } else { 0 };
        let op = if take {
            StepOp::CopyWork {
                src_tape: 0,
                dst_tape: 1,
            }
        } else {
            StepOp::PassThrough
        };
        sb.step_with_op(0, &[d0, d1], false, op);
    }
    assert_eq!(w1_cnt, blk_len / 2);

    sb.move_work_to(0, base as i64);

    for off in 0..blk_len {
        let orig = perm0[base + off];
        let col = (orig / b) % d;
        let take = ((col >> bit_pos) & 1) == 1;
        if take {
            perm1[base + w1_cnt] = orig;
            w1_cnt += 1;
        }
        let d0 = if off + 1 < blk_len { 1 } else { 0 };
        let d1 = if take && w1_cnt < blk_len { 1 } else { 0 };
        let op = if take {
            StepOp::CopyWork {
                src_tape: 0,
                dst_tape: 1,
            }
        } else {
            StepOp::PassThrough
        };
        sb.step_with_op(0, &[d0, d1], false, op);
    }
    assert_eq!(w1_cnt, blk_len);

    for off in (0..blk_len).rev() {
        perm0[base + off] = perm1[base + off];
        let d01 = if off > 0 { -1 } else { 0 };
        sb.step_with_op(
            0,
            &[d01, d01],
            false,
            StepOp::CopyWork {
                src_tape: 1,
                dst_tape: 0,
            },
        );
    }
}

pub fn build_ctrl_localized_msb_bfly(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m = d.trailing_zeros() as usize;
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "ctrl_localized_msb_bfly",
        "Control: Block-localized MSB butterfly transposer, O(L log d)",
        d,
        b,
        2,
        ComputationKind::BitVerifiedTransposer,
    );

    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(d0, &[d0, 0], false, StepOp::LoadInput { dst_tape: 0 });
    }

    let mut perm0: Vec<usize> = (0..l).collect();
    let mut perm1: Vec<usize> = vec![0; l];

    for s in 0..m {
        let bit_pos = m - 1 - s;
        let num_blks = 1usize << s;
        let blk_len = l >> s;
        let blk_iter: Vec<usize> = if (s % 2) == 0 {
            (0..num_blks).collect()
        } else {
            (0..num_blks).rev().collect()
        };
        for q in blk_iter {
            emit_bfly_block_pass(
                &mut sb,
                &mut perm0,
                &mut perm1,
                d,
                b,
                q * blk_len,
                blk_len,
                bit_pos,
            );
        }
    }

    sb.move_work_to(0, 0);
    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(0, &[d0, 0], true, StepOp::EmitWork { src_tape: 0 });
    }
    sb.finish()
}

#[allow(clippy::too_many_arguments)]
fn emit_recursive_dfs_bfly(
    sb: &mut ScheduleBuilder,
    perm0: &mut [usize],
    perm1: &mut [usize],
    d: usize,
    b: usize,
    r_tot: usize,
    s: usize,
    base: usize,
) {
    if s >= r_tot {
        return;
    }
    let l = d * d * b;
    let blk_len = l >> s;
    let bit_pos = r_tot - 1 - s;
    emit_bfly_block_pass(sb, perm0, perm1, d, b, base, blk_len, bit_pos);
    emit_recursive_dfs_bfly(sb, perm0, perm1, d, b, r_tot, s + 1, base);
    emit_recursive_dfs_bfly(sb, perm0, perm1, d, b, r_tot, s + 1, base + blk_len / 2);
}

pub fn build_ctrl_pinned_dfs_bfly(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 16);
    let r_tot = d.trailing_zeros() as usize;
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "ctrl_pinned_dfs_bfly",
        "Control: Pinned-skeleton single-leg DFS butterfly transposer, O(L log d)",
        d,
        b,
        2,
        ComputationKind::BitVerifiedTransposer,
    );
    let mut perm0: Vec<usize> = (0..l).collect();
    let mut perm1: Vec<usize> = vec![0; l];

    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(d0, &[d0, 0], false, StepOp::LoadInput { dst_tape: 0 });
    }

    for s in 0..3usize {
        let blk_len = l >> s;
        let num_blks = 1usize << s;
        let bit_pos = r_tot - 1 - s;
        let blk_iter: Vec<usize> = if (s % 2) == 0 {
            (0..num_blks).collect()
        } else {
            (0..num_blks).rev().collect()
        };
        for q in blk_iter {
            emit_bfly_block_pass(
                &mut sb,
                &mut perm0,
                &mut perm1,
                d,
                b,
                q * blk_len,
                blk_len,
                bit_pos,
            );
        }
    }

    let lam_star = (l / 6 + 1) as i64;
    sb.move_two_works_to(0, -lam_star, 1, -lam_star);
    sb.move_two_works_to(0, 0, 1, 0);

    let tile_len = l / 8;
    for u in 0..8usize {
        let tile_lo = u * tile_len;
        let tile_hi = (u + 1) * tile_len;
        sb.move_two_works_to(0, tile_lo as i64, 1, tile_lo as i64);
        emit_recursive_dfs_bfly(&mut sb, &mut perm0, &mut perm1, d, b, r_tot, 3, tile_lo);
        let end_pos = (tile_hi - 1) as i64;
        sb.move_two_works_to(0, end_pos, 1, end_pos);
    }

    sb.move_two_works_to(0, 0, 1, 0);
    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(0, &[d0, 0], true, StepOp::EmitWork { src_tape: 0 });
    }
    sb.finish()
}

fn emit_xor_swap_stage_in_slab(
    sb: &mut ScheduleBuilder,
    d: usize,
    b: usize,
    r: usize,
    sub_lo: usize,
    sub_hi: usize,
) {
    let delta = (1usize << r) * (d - 1) * b;
    let span = (sub_hi - sub_lo).saturating_sub(delta);
    assert!(span > 0);
    let len = sub_hi - sub_lo;

    sb.move_two_works_to(0, sub_lo as i64, 1, sub_lo as i64);
    for u in 0..len {
        let d01 = if u + 1 < len { 1 } else { 0 };
        sb.step_with_op(
            0,
            &[d01, d01],
            false,
            StepOp::CopyWork {
                src_tape: 0,
                dst_tape: 1,
            },
        );
    }

    sb.move_two_works_to(0, sub_lo as i64, 1, (sub_lo + delta) as i64);
    for u in 0..span {
        let p = sub_lo + u;
        let entry = p / b;
        let active = (((entry / d) >> r) & 1) == 0 && (((entry % d) >> r) & 1) == 1;
        let d01 = if u + 1 < span { 1 } else { 0 };
        let op = if active {
            StepOp::XorWork {
                src_tape: 1,
                dst_tape: 0,
            }
        } else {
            StepOp::PassThrough
        };
        sb.step_with_op(0, &[d01, d01], false, op);
    }

    for u in (0..span).rev() {
        let p = sub_lo + u;
        let entry = p / b;
        let active = (((entry / d) >> r) & 1) == 0 && (((entry % d) >> r) & 1) == 1;
        let d01 = if u > 0 { -1 } else { 0 };
        let op = if active {
            StepOp::XorWork {
                src_tape: 0,
                dst_tape: 1,
            }
        } else {
            StepOp::PassThrough
        };
        sb.step_with_op(0, &[d01, d01], false, op);
    }

    for u in 0..span {
        let p = sub_lo + u;
        let entry = p / b;
        let active = (((entry / d) >> r) & 1) == 0 && (((entry % d) >> r) & 1) == 1;
        let d01 = if u + 1 < span { 1 } else { 0 };
        let op = if active {
            StepOp::XorWork {
                src_tape: 1,
                dst_tape: 0,
            }
        } else {
            StepOp::PassThrough
        };
        sb.step_with_op(0, &[d01, d01], false, op);
    }

    sb.move_two_works_to(0, (sub_hi - 1) as i64, 1, (sub_hi - 1) as i64);
    for u in (0..len).rev() {
        let p = sub_lo + u;
        let entry = p / b;
        let is_partner = (((entry / d) >> r) & 1) == 1 && (((entry % d) >> r) & 1) == 0;
        let d01 = if u > 0 { -1 } else { 0 };
        let op = if is_partner {
            StepOp::CopyWork {
                src_tape: 1,
                dst_tape: 0,
            }
        } else {
            StepOp::PassThrough
        };
        sb.step_with_op(0, &[d01, d01], false, op);
    }
}

fn emit_xor_dfs_sub_slabs(
    sb: &mut ScheduleBuilder,
    d: usize,
    b: usize,
    r_cur: isize,
    sub_lo: usize,
    sub_hi: usize,
) {
    if r_cur < 0 {
        return;
    }
    emit_xor_swap_stage_in_slab(sb, d, b, r_cur as usize, sub_lo, sub_hi);
    let mid = sub_lo + (sub_hi - sub_lo) / 2;
    emit_xor_dfs_sub_slabs(sb, d, b, r_cur - 1, sub_lo, mid);
    emit_xor_dfs_sub_slabs(sb, d, b, r_cur - 1, mid, sub_hi);
}

pub fn build_ctrl_xor_butterfly(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m = d.trailing_zeros() as usize;
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "ctrl_xor_butterfly",
        "Control: Global 3-XOR F_2 butterfly transposer, O(L log d)",
        d,
        b,
        2,
        ComputationKind::BitVerifiedTransposer,
    );

    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(d0, &[d0, 0], false, StepOp::LoadInput { dst_tape: 0 });
    }
    for r in (0..m).rev() {
        emit_xor_swap_stage_in_slab(&mut sb, d, b, r, 0, l);
    }
    sb.move_work_to(0, 0);
    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(0, &[d0, 0], true, StepOp::EmitWork { src_tape: 0 });
    }
    sb.finish()
}

pub fn build_ctrl_xor_pinned_dfs(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 16);
    let m = d.trailing_zeros() as usize;
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "ctrl_xor_pinned_dfs",
        "Control: Pinned-skeleton single-leg 3-XOR F_2 transposer, O(L log d)",
        d,
        b,
        2,
        ComputationKind::BitVerifiedTransposer,
    );

    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(d0, &[d0, 0], false, StepOp::LoadInput { dst_tape: 0 });
    }
    for s in 0..3usize {
        let r = m - 1 - s;
        let num_slabs = 1usize << s;
        let slab_len = l >> s;
        for q in 0..num_slabs {
            emit_xor_swap_stage_in_slab(&mut sb, d, b, r, q * slab_len, (q + 1) * slab_len);
        }
    }
    let lam_star = (l / 6 + 1) as i64;
    sb.move_two_works_to(0, -lam_star, 1, -lam_star);
    sb.move_two_works_to(0, 0, 1, 0);

    let tile_len = l / 8;
    for u in 0..8usize {
        emit_xor_dfs_sub_slabs(
            &mut sb,
            d,
            b,
            (m as isize) - 4,
            u * tile_len,
            (u + 1) * tile_len,
        );
    }
    sb.move_work_to(0, 0);
    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(0, &[d0, 0], true, StepOp::EmitWork { src_tape: 0 });
    }
    sb.finish()
}

pub fn build_ctrl_u1_unitslope_bfly(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m = d.trailing_zeros() as usize;
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "ctrl_u1_unitslope_bfly",
        "Control: Three-tape unit-slope 3-shift butterfly transposer, O(L log d)",
        d,
        b,
        3,
        ComputationKind::BitVerifiedTransposer,
    );

    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(1, &[dw0, 0, 0], false, StepOp::LoadInput { dst_tape: 0 });
    }
    sb.move_work_to(0, 0);

    for r in 0..m {
        let delta = (1usize << r) * (d - 1) * b;
        let span = l - delta;

        for u in 0..l {
            let d01 = if u + 1 < l { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d01, d01, 0],
                false,
                StepOp::CopyWork {
                    src_tape: 0,
                    dst_tape: 1,
                },
            );
        }
        sb.move_two_works_to(0, 0, 1, 0);

        for u in 0..l {
            let d02 = if u + 1 < l { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d02, 0, d02],
                false,
                StepOp::CopyWork {
                    src_tape: 0,
                    dst_tape: 2,
                },
            );
        }
        sb.move_two_works_to(0, 0, 2, 0);

        sb.move_work_to(1, delta as i64);
        for p in 0..span {
            let entry = p / b;
            let active = (((entry / d) >> r) & 1) == 0 && (((entry % d) >> r) & 1) == 1;
            let d01 = if p + 1 < span { 1 } else { 0 };
            let op = if active {
                StepOp::CopyWork {
                    src_tape: 1,
                    dst_tape: 0,
                }
            } else {
                StepOp::PassThrough
            };
            sb.step_with_op(0, &[d01, d01, 0], false, op);
        }
        sb.move_two_works_to(0, 0, 1, 0);

        sb.move_work_to(0, delta as i64);
        for u in 0..span {
            let p = delta + u;
            let entry = p / b;
            let active = (((entry / d) >> r) & 1) == 1 && (((entry % d) >> r) & 1) == 0;
            let d02 = if u + 1 < span { 1 } else { 0 };
            let op = if active {
                StepOp::CopyWork {
                    src_tape: 2,
                    dst_tape: 0,
                }
            } else {
                StepOp::PassThrough
            };
            sb.step_with_op(0, &[d02, 0, d02], false, op);
        }
        sb.move_two_works_to(0, 0, 2, 0);
    }

    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(0, &[d0, 0, 0], true, StepOp::EmitWork { src_tape: 0 });
    }
    sb.finish()
}

pub fn build_ctrl_d13_one_excursion(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let g = ((d as f64).cbrt().round() as usize).max(1);
    let n_grp = (d + g - 1) / g;
    let m_batch = ((n_grp as f64).sqrt().ceil() as usize).max(1);
    let n_super = (n_grp + m_batch - 1) / m_batch;

    let mut sb = ScheduleBuilder::new(
        "ctrl_d13_one_excursion",
        "Control: One-excursion pure-stack transposer, O(d^{1/3} L)",
        d,
        b,
        2,
        ComputationKind::BitVerifiedTransposer,
    );

    let mut pushed = 0usize;
    for s_rev in (0..n_super).rev() {
        let q_lo = s_rev * m_batch;
        let q_hi = ((s_rev + 1) * m_batch).min(n_grp);
        let col_lo = q_lo * g;
        let col_hi = (q_hi * g).min(d);
        let cols_in_super = col_hi - col_lo;
        let buf_len = d * cols_in_super * b;

        while sb.cur_in > 0 || sb.cur_work[0] > 0 {
            let dx = if sb.cur_in > 0 { -1 } else { 0 };
            let dw0 = if sb.cur_work[0] > 0 { -1 } else { 0 };
            sb.step_with_op(dx, &[dw0, 0], false, StepOp::PassThrough);
        }

        let mut w0_write = 0usize;
        for p in 0..l {
            let col = (p / b) % d;
            let in_window = col >= col_lo && col < col_hi;
            if in_window {
                w0_write += 1;
            }
            let dx = if p + 1 < l { 1 } else { 0 };
            let dw0 = if in_window && w0_write < buf_len {
                1
            } else {
                0
            };
            let op = if in_window {
                StepOp::LoadInput { dst_tape: 0 }
            } else {
                StepOp::PassThrough
            };
            sb.step_with_op(dx, &[dw0, 0], false, op);
        }

        for q in (q_lo..q_hi).rev() {
            let g_col_lo = q * g;
            let g_col_hi = ((q + 1) * g).min(d);
            while sb.cur_work[0] < (buf_len - 1) as i64 {
                sb.step_with_op(0, &[1, 0], false, StepOp::PassThrough);
            }
            for pos in (0..buf_len).rev() {
                let rel_col = col_lo + ((pos / b) % cols_in_super);
                let in_q = rel_col >= g_col_lo && rel_col < g_col_hi;
                if in_q {
                    pushed += 1;
                }
                let dw0 = if pos > 0 { -1 } else { 0 };
                let dw1 = if in_q { 1 } else { 0 };
                let op = if in_q {
                    StepOp::CopyWork {
                        src_tape: 0,
                        dst_tape: 1,
                    }
                } else {
                    StepOp::PassThrough
                };
                sb.step_with_op(0, &[dw0, dw1], false, op);
            }
        }
    }
    assert_eq!(pushed, l);

    let mut rem_stack = l;
    for q in 0..n_grp {
        let g_col_lo = q * g;
        let g_col_hi = ((q + 1) * g).min(d);
        let g_cols = g_col_hi - g_col_lo;
        let g_len = d * g_cols * b;

        while sb.cur_work[0] > 0 {
            sb.step_with_op(0, &[-1, 0], false, StepOp::PassThrough);
        }
        for pos in 0..g_len {
            if q == 0 && pos == 0 {
                sb.step_with_op(0, &[0, -1], false, StepOp::PassThrough);
            }
            rem_stack -= 1;
            let dw0 = if pos + 1 < g_len { 1 } else { 0 };
            let dw1 = if rem_stack > 0 { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[dw0, dw1],
                false,
                StepOp::CopyWork {
                    src_tape: 1,
                    dst_tape: 0,
                },
            );
        }

        for c_off in 0..g_cols {
            while sb.cur_work[0] > 0 {
                sb.step_with_op(0, &[-1, 0], false, StepOp::PassThrough);
            }
            for pos in 0..g_len {
                let is_target_col = ((pos / b) % g_cols) == c_off;
                let dw0 = if pos + 1 < g_len { 1 } else { 0 };
                let op = if is_target_col {
                    StepOp::EmitWork { src_tape: 0 }
                } else {
                    StepOp::PassThrough
                };
                sb.step_with_op(0, &[dw0, 0], is_target_col, op);
            }
        }
    }
    sb.finish()
}

pub fn build_padded_cascade(
    base: &Schedule,
    id: &'static str,
    title: &'static str,
) -> Schedule {
    let d = base.d;
    let b = base.b;
    let k = base.k;
    let l = d * d * b;
    let t_base = base.horizon();
    let first_out = base.append_times.first().copied().unwrap_or(t_base);
    let r_pad = if d <= 1 {
        1
    } else {
        (usize::BITS - (d - 1).leading_zeros()) as usize
    };

    let mut bank_lo = vec![0i64; k];
    for j in 0..k {
        if first_out < t_base {
            let mn = base.work_pos[j][first_out..t_base]
                .iter()
                .copied()
                .min()
                .unwrap_or(0);
            let mx = base.work_pos[j][first_out..t_base]
                .iter()
                .copied()
                .max()
                .unwrap_or(0);
            if mx - mn >= (l as i64) / 2 {
                bank_lo[j] = mn;
            }
        }
    }

    let mut sb = ScheduleBuilder::new(id, title, d, b, k, ComputationKind::GeometryOnly);
    let mut dwork = vec![0i64; k];
    for t in 0..first_out {
        let din = if t + 1 < t_base {
            base.in_pos[t + 1] - base.in_pos[t]
        } else {
            0
        };
        for j in 0..k {
            dwork[j] = if t + 1 < t_base {
                base.work_pos[j][t + 1] - base.work_pos[j][t]
            } else {
                0
            };
        }
        sb.step(din, &dwork, false);
    }

    for pass in 0..r_pad {
        let forward = (pass % 2) == 0;
        loop {
            let mut any_move = false;
            for j in 0..k {
                let tgt = if forward {
                    bank_lo[j]
                } else {
                    bank_lo[j] + (l as i64) - 1
                };
                let step = (tgt - sb.cur_work[j]).signum();
                dwork[j] = step;
                if step != 0 {
                    any_move = true;
                }
            }
            if !any_move {
                break;
            }
            sb.step(0, &dwork, false);
        }
        let dir = if forward { 1i64 } else { -1i64 };
        for u in 0..l {
            let step = if u + 1 < l { dir } else { 0 };
            dwork.fill(step);
            sb.step(0, &dwork, false);
        }
    }

    if first_out < t_base {
        loop {
            let din = (base.in_pos[first_out] - sb.cur_in).signum();
            let mut any_move = din != 0;
            for j in 0..k {
                let step = (base.work_pos[j][first_out] - sb.cur_work[j]).signum();
                dwork[j] = step;
                if step != 0 {
                    any_move = true;
                }
            }
            if !any_move {
                break;
            }
            sb.step(din, &dwork, false);
        }

        let mut out_ptr = 0usize;
        for t in first_out..t_base {
            let emit = out_ptr < base.append_times.len() && base.append_times[out_ptr] == t;
            if emit {
                out_ptr += 1;
            }
            let din = if t + 1 < t_base {
                base.in_pos[t + 1] - base.in_pos[t]
            } else {
                0
            };
            for j in 0..k {
                dwork[j] = if t + 1 < t_base {
                    base.work_pos[j][t + 1] - base.work_pos[j][t]
                } else {
                    0
                };
            }
            sb.step(din, &dwork, emit);
        }
    }
    sb.finish()
}

pub fn build_ctrl_xor_cascade_lintime(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 4);
    let m_log = d.trailing_zeros() as usize;
    let r_max = (m_log - 1).max(1);
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "ctrl_xor_cascade_lintime",
        "Control: Explicit F_2 linear-time multi-scale XOR-mixing cascade (non-transpose)",
        d,
        b,
        3,
        ComputationKind::ExplicitNonTransposer,
    );

    for u in 0..l {
        let d012 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(
            d012,
            &[d012, d012, d012],
            false,
            StepOp::LoadInput { dst_tape: 0 },
        );
    }
    for u in (0..l).rev() {
        let d012 = if u > 0 { -1 } else { 0 };
        sb.step_with_op(
            0,
            &[d012, d012, d012],
            false,
            StepOp::CopyWork {
                src_tape: 0,
                dst_tape: 1,
            },
        );
    }
    for u in 0..l {
        let d02 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(
            0,
            &[d02, 0, d02],
            false,
            StepOp::CopyWork {
                src_tape: 0,
                dst_tape: 2,
            },
        );
    }

    let mut z_off = vec![0usize; r_max + 1];
    let mut acc = 0usize;
    for r in 1..=r_max {
        z_off[r] = acc;
        acc += l >> r;
    }
    let mut cur0 = 0usize;
    let mut cur1 = l;

    for r in 1..=r_max {
        let m_r = l >> r;
        let shift = (m_r / 3 + b) % m_r;
        let next0 = cur0 + 2 * m_r + 2;
        let scratch1 = cur1;
        cur1 += m_r + 2;

        sb.move_two_works_to(0, cur0 as i64, 1, scratch1 as i64);
        for u in 0..m_r {
            let d01 = if u + 1 < m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d01, d01, 0],
                false,
                StepOp::CopyWork {
                    src_tape: 0,
                    dst_tape: 1,
                },
            );
        }
        sb.move_two_works_to(0, (cur0 + 2 * m_r - 1) as i64, 1, scratch1 as i64);
        for u in 0..m_r {
            let d0 = if u + 1 < m_r { -1 } else { 0 };
            let d1 = if u + 1 < m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d0, d1, 0],
                false,
                StepOp::XorWork {
                    src_tape: 0,
                    dst_tape: 1,
                },
            );
        }
        sb.move_three_works_to(next0 as i64, (scratch1 + shift) as i64, z_off[r] as i64);
        let rem = m_r - shift;
        for u in 0..rem {
            let d012 = if u + 1 < rem { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d012, d012, d012],
                false,
                StepOp::XorWork {
                    src_tape: 1,
                    dst_tape: 2,
                },
            );
        }
        if shift > 0 {
            if rem > 0 {
                sb.step_with_op(0, &[1, 0, 1], false, StepOp::PassThrough);
            }
            sb.move_work_to(1, scratch1 as i64);
            for u in 0..shift {
                let d012 = if u + 1 < shift { 1 } else { 0 };
                sb.step_with_op(
                    0,
                    &[d012, d012, d012],
                    false,
                    StepOp::XorWork {
                        src_tape: 1,
                        dst_tape: 2,
                    },
                );
            }
        }
        for u in (0..m_r).rev() {
            let d02 = if u > 0 { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[d02, 0, d02],
                false,
                StepOp::CopyWork {
                    src_tape: 2,
                    dst_tape: 0,
                },
            );
        }
        cur0 = next0;
    }

    for r in (1..=r_max).rev() {
        let m_r = l >> r;
        let next0 = cur0 + 2 * m_r + 2;
        let comb1 = cur1;
        cur1 += m_r + 2;
        sb.move_three_works_to(cur0 as i64, comb1 as i64, z_off[r] as i64);
        for u in 0..m_r {
            let d012 = if u + 1 < m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d012, d012, d012],
                false,
                StepOp::CopyWork {
                    src_tape: 0,
                    dst_tape: 1,
                },
            );
        }
        for u in (0..m_r).rev() {
            let d12 = if u > 0 { -1 } else { 0 };
            sb.step_with_op(
                0,
                &[0, d12, d12],
                false,
                StepOp::XorWork {
                    src_tape: 2,
                    dst_tape: 1,
                },
            );
        }
        sb.move_two_works_to(0, next0 as i64, 1, comb1 as i64);
        for u in 0..m_r {
            sb.step_with_op(
                0,
                &[1, 0, 0],
                false,
                StepOp::CopyWork {
                    src_tape: 1,
                    dst_tape: 0,
                },
            );
            let d01 = if u + 1 < m_r { 1 } else { 0 };
            sb.step_with_op(
                0,
                &[d01, d01, 0],
                false,
                StepOp::CopyWork {
                    src_tape: 1,
                    dst_tape: 0,
                },
            );
        }
        cur0 = next0;
    }

    sb.move_three_works_to(cur0 as i64, 0, 0);
    for u in 0..l {
        let d012 = if u + 1 < l { 1 } else { 0 };
        sb.step_with_op(0, &[d012, d012, d012], true, StepOp::EmitXor3);
    }
    let sched = sb.finish();

    // Sanity check: non-trivial F_2 parity fanout and genuinely NOT matrix transposition.
    let mut x = vec![0u8; l];
    x[b] = 1;
    let out = sched.simulate_bits(&x);
    let ones: usize = out.iter().map(|&v| v as usize).sum();
    assert!(ones >= 2);
    let mut x_rand = vec![0u8; l];
    for (idx, bit) in x_rand.iter_mut().enumerate() {
        *bit = (((idx * 131 + 17) >> 3) & 1) as u8;
    }
    let out_rand = sched.simulate_bits(&x_rand);
    assert!(!(0..l).all(|r| out_rand[r] == x_rand[tpos(d, b, r)]));
    sched
}

// ============================================================================
// Part 3: Excluded Linear-Time Schedules & Appendix A "Crossings" Rows
// ============================================================================

pub fn build_cat_row01_direct_copy(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "cat_row01_direct_copy",
        "Catalogue Row 1: Direct input-to-output identity copy (C1_identity)",
        d,
        b,
        1,
        ComputationKind::ExplicitNonTransposer,
    );
    for p in 0..l {
        let din = if p + 1 < l { 1 } else { 0 };
        sb.step_with_op(din, &[0], true, StepOp::EmitInput);
    }
    sb.finish()
}

pub fn build_cat_row02_persistent_triangles(d: usize, b: usize) -> Schedule {
    let mut sb = ScheduleBuilder::new(
        "cat_row02_persistent_triangles",
        "Catalogue Row 2: Persistent-triangle schedule Y[j,i]=X[j,-j-i] (C2_triangles)",
        d,
        b,
        1,
        ComputationKind::ExplicitNonTransposer,
    );
    for j in 0..d {
        for i in 0..d {
            let c = (2 * d - j - i) % d;
            let p0 = ((j * d + c) * b) as i64;
            while sb.cur_in != p0 || sb.cur_work[0] != 0 {
                let din = (p0 - sb.cur_in).signum();
                let dw0 = (0 - sb.cur_work[0]).signum();
                sb.step_with_op(din, &[dw0], false, StepOp::PassThrough);
            }
            for s in 0..b {
                let d_step = if s + 1 < b { 1 } else { 0 };
                sb.step_with_op(d_step, &[d_step], true, StepOp::EmitInput);
            }
        }
    }
    sb.finish()
}

pub fn build_cat_row03_one_pass_shear(d: usize, b: usize) -> Schedule {
    assert_eq!(d % 2, 0, "cat_row03_one_pass_shear requires even d");
    let m = d / 2;
    let w = d * b;
    let h = m * w;
    let mut sb = ScheduleBuilder::new(
        "cat_row03_one_pass_shear",
        "Catalogue Row 3: One-pass rotated row-shear schedule (S1_shear)",
        d,
        b,
        3,
        ComputationKind::GeometryOnly,
    );

    for i in 0..d {
        let bt = if i < m { 0 } else { 1 };
        let b_start = ((i % m) * w) as i64;
        sb.move_two_works_to(bt, b_start, 2, 0);
        for u in 0..w {
            let dw2 = if u + 1 < w { 1 } else { 0 };
            sb.step(1, &[0, 0, dw2], false);
        }
        let rot = (i * b) % w;
        let cut = (w - rot) % w;
        if cut == 0 {
            sb.move_work_to(2, 0);
            for u in 0..w {
                let mut dw = [0i64; 3];
                if u + 1 < w {
                    dw[bt] = 1;
                    dw[2] = 1;
                }
                sb.step(0, &dw, false);
            }
        } else {
            sb.move_work_to(2, cut as i64);
            let suf_len = w - cut;
            for u in 0..suf_len {
                let mut dw = [0i64; 3];
                dw[bt] = 1;
                if u + 1 < suf_len {
                    dw[2] = 1;
                }
                sb.step(0, &dw, false);
            }
            sb.move_work_to(2, 0);
            for u in 0..cut {
                let mut dw = [0i64; 3];
                if u + 1 < cut {
                    dw[bt] = 1;
                    dw[2] = 1;
                }
                sb.step(0, &dw, false);
            }
        }
        sb.move_work_to(2, 0);
    }

    sb.move_two_works_to(0, 0, 1, 0);
    for u in 0..h {
        let d01 = if u + 1 < h { 1 } else { 0 };
        sb.step(0, &[d01, d01, 0], false);
    }
    sb.move_two_works_to(0, 0, 1, 0);

    if m >= 2 {
        sb.move_work_to(1, w as i64);
        let active = (m - 1) * w;
        for u in 0..active {
            let d01 = if u + 1 < active { 1 } else { 0 };
            sb.step(0, &[d01, d01, 0], false);
        }
        sb.move_work_to(0, (h - 1) as i64);
        sb.move_two_works_to(0, 0, 1, 0);
    }

    for i in 0..d {
        let bt = if i < m { 0 } else { 1 };
        let b_start = ((i % m) * w) as i64;
        sb.move_two_works_to(bt, b_start, 2, 0);
        for u in 0..w {
            let mut dw = [0i64; 3];
            if u + 1 < w {
                dw[bt] = 1;
                dw[2] = 1;
            }
            sb.step(0, &dw, false);
        }
        let cut = (i * b) % w;
        if cut == 0 {
            sb.move_work_to(2, 0);
            for u in 0..w {
                let dw2 = if u + 1 < w { 1 } else { 0 };
                sb.step(0, &[0, 0, dw2], true);
            }
        } else {
            sb.move_work_to(2, cut as i64);
            let suf_len = w - cut;
            for u in 0..suf_len {
                let dw2 = if u + 1 < suf_len { 1 } else { 0 };
                sb.step(0, &[0, 0, dw2], true);
            }
            sb.move_work_to(2, 0);
            for u in 0..cut {
                let dw2 = if u + 1 < cut { 1 } else { 0 };
                sb.step(0, &[0, 0, dw2], true);
            }
        }
        sb.move_work_to(2, 0);
    }
    sb.finish()
}

pub fn build_cat_row07_unitslope(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let shift = (d * b / 2).max(1).min(l - 1);
    let mut sb = ScheduleBuilder::new(
        "cat_row07_unitslope",
        "Catalogue Row 7: Constant-phase unit-slope reflection+shift (B1_unitslope_const)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for u in 0..l {
        let dw = if u + 1 < l { 1 } else { 0 };
        sb.step(1, &[dw, dw], false);
    }
    sb.move_work_to(0, 0);
    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        let d1 = if u + 1 < l { -1 } else { 0 };
        sb.step(0, &[d0, d1], false);
    }
    sb.move_two_works_to(0, 0, 1, shift as i64);
    let span = l - shift;
    for u in 0..span {
        let d1 = if shift + u + 1 < l { 1 } else { 0 };
        sb.step(0, &[1, d1], false);
    }
    for u in span..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[d0, 0], false);
    }
    sb.move_work_to(0, 0);
    for u in 0..l {
        let d0 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[d0, 0], true);
    }
    sb.finish()
}

pub fn build_cat_row08_bounce(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "cat_row08_bounce",
        "Catalogue Row 8: Sub-row fresh-slot bounce + multi-pass input (Adv_IC2_bounce)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );
    let h_cap = (l / (4 * d)).max(2) as i64;

    let mut w1_base = 0i64;
    let mut cur_scale = 1i64;
    let mut w1_dir = 1i64;
    let mut w0_dir = 1i64;
    while (sb.cur_in as usize) + 1 < l {
        for _ in 0..3 {
            if (sb.cur_in as usize) + 1 >= l {
                break;
            }
            if sb.cur_work[0] >= (l as i64) - 1 {
                w0_dir = -1;
            } else if sb.cur_work[0] <= 0 {
                w0_dir = 1;
            }
            let dw1 = if w1_dir > 0 {
                if sb.cur_work[1] - w1_base >= cur_scale {
                    w1_dir = -1;
                    -1
                } else {
                    1
                }
            } else if sb.cur_work[1] <= w1_base {
                w1_base = sb.cur_work[1] + cur_scale + 2;
                cur_scale = if cur_scale * 2 <= h_cap {
                    cur_scale * 2
                } else {
                    1
                };
                w1_dir = 1;
                1
            } else {
                -1
            };
            sb.step(1, &[w0_dir, dw1], false);
        }
        if sb.cur_in >= 1 && (sb.cur_in as usize) + 2 < l {
            sb.step(-1, &[0, 0], false);
        }
    }

    for ell in 0..l {
        let din = if ell % 5 == 4 && (sb.cur_in as usize) + 1 < l {
            1
        } else if sb.cur_in > 0 {
            -1
        } else {
            0
        };
        if sb.cur_work[0] >= (l as i64) - 1 {
            w0_dir = -1;
        } else if sb.cur_work[0] <= 0 {
            w0_dir = 1;
        }
        let dw1 = if sb.cur_work[1] < w1_base + h_cap && (ell / (h_cap as usize).max(1)) % 2 == 0 {
            1
        } else if sb.cur_work[1] > w1_base {
            -1
        } else {
            0
        };
        sb.step(din, &[w0_dir, dw1], true);
    }
    sb.finish()
}

pub fn build_cat_row16_one_free_wave(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let strips = (d / 2).max(2);
    let h_sub = l / strips;
    let n_scales = ((h_sub / 2).ilog2() as usize).max(1);
    let h_slot = h_sub.max(2) as i64;
    let mut sb = ScheduleBuilder::new(
        "cat_row16_one_free_wave",
        "Catalogue Row 16: One free tape + sub-row strip wavefront (S6_1free_wave_sublinear)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for g in 0..strips {
        let arena_base = (g * h_sub) as i64;
        sb.move_work_to(0, arena_base);
        let slot_base = (2 * g as i64) * h_slot;
        sb.move_work_to(1, slot_base);
        for off in 0..h_sub {
            let din = if (sb.cur_in as usize) + 1 < l { 1 } else { 0 };
            let dw0 = if off % 2 == 0 { 1 } else { 0 };
            sb.step(din, &[dw0, 1], false);
        }
        for s in 0..n_scales {
            let step_span = (h_sub >> (s + 1)).max(1);
            for _ in 0..step_span {
                let dw0 = if sb.cur_work[0] > arena_base { -1 } else { 0 };
                let dw1 = if sb.cur_work[1] > slot_base { -1 } else { 0 };
                sb.step(0, &[dw0, dw1], false);
            }
        }
        while sb.cur_work[1] > slot_base {
            sb.step(0, &[0, -1], false);
        }
    }

    for g in (0..strips).rev() {
        let arena_base = (g * h_sub) as i64;
        sb.move_work_to(0, arena_base);
        let slot_base = (2 * (strips + (strips - 1 - g)) as i64) * h_slot;
        sb.move_work_to(1, slot_base);
        for off in 0..h_sub {
            let dw0 = if off + 1 < h_sub { 1 } else { 0 };
            let dw1 = if off < h_sub / 2 { 1 } else { -1 };
            sb.step(0, &[dw0, dw1], true);
        }
    }
    sb.finish()
}

fn gen_multiscale_w0_deltas(d: usize, b: usize) -> Vec<i64> {
    let l = d * d * b;
    let w = d * b;
    let scales = (d.ilog2() as usize).max(1);
    let mut deltas: Vec<i64> = Vec::with_capacity(5 * l);
    let mut cur: i64 = 0;

    let move_to = |cur: &mut i64, target: i64, out: &mut Vec<i64>| {
        while *cur < target {
            out.push(1);
            *cur += 1;
        }
        while *cur > target {
            out.push(-1);
            *cur -= 1;
        }
    };

    for r in 0..=scales {
        let span0 = ((l >> r).max(b)) as i64;
        move_to(&mut cur, span0 - 1, &mut deltas);
        move_to(&mut cur, 0, &mut deltas);
    }

    for i in 0..d {
        let s = i % scales;
        let blk = ((b << s).min(w)) as i64;
        let n_blks = (w as i64) / blk;
        for g in 0..n_blks {
            let base = (i * w) as i64 + g * blk;
            move_to(&mut cur, base, &mut deltas);
            move_to(&mut cur, base + blk - 1, &mut deltas);
            move_to(&mut cur, base, &mut deltas);
            move_to(&mut cur, base + blk - 1, &mut deltas);
        }
    }
    move_to(&mut cur, 0, &mut deltas);
    deltas
}

pub fn build_cat_row24_dyck_mscale(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let w = d * b;
    let w0_mscale = gen_multiscale_w0_deltas(d, b);
    let mut sb = ScheduleBuilder::new(
        "cat_row24_dyck_mscale",
        "Catalogue Row 24: Multi-scale free tape + sawtooth Dyck LIFO stack (Adv_Leaf1_dyck)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for u in 0..l {
        let dx = if u + 1 < l { 1 } else { 0 };
        sb.step(dx, &[dx, 0], false);
    }
    sb.move_work_to(0, 0);

    let half_m = w0_mscale.len() / 2;
    for (idx, &dw0) in w0_mscale.iter().enumerate() {
        let dw1 = if idx < half_m {
            1
        } else if sb.cur_work[1] > 0 {
            -1
        } else {
            0
        };
        sb.step(0, &[dw0, dw1], false);
    }
    while sb.cur_work[1] > 0 {
        sb.step(0, &[0, -1], false);
    }

    let hub_w = (l / 8).max(b) as i64;
    let mut w0_dir = 1i64;
    for _ in 0..(2 * l) {
        if sb.cur_work[0] >= hub_w - 1 {
            w0_dir = -1;
        } else if sb.cur_work[0] <= 0 {
            w0_dir = 1;
        }
        sb.step(0, &[w0_dir, 1], false);
    }
    while sb.cur_work[0] < l as i64 {
        sb.step(0, &[1, 0], false);
    }

    w0_dir = 1;
    let mut emitted = 0usize;
    for wave in 0..d {
        if wave + 1 == d {
            while emitted < l {
                if sb.cur_work[0] >= (2 * l - 1) as i64 {
                    w0_dir = -1;
                } else if sb.cur_work[0] <= l as i64 {
                    w0_dir = 1;
                }
                if sb.cur_work[1] >= 2 {
                    sb.step(0, &[w0_dir, -1], false);
                }
                if sb.cur_work[0] >= (2 * l - 1) as i64 {
                    w0_dir = -1;
                } else if sb.cur_work[0] <= l as i64 {
                    w0_dir = 1;
                }
                let dw1 = if sb.cur_work[1] >= 1 { -1 } else { 0 };
                sb.step(0, &[w0_dir, dw1], true);
                emitted += 1;
            }
        } else {
            for _ in 0..w {
                if sb.cur_work[0] >= (2 * l - 1) as i64 {
                    w0_dir = -1;
                } else if sb.cur_work[0] <= l as i64 {
                    w0_dir = 1;
                }
                sb.step(0, &[w0_dir, -1], false);
            }
            for _ in 0..w {
                if sb.cur_work[0] >= (2 * l - 1) as i64 {
                    w0_dir = -1;
                } else if sb.cur_work[0] <= l as i64 {
                    w0_dir = 1;
                }
                sb.step(0, &[w0_dir, -1], false);
                if sb.cur_work[0] >= (2 * l - 1) as i64 {
                    w0_dir = -1;
                } else if sb.cur_work[0] <= l as i64 {
                    w0_dir = 1;
                }
                sb.step(0, &[w0_dir, -1], true);
                emitted += 1;
            }
            for _ in 0..w {
                if sb.cur_work[0] >= (2 * l - 1) as i64 {
                    w0_dir = -1;
                } else if sb.cur_work[0] <= l as i64 {
                    w0_dir = 1;
                }
                sb.step(0, &[w0_dir, 1], false);
            }
        }
    }
    assert_eq!(emitted, l);
    sb.finish()
}

// --- Inverse-Square Two-Exception Geometries (Catalogue Rows 27, 28, 29) ---

#[derive(Clone)]
struct ChainFam {
    owner: usize,
    start: usize,
    stop: usize,
    hops: Vec<(usize, usize)>,
}

impl ChainFam {
    fn held(&self, t: usize) -> usize {
        match self.hops.binary_search_by_key(&t, |&(_, u)| u) {
            Ok(idx) => self.hops[idx].0,
            Err(0) => self.owner,
            Err(idx) => self.hops[idx - 1].0,
        }
    }

    fn shadow(&self, t: usize) -> usize {
        if self.owner < t && t <= self.stop {
            (self.start + 1).max(self.held(t))
        } else {
            t
        }
    }
}

fn extract_chain_fams(xs: &[Vec<i64>], t_horizon: usize) -> Vec<ChainFam> {
    let mut grouped: HashMap<(usize, bool, usize), Vec<(usize, usize)>> = HashMap::new();
    for (h, walk) in xs.iter().enumerate() {
        let mut last_visit: HashMap<i64, usize> = HashMap::new();
        for u in 0..t_horizon {
            let pos = walk[u];
            if let Some(p) = last_visit.insert(pos, u) {
                if u >= p + 2 {
                    let side_up = walk[p + 1] > pos;
                    let mut best_dist = 0i64;
                    let mut owner = p + 1;
                    for s in (p + 1)..u {
                        let dist = (walk[s] - pos).abs();
                        if dist > best_dist {
                            best_dist = dist;
                            owner = s;
                        }
                    }
                    grouped.entry((h, side_up, owner)).or_default().push((p, u));
                }
            }
        }
    }
    let mut fams = Vec::with_capacity(grouped.len());
    for ((_h, _side, owner), mut hops) in grouped {
        hops.sort_unstable_by_key(|&(_, u)| u);
        let start = hops.last().unwrap().0;
        let stop = hops.last().unwrap().1;
        fams.push(ChainFam {
            owner,
            start,
            stop,
            hops,
        });
    }
    fams.sort_unstable_by_key(|f| f.owner);
    fams
}

fn build_two_head_unit_banks(
    t_horizon: usize,
    d0: usize,
    w: &[usize],
) -> (Vec<i64>, Vec<i64>, Vec<usize>) {
    let n = w.len();
    let mut a = Vec::with_capacity(n + 1);
    a.push(d0);
    for j in 0..n {
        a.push(a[j] + 2 * w[j]);
    }
    let mut h0_delta = vec![0i64; t_horizon];
    let mut h1_delta = vec![0i64; t_horizon];
    for j in 0..n {
        let arr = if j % 2 == 0 {
            &mut h0_delta
        } else {
            &mut h1_delta
        };
        let wj = w[j];
        let aj = a[j];
        for t in aj..(aj + wj) {
            arr[t] = 1;
        }
        for t in (aj + wj)..(aj + 2 * wj) {
            arr[t] = -1;
        }
        for t in (aj + 2 * wj)..(aj + 3 * wj) {
            arr[t] = 1;
        }
    }
    let integrate = |dlt: &[i64]| -> Vec<i64> {
        let mut out = vec![0i64; t_horizon];
        let mut c = 0i64;
        for t in 0..t_horizon {
            out[t] = c;
            c += dlt[t];
        }
        out
    };
    (integrate(&h0_delta), integrate(&h1_delta), a)
}

fn build_lemma_a_walk(t_horizon: usize, hops: &[(usize, usize)]) -> Vec<i64> {
    let mut delta = vec![0i64; t_horizon];
    for &(p, u) in hops {
        delta[p] = 1;
        delta[u - 1] = -1;
    }
    let mut walk = vec![0i64; t_horizon];
    let mut cur = 0i64;
    for t in 0..t_horizon {
        walk[t] = cur;
        cur += delta[t];
    }
    walk
}

fn schedule_from_position_traces(
    id: &'static str,
    title: &'static str,
    d: usize,
    b: usize,
    x: &[usize],
    xs: Vec<Vec<i64>>,
    out_times: &[usize],
) -> Schedule {
    let t_horizon = x.len();
    let k = xs.len();
    let mut sb = ScheduleBuilder::new(id, title, d, b, k, ComputationKind::GeometryOnly);
    let mut out_ptr = 0usize;
    let mut dwork = vec![0i64; k];
    for t in 0..t_horizon {
        let din = if t + 1 < t_horizon {
            x[t + 1] as i64 - x[t] as i64
        } else {
            0
        };
        for j in 0..k {
            dwork[j] = if t + 1 < t_horizon {
                xs[j][t + 1] - xs[j][t]
            } else {
                0
            };
        }
        let emit = out_ptr < out_times.len() && out_times[out_ptr] == t;
        if emit {
            out_ptr += 1;
        }
        sb.step(din, &dwork, emit);
    }
    sb.finish()
}

pub fn build_cat_row28_gis2(d: usize, b: usize) -> Schedule {
    assert!(d >= 64 && b >= 1);
    let l = d * d * b;
    let n = ((d as f64).sqrt() as usize) / 2;
    let m: Vec<usize> = (0..n).map(|s| l / (4 * (s + 1) * (s + 1))).collect();
    let w: Vec<usize> = (0..n).map(|j| m[n - 1 - j]).collect();
    let t_horizon = 16 * l;

    let mut x = vec![0usize; t_horizon];
    for s in 0..l {
        x[s] = s;
        x[7 * l + s] = s;
    }
    for s in l..=(2 * l - 2) {
        x[s] = 2 * l - 2 - s;
        x[7 * l + s] = 2 * l - 2 - s;
    }

    let mut hh = vec![0i64; t_horizon];
    for (t, v) in hh.iter_mut().enumerate().take(l + 1) {
        *v = t as i64;
    }
    for v in hh.iter_mut().take(2 * l + 1).skip(l + 1) {
        *v = l as i64;
    }
    for (t, v) in hh.iter_mut().enumerate().take(3 * l + 1).skip(2 * l + 1) {
        *v = (3 * l - t) as i64;
    }

    let (ha0, ha1, a_early) = build_two_head_unit_banks(t_horizon, 3 * l + 1, &w);
    let r_times: Vec<usize> = (1..=(2 * n + 1)).map(|k| 9 * l + 1 + k).collect();
    let mut hbr_delta = vec![0i64; t_horizon];
    let p_br = a_early[n];
    for v in hbr_delta.iter_mut().take(p_br + l).skip(p_br) {
        *v = 1;
    }
    for v in hbr_delta
        .iter_mut()
        .take(p_br + 2 * l - (2 * n + 1))
        .skip(p_br + l)
    {
        *v = -1;
    }
    for &rk in &r_times {
        hbr_delta[rk - 1] = -1;
    }
    let mut hbr = vec![0i64; t_horizon];
    let mut cur = 0i64;
    for t in 0..t_horizon {
        hbr[t] = cur;
        cur += hbr_delta[t];
    }

    let (he0, he1, a_late) = build_two_head_unit_banks(t_horizon, 10 * l, &w);
    let p_fun = a_late[n];
    let mut hfun_delta = vec![0i64; t_horizon];
    for v in hfun_delta.iter_mut().take(p_fun + l).skip(p_fun) {
        *v = 1;
    }
    for v in hfun_delta
        .iter_mut()
        .take(p_fun + 2 * l - 2)
        .skip(p_fun + l)
    {
        *v = -1;
    }
    let out_base = p_fun + 2 * l - 2;
    let out_times: Vec<usize> = (0..l).map(|z| out_base + z).collect();
    hfun_delta[out_base + l] = -1;
    hfun_delta[out_base + l + 1] = -1;
    let mut hfun = vec![0i64; t_horizon];
    cur = 0;
    for t in 0..t_horizon {
        hfun[t] = cur;
        cur += hfun_delta[t];
    }

    let q_cnt = (2 * n) * (2 * n);
    let mut z_early = Vec::with_capacity(q_cnt + 1);
    for k in 1..=(2 * n) {
        let delta_k = 2 * n + 1 - k;
        for step_m in 1..=(2 * n) {
            let z = if step_m % 2 == 1 {
                a_early[n + 1 - (step_m + 1) / 2] - delta_k
            } else {
                a_early[n - step_m / 2] + delta_k
            };
            z_early.push(z);
        }
    }
    z_early.sort_unstable();
    z_early.dedup();
    z_early.push(*z_early.last().unwrap() + 1);
    let old_hops: Vec<(usize, usize)> = z_early
        .iter()
        .enumerate()
        .map(|(idx, &uz)| (2 * l + 2 + (q_cnt - idx), uz))
        .collect();
    let hold_walk = build_lemma_a_walk(t_horizon, &old_hops);

    let mut v_late: Vec<usize> = (1..=(2 * n))
        .map(|step_m| {
            if step_m % 2 == 1 {
                a_late[n + 1 - (step_m + 1) / 2] - 2
            } else {
                a_late[n - step_m / 2] + 2
            }
        })
        .collect();
    v_late.reverse();

    let m_raw = l / 4 - 2;
    let mut new_hops: Vec<(usize, usize)> = Vec::with_capacity(2 * n + m_raw + 1);
    for (idx, &uv) in v_late.iter().enumerate() {
        new_hops.push((r_times[2 * n - 1 - idx], uv));
    }
    for r in 0..m_raw {
        new_hops.push((7 * l + 4 * (m_raw - r), out_times[4 * r]));
    }
    new_hops.push((7 * l + 1, out_times[4 * (m_raw - 1)] + 1));
    let hnew_walk = build_lemma_a_walk(t_horizon, &new_hops);

    schedule_from_position_traces(
        "cat_row28_gis2",
        "Catalogue Row 28: Nine-head inverse-square two-exception geometry (G_IS2)",
        d,
        b,
        &x,
        vec![hh, ha0, ha1, hbr, he0, he1, hfun, hold_walk, hnew_walk],
        &out_times,
    )
}

fn select_dyadic_old_pairs(
    n: usize,
    l: usize,
    tb: &[usize],
    a_early: &[usize],
    chain_fams: &[ChainFam],
    x: &[usize],
) -> Vec<(usize, usize)> {
    let mut old_pairs: Vec<(usize, usize)> = Vec::with_capacity(4 * n * n + 1);
    let mut used_raws: HashSet<usize> = HashSet::with_capacity(4 * n * n);
    for r in 1..=(2 * n) {
        let m_scale = (usize::BITS - 1 - r.leading_zeros()) as usize;
        let p2 = 1usize << m_scale;
        let j_sub = r - p2;
        let win_lo = tb[r] + 2;
        let win_hi = tb[r + 1] - 2;
        let psi_vals: Vec<(usize, usize)> = (win_lo..=win_hi)
            .map(|t0| {
                let mut cur = t0;
                for link in (0..=r).rev() {
                    cur = chain_fams[link].shadow(cur);
                }
                (t0, x[cur])
            })
            .filter(|&(_, raw)| raw >= 1 && raw + 3 <= l && !used_raws.contains(&raw))
            .collect();
        let mut chosen_t_for_k = Vec::with_capacity(2 * n);
        for k in 1..=(2 * n) {
            let sub_frac = if k <= 2 * p2 {
                1.0 - (2 * k - 1) as f64 / (4 * p2) as f64
            } else {
                (2 * n + 1 - k) as f64 / ((4 * p2) * (2 * n + 1)) as f64
            };
            let theta = ((p2 - 1 - j_sub) as f64 + sub_frac) / (p2 as f64);
            let target_raw = (theta * (l as f64)).round() as isize;
            let (best_t, best_raw) = if r % 2 == 1 {
                let max_allowed_t = chosen_t_for_k
                    .last()
                    .map(|&prev: &usize| prev - 1)
                    .unwrap_or(usize::MAX);
                *psi_vals
                    .iter()
                    .enumerate()
                    .filter(|&(idx, &(t_cand, _))| idx >= (2 * n - k) && t_cand <= max_allowed_t)
                    .min_by_key(|&(_, &(_, raw))| (raw as isize - target_raw).abs())
                    .unwrap()
                    .1
            } else {
                let min_allowed_t = chosen_t_for_k
                    .last()
                    .map(|&prev: &usize| prev + 1)
                    .unwrap_or(0);
                let len = psi_vals.len();
                *psi_vals
                    .iter()
                    .enumerate()
                    .filter(|&(idx, &(t_cand, _))| {
                        idx + (2 * n - k) < len && t_cand >= min_allowed_t
                    })
                    .min_by_key(|&(_, &(_, raw))| (raw as isize - target_raw).abs())
                    .unwrap()
                    .1
            };
            chosen_t_for_k.push(best_t);
            used_raws.insert(best_raw);
            let delta_k = 2 * n + 1 - k;
            let z_kr = if r % 2 == 1 {
                a_early[n + 1 - (r + 1) / 2] - delta_k
            } else {
                a_early[n - r / 2] + delta_k
            };
            old_pairs.push((best_t, z_kr));
        }
    }
    old_pairs.sort_unstable_by_key(|&(_, u)| u);
    old_pairs.push((3 * l + 1, old_pairs.last().unwrap().1 + 1));
    old_pairs
}

pub fn build_cat_row29_gis2_gap(d: usize, b: usize) -> Schedule {
    assert!(d >= 64 && b >= 1);
    let l = d * d * b;
    let n = (d as f64 / 2.0 + 1e-9).cbrt() as usize;
    let m: Vec<usize> = (0..n).map(|s| l / (4 * (s + 1) * (s + 1))).collect();
    let w: Vec<usize> = (0..n).map(|j| m[n - 1 - j]).collect();
    let t_horizon = 18 * l;

    let mut x = vec![0usize; t_horizon];
    for s in 0..l {
        x[s] = s;
        x[9 * l + s] = s;
    }
    for s in l..=(2 * l - 2) {
        x[s] = 2 * l - 2 - s;
        x[9 * l + s] = 2 * l - 2 - s;
    }

    let integrate = |dlt: &[i64]| -> Vec<i64> {
        let mut out = vec![0i64; t_horizon];
        let mut c = 0i64;
        for t in 0..t_horizon {
            out[t] = c;
            c += dlt[t];
        }
        out
    };

    let mut hh = vec![0i64; t_horizon];
    for (t, v) in hh.iter_mut().enumerate().take(l + 1) {
        *v = t as i64;
    }
    for v in hh.iter_mut().take(2 * l + 1).skip(l + 1) {
        *v = l as i64;
    }
    for (t, v) in hh.iter_mut().enumerate().take(3 * l + 1).skip(2 * l + 1) {
        *v = (3 * l - t) as i64;
    }

    let mut tb = vec![2 * l, 3 * l];
    for &mi in &m {
        let prev = *tb.last().unwrap();
        tb.push(prev + mi);
        tb.push(prev + 2 * mi);
    }
    let mut hb0_delta = vec![0i64; t_horizon];
    let mut hb1_delta = vec![0i64; t_horizon];
    for i in 0..n {
        let arr = if i % 2 == 0 {
            &mut hb0_delta
        } else {
            &mut hb1_delta
        };
        let mi = m[i];
        let a_win = tb[2 * i];
        let b_win = tb[2 * i + 1];
        let d_win = b_win - a_win;
        for j in 0..mi {
            let tau = if j + 1 < mi {
                a_win + 1 + (j * (d_win - 2)) / (mi - 1)
            } else {
                b_win - 1
            };
            arr[tau] = 1;
        }
        for v in arr.iter_mut().take(b_win + mi).skip(b_win) {
            *v = -1;
        }
        for v in arr.iter_mut().take(b_win + 2 * mi).skip(b_win + mi) {
            *v = 1;
        }
    }
    let hb0 = integrate(&hb0_delta);
    let hb1 = integrate(&hb1_delta);
    let chain_fams = extract_chain_fams(&[hh.clone(), hb0.clone(), hb1.clone()], t_horizon);

    let (ha0, ha1, a_early) = build_two_head_unit_banks(t_horizon, 5 * l, &w);
    let r_times: Vec<usize> = (1..=(2 * n + 1)).map(|k| 11 * l + 1 + k).collect();
    let mut hbr_delta = vec![0i64; t_horizon];
    let p_br = a_early[n];
    for v in hbr_delta.iter_mut().take(p_br + l).skip(p_br) {
        *v = 1;
    }
    for v in hbr_delta
        .iter_mut()
        .take(p_br + 2 * l - (2 * n + 1))
        .skip(p_br + l)
    {
        *v = -1;
    }
    for &rk in &r_times {
        hbr_delta[rk - 1] = -1;
    }
    let hbr = integrate(&hbr_delta);

    let (he0, he1, a_late) = build_two_head_unit_banks(t_horizon, 12 * l, &w);
    let p_fun = a_late[n];
    let mut hfun_delta = vec![0i64; t_horizon];
    for v in hfun_delta.iter_mut().take(p_fun + l).skip(p_fun) {
        *v = 1;
    }
    for v in hfun_delta
        .iter_mut()
        .take(p_fun + 2 * l - 2)
        .skip(p_fun + l)
    {
        *v = -1;
    }
    let out_base = p_fun + 2 * l - 2;
    let out_times: Vec<usize> = (0..l).map(|z| out_base + z).collect();
    hfun_delta[out_base + l] = -1;
    hfun_delta[out_base + l + 1] = -1;
    let hfun = integrate(&hfun_delta);

    let old_pairs = select_dyadic_old_pairs(n, l, &tb, &a_early, &chain_fams, &x);
    let hold_walk = build_lemma_a_walk(t_horizon, &old_pairs);

    let mut v_late: Vec<usize> = (1..=(2 * n))
        .map(|step_m| {
            if step_m % 2 == 1 {
                a_late[n + 1 - (step_m + 1) / 2] - 2
            } else {
                a_late[n - step_m / 2] + 2
            }
        })
        .collect();
    v_late.reverse();
    let m_raw = l / 4 - 2;
    let mut new_hops: Vec<(usize, usize)> = Vec::with_capacity(2 * n + m_raw + 1);
    for (idx, &uv) in v_late.iter().enumerate() {
        new_hops.push((r_times[2 * n - 1 - idx], uv));
    }
    for r in 0..m_raw {
        new_hops.push((9 * l + 4 * (m_raw - r), out_times[4 * r]));
    }
    new_hops.push((9 * l + 1, out_times[4 * (m_raw - 1)] + 1));
    let hnew_walk = build_lemma_a_walk(t_horizon, &new_hops);

    schedule_from_position_traces(
        "cat_row29_gis2_gap",
        "Catalogue Row 29: Eleven-head small-gap inverse-square geometry (G_IS2_gap)",
        d,
        b,
        &x,
        vec![
            hh, hb0, hb1, ha0, ha1, hbr, he0, he1, hfun, hold_walk, hnew_walk,
        ],
        &out_times,
    )
}

pub fn build_cat_row27_gis2_swept(d: usize, b: usize) -> Schedule {
    assert!(d >= 64 && b >= 1);
    let l = d * d * b;
    let n = ((d as f64 / 2.0).cbrt().floor() as usize).max(3);
    let m: Vec<usize> = (0..n).map(|s| l / (4 * (s + 1) * (s + 1))).collect();
    let w: Vec<usize> = (0..n).map(|j| m[n - 1 - j]).collect();
    let t_horizon = 20 * l;

    let mut x = vec![0usize; t_horizon];
    for s in 0..l {
        x[s] = s;
        x[10 * l + s] = s;
    }
    for s in l..=(2 * l - 2) {
        x[s] = 2 * l - 2 - s;
        x[10 * l + s] = 2 * l - 2 - s;
    }

    let integrate = |dlt: &[i64]| -> Vec<i64> {
        let mut out = vec![0i64; t_horizon];
        let mut c = 0i64;
        for t in 0..t_horizon {
            out[t] = c;
            c += dlt[t];
        }
        out
    };

    let mut hh = vec![0i64; t_horizon];
    for (t, v) in hh.iter_mut().enumerate().take(l + 1) {
        *v = t as i64;
    }
    for v in hh.iter_mut().take(2 * l + 1).skip(l + 1) {
        *v = l as i64;
    }
    for (t, v) in hh.iter_mut().enumerate().take(3 * l + 1).skip(2 * l + 1) {
        *v = (3 * l - t) as i64;
    }

    let mut tb = vec![2 * l, 3 * l];
    for &mi in &m {
        let prev = *tb.last().unwrap();
        tb.push(prev + mi);
        tb.push(prev + 2 * mi);
    }
    let mut hb0_delta = vec![0i64; t_horizon];
    let mut hb1_delta = vec![0i64; t_horizon];
    for i in 0..n {
        let arr = if i % 2 == 0 {
            &mut hb0_delta
        } else {
            &mut hb1_delta
        };
        let mi = m[i];
        let a_win = tb[2 * i];
        let b_win = tb[2 * i + 1];
        let d_win = b_win - a_win;
        for j in 0..mi {
            let tau = if j + 1 < mi {
                a_win + 1 + (j * (d_win - 2)) / (mi - 1)
            } else {
                b_win - 1
            };
            arr[tau] = 1;
        }
        for v in arr.iter_mut().take(b_win + mi).skip(b_win) {
            *v = -1;
        }
        for v in arr.iter_mut().take(b_win + 2 * mi).skip(b_win + mi) {
            *v = 1;
        }
    }
    let hb0 = integrate(&hb0_delta);
    let hb1 = integrate(&hb1_delta);
    let chain_fams = extract_chain_fams(&[hh.clone(), hb0.clone(), hb1.clone()], t_horizon);

    let (ha0, ha1, a_early) = build_two_head_unit_banks(t_horizon, 5 * l, &w);
    let p_br = a_early[n];
    let mut hbr_delta = vec![0i64; t_horizon];
    for v in hbr_delta.iter_mut().take(p_br + l).skip(p_br) {
        *v = 1;
    }
    let down_steps_initial = l - 2 * n;
    for v in hbr_delta
        .iter_mut()
        .take(p_br + l + down_steps_initial)
        .skip(p_br + l)
    {
        *v = -1;
    }
    let mut j_br_ranges: Vec<(usize, usize)> = Vec::with_capacity(2 * n);
    let mut cur_br = 12 * l + 4;
    for r in 1..=(2 * n) {
        let len_r = m[(r + 1) / 2 - 1];
        let start_r = cur_br;
        let end_r = start_r + len_r;
        j_br_ranges.push((start_r, end_r));
        hbr_delta[end_r] = -1;
        cur_br = end_r + 2;
    }
    let hbr = integrate(&hbr_delta);

    let s_rev = tb[2 * n + 1];
    let rev_span = s_rev - 2 * l;
    let te: Vec<usize> = (0..=(2 * n + 1))
        .map(|idx| 14 * l + (s_rev - tb[2 * n + 1 - idx]))
        .collect();
    let out_base = te[2 * n];
    let out_times: Vec<usize> = (0..l).map(|z| out_base + z).collect();

    let mut he0 = vec![hb0[s_rev]; t_horizon];
    let mut he1 = vec![hb1[s_rev]; t_horizon];
    for u_loc in 0..=rev_span {
        he0[14 * l + u_loc] = hb0[s_rev - u_loc];
        he1[14 * l + u_loc] = hb1[s_rev - u_loc];
    }
    for t in (14 * l + rev_span + 1)..t_horizon {
        he0[t] = hb0[2 * l];
        he1[t] = hb1[2 * l];
    }

    let old_pairs = select_dyadic_old_pairs(n, l, &tb, &a_early, &chain_fams, &x);
    let hold_walk = build_lemma_a_walk(t_horizon, &old_pairs);

    let mut new_pairs: Vec<(usize, usize)> = Vec::new();
    for idx in 0..(2 * n) {
        let r = 2 * n - idx;
        let u_lo = te[idx] + 2;
        let u_hi = te[idx + 1] - 2;
        let (_p_start, p_end) = j_br_ranges[r - 1];
        let count_u = u_hi - u_lo + 1;
        for off in 0..count_u {
            new_pairs.push((p_end - 1 - off, u_lo + off));
        }
    }
    let u_outer = new_pairs.last().unwrap().1 + 1;
    new_pairs.push((10 * l + 1, u_outer));
    let hnew_walk = build_lemma_a_walk(t_horizon, &new_pairs);

    schedule_from_position_traces(
        "cat_row27_gis2_swept",
        "Catalogue Row 27: Swept inverse-square two-exception geometry (G_IS2_swept)",
        d,
        b,
        &x,
        vec![hh, hb0, hb1, ha0, ha1, hbr, he0, he1, hold_walk, hnew_walk],
        &out_times,
    )
}

pub fn build_cat_row30_mirrored_dyadic(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let mut sb = ScheduleBuilder::new(
        "cat_row30_mirrored_dyadic",
        "Catalogue Row 30: Mirrored dyadic fold-back cascade (S2b_dyadic_fold)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    sb.move_work_to(1, (l - 1) as i64);
    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        let dw1 = if u + 1 < l { -1 } else { 0 };
        sb.step(1, &[dw0, dw1], false);
    }

    let mut span = l;
    while span >= b {
        sb.move_two_works_to(0, (span - 1) as i64, 1, 0);
        for u in 0..span {
            let dw0 = if u + 1 < span { -1 } else { 0 };
            let dw1 = if u + 1 < span { 1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }
        span /= 2;
    }

    sb.move_two_works_to(0, 0, 1, 0);
    for u in 0..l {
        let dw = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[dw, dw], true);
    }
    sb.finish()
}

pub fn build_cat_row32_dyadic_fold(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let w = d * b;
    let scales = (d.ilog2() as usize).max(1);
    let mut sb = ScheduleBuilder::new(
        "cat_row32_dyadic_fold",
        "Catalogue Row 32: Dyadic geometric + sub-row butterfly fold (S2_dyadic_fold)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        sb.step(1, &[dw0, 0], false);
    }
    sb.move_work_to(0, 0);

    for r in 0..=scales {
        let span0 = (l >> r).max(b);
        let span1 = (l >> (r + 1)).max(b);
        sb.move_work_to(1, (span1 - 1) as i64);
        for u in 0..span0 {
            let dw0 = if u + 1 < span0 { 1 } else { 0 };
            let dw1 = if sb.cur_work[1] > 0 { -1 } else { 0 };
            sb.step(0, &[dw0, dw1], false);
        }
        for u in 0..span0 {
            let dw0 = if u + 1 < span0 { -1 } else { 0 };
            let dw1 = if (sb.cur_work[1] as usize) + 1 < span1 {
                1
            } else {
                0
            };
            sb.step(0, &[dw0, dw1], false);
        }
    }
    sb.move_two_works_to(0, 0, 1, 0);

    for i in 0..d {
        let s = i % scales;
        let blk = (b << s).min(w);
        let n_blks = w / blk;
        for g in 0..n_blks {
            let base = (i * w + g * blk) as i64;
            sb.move_two_works_to(0, base, 1, 0);
            for u in 0..blk {
                let d01 = if u + 1 < blk { 1 } else { 0 };
                sb.step(0, &[d01, d01], false);
            }
            for u in 0..blk {
                let d01 = if u + 1 < blk { -1 } else { 0 };
                sb.step(0, &[d01, d01], false);
            }
            for u in 0..blk {
                let d01 = if u + 1 < blk { 1 } else { 0 };
                sb.step(0, &[d01, d01], false);
            }
        }
    }

    sb.move_two_works_to(0, (l - 1) as i64, 1, 0);
    for u in 0..l {
        let dw0 = if u + 1 < l { -1 } else { 0 };
        let in_row = u % w;
        let dw1 = if in_row + 1 < w {
            if (u / w) % 2 == 0 { 1 } else { -1 }
        } else {
            0
        };
        sb.step(0, &[dw0, dw1], true);
    }
    sb.finish()
}

fn stack_copy_interval_fresh(
    sb: &mut ScheduleBuilder,
    src_base: i64,
    dst_base: i64,
    len: usize,
    reverse_map: bool,
) {
    let base1 = sb.cur_work[1];
    let push_start_w0 = if reverse_map {
        src_base
    } else {
        src_base + (len as i64) - 1
    };
    while sb.cur_work[0] < push_start_w0 {
        sb.step(0, &[1, 0], false);
    }
    while sb.cur_work[0] > push_start_w0 {
        sb.step(0, &[-1, 0], false);
    }
    let dw0_push = if reverse_map { 1i64 } else { -1i64 };
    for u in 0..len {
        let dw0 = if u + 1 < len { dw0_push } else { 0 };
        sb.step(0, &[dw0, 1], false);
    }
    while sb.cur_work[0] < dst_base {
        sb.step(0, &[1, 0], false);
    }
    while sb.cur_work[0] > dst_base {
        sb.step(0, &[-1, 0], false);
    }
    sb.step(0, &[0, -1], false);
    for _ in 1..len {
        sb.step(0, &[1, -1], false);
    }
    debug_assert_eq!(sb.cur_work[1], base1);
    for _ in 0..=len {
        sb.step(0, &[0, 1], false);
    }
}

fn stack_cyclic_shift_exact_band(
    sb: &mut ScheduleBuilder,
    src_base: i64,
    dst_base: i64,
    len: usize,
    shift: usize,
) {
    let sh = shift % len;
    if sh == 0 {
        stack_copy_interval_fresh(sb, src_base, dst_base, len, false);
        return;
    }
    let base1 = sb.cur_work[1];
    let p1_start = src_base + (sh as i64) - 1;
    while sb.cur_work[0] < p1_start {
        sb.step(0, &[1, 0], false);
    }
    while sb.cur_work[0] > p1_start {
        sb.step(0, &[-1, 0], false);
    }
    for u in 0..sh {
        let dw0 = if u + 1 < sh { -1 } else { 0 };
        sb.step(0, &[dw0, 1], false);
    }
    let p2_start = src_base + (len as i64) - 1;
    while sb.cur_work[0] < p2_start {
        sb.step(0, &[1, 0], false);
    }
    while sb.cur_work[0] > p2_start {
        sb.step(0, &[-1, 0], false);
    }
    let rem = len - sh;
    for u in 0..rem {
        let dw0 = if u + 1 < rem { -1 } else { 0 };
        sb.step(0, &[dw0, 1], false);
    }
    while sb.cur_work[0] < dst_base {
        sb.step(0, &[1, 0], false);
    }
    while sb.cur_work[0] > dst_base {
        sb.step(0, &[-1, 0], false);
    }
    sb.step(0, &[0, -1], false);
    for _ in 1..len {
        sb.step(0, &[1, -1], false);
    }
    debug_assert_eq!(sb.cur_work[1], base1);
    for _ in 0..=len {
        sb.step(0, &[0, 1], false);
    }
}

pub fn build_cat_row36_lifo_fanout(d: usize, b: usize) -> Schedule {
    assert!(d.is_power_of_two() && d >= 8);
    let l = d * d * b;
    let r_max = (d.trailing_zeros() as usize).saturating_sub(2).max(1);
    let mut sb = ScheduleBuilder::new(
        "cat_row36_lifo_fanout",
        "Catalogue Row 36: Binary-tree LIFO pushdown fan-out cascade (Adv_Leaf1_lifo_fanout)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    let block_slot = |r: usize, slot: i64| -> i64 {
        16 * ((l - (l >> r)) as i64) + slot * ((l >> r) as i64)
    };

    let warm_w = ((d * b) / 2).max(2) as i64;
    let mut w0_dir = -1i64;
    for _ in 0..l {
        if sb.cur_work[0] <= -warm_w {
            w0_dir = 1;
        } else if sb.cur_work[0] >= -1 {
            w0_dir = -1;
        }
        sb.step(0, &[w0_dir, 0], false);
    }
    while sb.cur_work[0] < 0 {
        sb.step(0, &[1, 0], false);
    }

    for u in 0..l {
        let dx = if u + 1 < l { 1 } else { 0 };
        sb.step(dx, &[dx, 0], false);
    }

    let mut a_arenas = vec![0i64; r_max + 1];
    let mut mix_arenas = vec![0i64; r_max + 1];
    a_arenas[0] = block_slot(0, 0);
    {
        let m0 = block_slot(0, 1);
        let sh0 = (((l as f64) * 0.618_033_988_75).round() as usize)
            .max(b + 1)
            .min(l - 1);
        stack_cyclic_shift_exact_band(&mut sb, a_arenas[0], m0, l, sh0);
        mix_arenas[0] = m0;
    }

    for r in 1..=r_max {
        let m_r = l >> r;
        let prev_a = a_arenas[r - 1];
        let cur_a = block_slot(r, 0);
        stack_copy_interval_fresh(&mut sb, prev_a, cur_a, m_r, false);
        let sh_fold = (((m_r as f64) * 0.381_966_011_25).round() as usize)
            .max(1)
            .min(m_r - 1);
        stack_cyclic_shift_exact_band(&mut sb, prev_a + (m_r as i64), cur_a, m_r, sh_fold);
        a_arenas[r] = cur_a;

        let mut mx = cur_a;
        let rounds_here = if r >= 2 { 2usize } else { 1usize };
        for t in 0..rounds_here {
            let nxt = block_slot(r, (t + 1) as i64);
            let sh = ((((m_r as f64) * 0.618_033_988_75).round() as usize) * (t + 1)
                + (r * 17 + 5) * b)
                % m_r;
            stack_cyclic_shift_exact_band(&mut sb, mx, nxt, m_r, sh.max(1));
            stack_copy_interval_fresh(&mut sb, mx, nxt, m_r, true);
            mx = nxt;
        }
        mix_arenas[r] = mx;
    }

    let mut cur_b = mix_arenas[r_max];
    for r in (0..r_max).rev() {
        let m_child = l >> (r + 1);
        let m_cur = l >> r;
        let nxt_b = block_slot(r, if r == 0 { 2 } else { 4 });
        let sh_lo = (((m_child as f64) * 0.276_393_202_25).round() as usize) % m_child;
        let sh_hi = (((m_child as f64) * 0.723_606_797_75).round() as usize) % m_child;
        stack_cyclic_shift_exact_band(&mut sb, cur_b, nxt_b, m_child, sh_lo.max(1));
        stack_cyclic_shift_exact_band(
            &mut sb,
            cur_b,
            nxt_b + (m_child as i64),
            m_child,
            sh_hi.max(1),
        );
        stack_copy_interval_fresh(&mut sb, mix_arenas[r], nxt_b, m_cur, (r & 1) == 1);
        cur_b = nxt_b;
    }

    while sb.cur_work[0] < cur_b {
        sb.step(0, &[1, 0], false);
    }
    while sb.cur_work[0] > cur_b {
        sb.step(0, &[-1, 0], false);
    }
    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        sb.step(0, &[dw0, 0], true);
    }
    sb.finish()
}

pub fn build_cat_row37_tapped_cascade(d: usize, b: usize) -> Schedule {
    let l = d * d * b;
    let s_taps = (d.ilog2() as usize).max(2);
    let m_meso = (l / s_taps).max(2 * b);
    let mut sb = ScheduleBuilder::new(
        "cat_row37_tapped_cascade",
        "Catalogue Row 37: Equal-volume tapped mesoscopic cascade (Adv_BTL5_tapped)",
        d,
        b,
        2,
        ComputationKind::GeometryOnly,
    );

    let stack_shift_fresh =
        |sb: &mut ScheduleBuilder, src: i64, dst: i64, len: usize, sh: usize, rev_pop: bool| {
            let sh = (sh % len).max(1).min(len - 1);
            sb.move_work_to(0, src + sh as i64);
            for _ in 0..(len - sh) {
                sb.step(0, &[1, 1], false);
            }
            sb.move_work_to(0, src);
            for _ in 0..sh {
                sb.step(0, &[1, 1], false);
            }
            if !rev_pop {
                sb.move_work_to(0, dst);
                for idx in 0..len {
                    let dw0 = if idx + 1 < len { 1 } else { 0 };
                    sb.step(0, &[dw0, -1], false);
                }
            } else {
                sb.move_work_to(0, dst + (len as i64) - 1);
                for idx in 0..len {
                    let dw0 = if idx + 1 < len { -1 } else { 0 };
                    sb.step(0, &[dw0, -1], false);
                }
            }
            for _ in 0..=len {
                sb.step(0, &[0, 1], false);
            }
        };

    for u in 0..l {
        let dw0 = if u + 1 < l { 1 } else { 0 };
        sb.step(1, &[dw0, 0], false);
    }
    sb.move_work_to(0, 0);
    for idx in 0..l {
        let dw0 = if idx + 1 < l { 1 } else { 0 };
        sb.step(0, &[dw0, 1], false);
    }
    sb.move_work_to(0, 0);
    let mut w0_dir = 1i64;
    for _ in 0..l {
        if sb.cur_work[0] >= (m_meso as i64) - 1 {
            w0_dir = -1;
        } else if sb.cur_work[0] <= 0 {
            w0_dir = 1;
        }
        sb.step(0, &[w0_dir, -1], false);
    }
    for _ in 0..=l {
        sb.step(0, &[0, 1], false);
    }

    let slot_x = |r: usize| -> i64 { ((2 * r + 2) * m_meso) as i64 };
    let slot_tap = |r: usize| -> i64 { ((2 * r + 3) * m_meso) as i64 };

    let mut cur_src = 0i64;
    for r in 0..s_taps {
        let mid_x = slot_x(r);
        let sh1 = ((((m_meso as f64) * 0.618_033_988_75).round() as usize) * (2 * r + 1)
            + 3 * b
            + r)
            % m_meso;
        let sh2 = ((((m_meso as f64) * 0.381_966_011_25).round() as usize) * (2 * r + 2)
            + 5 * b
            + r)
            % m_meso;
        stack_shift_fresh(&mut sb, cur_src, mid_x, m_meso, sh1, true);
        stack_shift_fresh(&mut sb, mid_x, mid_x, m_meso, sh2, false);
        cur_src = mid_x;
    }

    stack_shift_fresh(
        &mut sb,
        slot_x(s_taps - 1),
        slot_tap(s_taps - 1),
        m_meso,
        1,
        false,
    );
    for r in (0..s_taps.saturating_sub(1)).rev() {
        let sh_tap =
            ((((m_meso as f64) * 0.276_393_202_25).round() as usize) * (r + 1) + b + 1) % m_meso;
        stack_shift_fresh(&mut sb, slot_tap(r + 1), slot_tap(r), m_meso, sh_tap, false);
        let sh_ov = ((((m_meso as f64) * 0.723_606_797_75).round() as usize) * (r + 1)
            + 2 * b
            + 1)
            % m_meso;
        stack_shift_fresh(
            &mut sb,
            slot_x(r),
            slot_tap(r),
            m_meso,
            sh_ov,
            (r & 1) == 1,
        );
    }

    let tap_base = slot_tap(0);
    sb.move_work_to(0, tap_base);
    w0_dir = 1;
    for _ in 0..l {
        if sb.cur_work[0] >= tap_base + (m_meso as i64) - 1 {
            w0_dir = -1;
        } else if sb.cur_work[0] <= tap_base {
            w0_dir = 1;
        }
        sb.step(0, &[w0_dir, 1], false);
    }
    let out_base = ((2 * s_taps + 4) * m_meso) as i64;
    sb.move_work_to(0, out_base);
    for idx in 0..l {
        let dw0 = if idx + 1 < l { 1 } else { 0 };
        sb.step(0, &[dw0, -1], true);
    }
    sb.finish()
}
