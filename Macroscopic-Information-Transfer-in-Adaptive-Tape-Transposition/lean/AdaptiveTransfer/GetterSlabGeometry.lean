import AdaptiveTransfer.GetterSlabSelection
import AdaptiveTransfer.GetterFootprint

/-! The actual p-port slab selection with the manuscript constants. -/

namespace AdaptiveTransfer.Getter
open Finset NativeRelations BoundedNesting

noncomputable def portSlabWidth (P a p : ℕ) (c : ℝ) : ℕ :=
  ⌈(P : ℝ) / (320 * a * p * c)⌉₊

noncomputable def portRunCap (a p : ℕ) (c : ℝ) : ℕ :=
  ⌊640 * a * p * c ^ 2⌋₊ + 1

noncomputable def portSaving (d b a p : ℕ) (c : ℝ) : ℝ :=
  (d * d * b : ℕ) / (4 * (portRunCap a p c : ℝ)) -
    3 * (portRunCap a p c : ℝ) * d * b - a

private theorem port_wall_count {P T a p : ℕ} {c : ℝ}
    (ha : 1 ≤ a) (hp : 1 ≤ p) (hc : 1 ≤ c) (hP : 0 < P)
    (hT : (T : ℝ) ≤ 2 * c * P) :
    (T - 1) / portSlabWidth P a p c + 1 ≤ portRunCap a p c := by
  apply Nat.add_le_add_right
  apply Nat.le_floor
  have hd : 0 < 320 * (a : ℝ) * p * c := by positivity
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hm : (((T - 1) / portSlabWidth P a p c : ℕ) : ℝ) *
      (portSlabWidth P a p c : ℝ) ≤ T := by
    exact_mod_cast (Nat.div_mul_le_self (T - 1) (portSlabWidth P a p c)).trans (Nat.sub_le T 1)
  have hw : (P : ℝ) / (320 * a * p * c) ≤ portSlabWidth P a p c := Nat.le_ceil _
  have hh := (mul_le_mul_of_nonneg_left hw
    (Nat.cast_nonneg ((T - 1) / portSlabWidth P a p c))).trans (hm.trans hT)
  apply (le_div_iff₀ (div_pos hPr hd)).mpr at hh
  convert hh using 1
  field_simp
  ring

private theorem port_snapshot_bound {P a p : ℕ} {c : ℝ}
    (ha : 1 ≤ a) (hp : 1 ≤ p) (hc : 1 ≤ c) :
    (a : ℝ) * portSlabWidth P a p c ≤ (P : ℝ) / (320 * p * c) + a := by
  have hd : 0 < 320 * (a : ℝ) * p * c := by positivity
  have hh := mul_le_mul_of_nonneg_left
    (Nat.ceil_lt_add_one (show 0 ≤ (P : ℝ) / (320 * a * p * c) by positivity)).le
    (Nat.cast_nonneg a)
  calc
    _ ≤ (a : ℝ) * ((P : ℝ) / (320 * a * p * c) + 1) := hh
    _ = _ := by field_simp

private theorem port_cap_comparison {P a p : ℕ} {c : ℝ}
    (ha : 1 ≤ a) (hp : 1 ≤ p) (hc : 1 ≤ c) :
    (P : ℝ) / (4 * (portRunCap a p c : ℝ)) ≤ (P : ℝ) / (320 * p * c) := by
  have hN : 640 * (a : ℝ) * p * c ^ 2 < portRunCap a p c := by
    simpa only [portRunCap, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (640 * (a : ℝ) * p * c ^ 2)
  have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hmul : (p : ℝ) * c ≤ a * p * c ^ 2 := by
    calc
      (p : ℝ) * c ≤ (p : ℝ) * c ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg p)
      _ ≤ (a : ℝ) * ((p : ℝ) * c ^ 2) := le_mul_of_one_le_left (by positivity) har
      _ = _ := by ring
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg P) (by positivity) (by nlinarith)

set_option maxHeartbeats 800000 in
/-- Construct the literal slab from its carrier walk and the actual ordered
append times, with every raw window in the omitted set paid by its interval. -/
theorem exists_port_slab_geometry {d b T a p R : ℕ} {c : ℝ}
    (hd : 1 ≤ d) (hb : 1 ≤ b) (ha : 1 ≤ a) (hp : 1 ≤ p)
    (hP : 4 * p ≤ d * d * b) (hc : 1 ≤ c)
    (hR : R ≤ (d * d * b) / (8 * p * portRunCap a p c))
    {xs : Fin p → ℕ → ℤ} (hx : ∀ j, IsWalk (xs j))
    {y : ℕ → ℤ} (hy : IsWalk y)
    {ot : Fin (d * d * b) → ℕ} (hot : StrictMono ot) (hotT : ∀ j, ot j < T)
    (hT : (T : ℝ) ≤ 2 * c * (d * d * b : ℕ)) :
    ∃ (ell : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ T ∧
      let C := selectedSlab y (portSlabWidth (d * d * b) a p c) ell s e
      C.card ≤ (d * d * b) / (4 * p) ∧
      (runStarts C).card ≤ portRunCap a p c ∧
      portSaving d b a p c ≤ ((omittedPortBits xs ot C T R).card : ℝ) -
        (a : ℝ) * (if s = 0 then 0 else (portSlabWidth (d * d * b) a p c : ℝ)) := by
  classical
  let P := d * d * b
  let W := portSlabWidth P a p c
  let N := portRunCap a p c
  let B := P / (4 * p)
  have hPpos : 0 < P := by dsimp [P]; nlinarith
  have hPr : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hW : 1 ≤ W := Nat.one_le_ceil_iff.mpr (by positivity)
  have hN : 0 < N := by dsimp [N, portRunCap]; omega
  have hB : 0 < B := Nat.div_pos hP (by omega)
  obtain ⟨u, _, hKdiv⟩ := exists_offset_slabTransitions_le hy hW T
  let K := slabTransitions y W T u
  let m := fun t => slabIdx W u (y t)
  have hKmem : ∀ t < T - 1, m t ≠ m (t + 1) → t ∈ K := fun t ht hne =>
    mem_filter.mpr ⟨mem_range.mpr ht, hne⟩
  have hKN : K.card + 1 ≤ N :=
    (Nat.add_le_add_right hKdiv 1).trans (port_wall_count ha hp hc hPpos hT)
  have hex : ∃ (ms : ℤ) (s e : ℕ), s ≤ e ∧ e ≤ T ∧
      ((Ico s e).filter fun t => m t = ms).card ≤ B ∧
      ((s = 0 ∧ P ≤ 2 * N * (outIn ot ((Ico s e).filter fun t => m t = ms)).card) ∨
        P * B < 4 * T * (outIn ot ((Ico s e).filter fun t => m t = ms)).card) := by
    rcases exists_slab_chunk_cap hPpos hB hKmem hotT with ⟨ms, hh, ho⟩ | ⟨ms, s, e, hse, he, hh, ho⟩
    · exact ⟨ms, 0, T, Nat.zero_le _, le_rfl, hh, Or.inl ⟨rfl,
        ho.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hKN))⟩⟩
    · exact ⟨ms, s, e, hse, he, hh, Or.inr ho⟩
  obtain ⟨ms, s, e, hse, heT, hcap, hcases⟩ := hex
  let C := (Ico s e).filter fun t => m t = ms
  have hCT : ∀ t ∈ C, t < T := fun t ht => (mem_Ico.mp (mem_filter.mp ht).1).2.trans_le heT
  have hruns : (runStarts C).card ≤ N := (card_runStarts_chunk_le heT hKmem).trans hKN
  have hcap' : 4 * p * C.card ≤ P :=
    (Nat.mul_le_mul_left (4 * p) hcap).trans (Nat.mul_div_le P (4 * p))
  have hradius : 8 * p * R * (runStarts C).card ≤ P := by
    have hh := (Nat.mul_le_mul_left (8 * p * N) hR).trans (Nat.mul_div_le P (8 * p * N))
    have hh' := Nat.mul_le_mul_left (8 * p * R) hruns
    nlinarith
  have hlen : 2 * (p * C.card + 2 * p * R * (runStarts C).card) ≤ P := by nlinarith
  have hstripe := port_discrepancy hd hb hx hot hCT hlen hcap'
  have hstripe' : ((outIn ot C).card : ℝ) ≤
      2 * ((omittedPortBits xs ot C T R).card : ℝ) + 6 * (N : ℝ) * d * b := by
    exact_mod_cast hstripe.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right b (Nat.mul_le_mul_right d (Nat.mul_le_mul_left 6 hruns))) _)
  have hCeq : selectedSlab y W ((u : ℤ) + ms * W) s e = C := by
    ext t
    simp only [selectedSlab, C, mem_filter]
    exact and_congr_right fun _ => (slab_index_iff hW (y t) ms).symm
  refine ⟨(u : ℤ) + ms * W, s, e, hse, heT, ?_⟩
  change (selectedSlab y W _ s e).card ≤ B ∧ _
  rw [hCeq]
  refine ⟨hcap, hruns, ?_⟩
  change (P : ℝ) / (4 * (N : ℝ)) - 3 * (N : ℝ) * d * b - a ≤ _
  rcases hcases with ⟨hs, hshort⟩ | hlong
  · have hshort' : (P : ℝ) ≤ 2 * (N : ℝ) * (outIn ot C).card := by exact_mod_cast hshort
    have hm : (P : ℝ) / (4 * (N : ℝ)) ≤
        (omittedPortBits xs ot C T R).card + 3 * (N : ℝ) * d * b := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (N : ℝ))).mpr
      nlinarith [mul_le_mul_of_nonneg_left hstripe' (show 0 ≤ (N : ℝ) by positivity)]
    simp only [hs, ite_true, mul_zero, sub_zero]
    linarith
  · have hPB : P ≤ 8 * p * B := by
      have hh := Nat.div_add_mod P (4 * p)
      have hmod := Nat.mod_lt P (show 0 < 4 * p by omega)
      dsimp only [B] at *
      nlinarith
    have hPB' : (P : ℝ) ≤ 8 * p * (B : ℝ) := by exact_mod_cast hPB
    have hl : (P : ℝ) * B < 4 * (T : ℝ) * (outIn ot C).card := by exact_mod_cast hlong
    have ht := mul_le_mul_of_nonneg_right hT (Nat.cast_nonneg (outIn ot C).card)
    have hout : (P : ℝ) / (64 * p * c) < (outIn ot C).card := by
      apply (div_lt_iff₀ (by positivity)).mpr
      have hpoly : (P : ℝ) * P < P * (64 * p * c * (outIn ot C).card) := by
        have hh := mul_le_mul_of_nonneg_left hPB' hPr.le
        have hh' := mul_lt_mul_of_pos_left hl (show (0 : ℝ) < 8 * p by positivity)
        nlinarith
      exact (mul_lt_mul_iff_right₀ hPr).mp (by nlinarith [hpoly])
    have hcost : (a : ℝ) * (if s = 0 then 0 else (W : ℝ)) ≤ (P : ℝ) / (320 * p * c) + a := by
      apply le_trans _ (port_snapshot_bound (P := P) ha hp hc)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg a)
      split_ifs <;> simp [W]
    have hcomp := port_cap_comparison (P := P) ha hp hc
    change (P : ℝ) / (4 * (N : ℝ)) ≤ (P : ℝ) / (320 * p * c) at hcomp
    have he : (P : ℝ) / (64 * p * c) = 5 * ((P : ℝ) / (320 * p * c)) := by field_simp; ring
    linarith

end AdaptiveTransfer.Getter
