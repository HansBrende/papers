import BoundedArityDecoders.ExtensionFieldTransfer
import LeanMachine.SequentialDimension

/-!
# Orbit Combinatorics and Proof of `Theorem 1A` (`Result 1`, Single-Shift Run-Extension)

This module proves:
* Exact cycle-decomposition lemmas for `c ↦ c + s` on `ZMod d` (`shiftOrbit`, `orbitElem`,
  `card_shiftOrbit`, `sum_orbitClassCard_eq`, `orbitClassCard_eq_orbitLen_of_runCount_zero`),
  reused by `Theorem 1B` in `ExtensionLinearRunProofs.lean`;
* Self-contained root-vanishing dimension bound `finrank_vanishCoeffs_le` on `Fin D → K`;
* `extension_Theorem1A_SingleShift : Extension_Theorem1A_SingleShiftSpec`;
* `linearClassUniform_singleShift_finrank_le` (unpacked top-level theorem).
-/

namespace BoundedArityDecoders

open Module
open scoped BigOperators

section OrbitCombinatorics

lemma shiftGcd_pos (d : ℕ) [NeZero d] (s : ZMod d) : 0 < shiftGcd d s :=
  Nat.gcd_pos_of_pos_left s.val (NeZero.pos d)

instance instNeZeroShiftGcd (d : ℕ) [NeZero d] (s : ZMod d) : NeZero (shiftGcd d s) :=
  ⟨Nat.ne_of_gt (shiftGcd_pos d s)⟩

lemma shiftGcd_dvd_dim (d : ℕ) (s : ZMod d) : shiftGcd d s ∣ d :=
  Nat.gcd_dvd_left d s.val

lemma shiftGcd_dvd_val (d : ℕ) (s : ZMod d) : shiftGcd d s ∣ s.val :=
  Nat.gcd_dvd_right d s.val

lemma shiftGcd_mul_orbitLen (d : ℕ) (s : ZMod d) :
    shiftGcd d s * shiftOrbitLen d s = d :=
  Nat.mul_div_cancel' (shiftGcd_dvd_dim d s)

lemma shiftOrbitLen_pos (d : ℕ) [NeZero d] (s : ZMod d) : 0 < shiftOrbitLen d s := by
  unfold shiftOrbitLen
  exact Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) (shiftGcd_dvd_dim d s)) (shiftGcd_pos d s)

instance instNeZeroShiftOrbitLen (d : ℕ) [NeZero d] (s : ZMod d) : NeZero (shiftOrbitLen d s) :=
  ⟨Nat.ne_of_gt (shiftOrbitLen_pos d s)⟩

/-- Explicit parametrization `(a, t) ↦ a + t * s` of the `a`-th `s`-orbit on `ZMod d`. -/
def orbitElem {d : ℕ} [NeZero d] (s : ZMod d) (a : Fin (shiftGcd d s))
    (t : Fin (shiftOrbitLen d s)) : ZMod d :=
  (a.val : ZMod d) + (t.val : ZMod d) * s

lemma orbitLen_nsmul_shift_eq_zero {d : ℕ} [NeZero d] (s : ZMod d) :
    ((shiftOrbitLen d s : ℕ) : ZMod d) * s = 0 := by
  have hcast : ((shiftOrbitLen d s * s.val : ℕ) : ZMod d) =
      ((shiftOrbitLen d s : ℕ) : ZMod d) * s := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.natCast_eq_zero_iff]
  have hd : shiftGcd d s * shiftOrbitLen d s = d := shiftGcd_mul_orbitLen d s
  obtain ⟨k, hk⟩ := shiftGcd_dvd_val d s
  refine ⟨k, ?_⟩
  calc shiftOrbitLen d s * s.val
      = shiftOrbitLen d s * (shiftGcd d s * k) := by rw [hk]
    _ = (shiftGcd d s * shiftOrbitLen d s) * k := by ring
    _ = d * k := by rw [hd]

lemma val_add_mod_shiftGcd {d : ℕ} [NeZero d] (s c : ZMod d) :
    (c + s).val % shiftGcd d s = c.val % shiftGcd d s := by
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (shiftGcd_dvd_dim d s)]
  obtain ⟨k, hk⟩ := shiftGcd_dvd_val d s
  rw [hk, Nat.add_mul_mod_self_left]

lemma mem_shiftOrbit_add_shift_iff {d : ℕ} [NeZero d] (s : ZMod d)
    (a : Fin (shiftGcd d s)) (c : ZMod d) :
    c + s ∈ shiftOrbit s a ↔ c ∈ shiftOrbit s a := by
  simp [shiftOrbit, val_add_mod_shiftGcd]

lemma orbitElem_mem_shiftOrbit {d : ℕ} [NeZero d] (s : ZMod d)
    (a : Fin (shiftGcd d s)) (t : Fin (shiftOrbitLen d s)) :
    orbitElem s a t ∈ shiftOrbit s a := by
  have hstep : ∀ k : ℕ,
      (((a.val : ZMod d) + (k : ZMod d) * s).val) % shiftGcd d s = a.val := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have ha_lt_d : a.val < d :=
        lt_of_lt_of_le a.isLt (Nat.le_of_dvd (NeZero.pos d) (shiftGcd_dvd_dim d s))
      rw [ZMod.val_natCast_of_lt ha_lt_d]
      exact Nat.mod_eq_of_lt a.isLt
    | succ k ih =>
      have hrew : (a.val : ZMod d) + ((k + 1 : ℕ) : ZMod d) * s =
          ((a.val : ZMod d) + (k : ZMod d) * s) + s := by
        push_cast
        ring
      rw [hrew, val_add_mod_shiftGcd]
      exact ih
  simp only [shiftOrbit, Finset.mem_filter, Finset.mem_univ, true_and, orbitElem]
  exact hstep t.val

lemma orbitParam_injective {d : ℕ} [NeZero d] (s : ZMod d) :
    Function.Injective (fun p : Fin (shiftGcd d s) × Fin (shiftOrbitLen d s) =>
      orbitElem s p.1 p.2) := by
  rintro ⟨a₁, t₁⟩ ⟨a₂, t₂⟩ heq
  dsimp only at heq
  have hm₁ := orbitElem_mem_shiftOrbit s a₁ t₁
  have hm₂ := orbitElem_mem_shiftOrbit s a₂ t₂
  simp only [shiftOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
  have ha_eq : a₁ = a₂ := Fin.ext (by rw [← hm₁, heq, hm₂])
  subst ha_eq
  simp only [orbitElem, add_right_inj] at heq
  have hdiff : ∀ {u v : ℕ}, u ≤ v → v < shiftOrbitLen d s →
      ((u : ZMod d) * s = (v : ZMod d) * s) → u = v := by
    intro u v huv hv hmul
    have hsub_zero : ((v - u : ℕ) : ZMod d) * s = 0 := by
      have hcast : ((v : ZMod d) - (u : ZMod d)) * s = 0 := by
        rw [sub_mul, hmul, sub_self]
      have hnat : ((v - u : ℕ) : ZMod d) = (v : ZMod d) - (u : ZMod d) := Nat.cast_sub huv
      rwa [hnat]
    have hs_cast : ((s.val : ℕ) : ZMod d) = s := ZMod.natCast_zmod_val s
    rw [← hs_cast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hsub_zero
    let g := shiftGcd d s
    have hg_pos : 0 < g := shiftGcd_pos d s
    have hcop : Nat.Coprime (d / g) (s.val / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    have hd_eq : g * (d / g) = d := Nat.mul_div_cancel' (shiftGcd_dvd_dim d s)
    have hs_eq : g * (s.val / g) = s.val := Nat.mul_div_cancel' (shiftGcd_dvd_val d s)
    have hdvd_mul : g * (d / g) ∣ g * ((v - u) * (s.val / g)) := by
      rw [hd_eq]
      have hrw : g * ((v - u) * (s.val / g)) = (v - u) * (g * (s.val / g)) := by ring
      rw [hrw, hs_eq]
      exact hsub_zero
    have hdvd_n : (d / g) ∣ (v - u) * (s.val / g) :=
      (Nat.mul_dvd_mul_iff_left hg_pos).mp hdvd_mul
    have hdvd_vu : (d / g) ∣ (v - u) := hcop.dvd_of_dvd_mul_right hdvd_n
    have hvu_lt : v - u < d / g := by
      change v - u < shiftOrbitLen d s
      omega
    have hvu_zero : v - u = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_vu hvu_lt
    omega
  have ht_eq : t₁.val = t₂.val := by
    rcases le_total t₁.val t₂.val with hle | hle
    · exact hdiff hle t₂.isLt heq
    · exact (hdiff hle t₁.isLt heq.symm).symm
  exact Prod.ext rfl (Fin.ext ht_eq)

/-- Bijection `(Fin g_s × Fin n_s) ≃ ZMod d` induced by `(a, t) ↦ a + t * s`. -/
noncomputable def orbitParamEquiv {d : ℕ} [NeZero d] (s : ZMod d) :
    (Fin (shiftGcd d s) × Fin (shiftOrbitLen d s)) ≃ ZMod d :=
  Equiv.ofBijective (fun p => orbitElem s p.1 p.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨orbitParam_injective s, by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ZMod.card,
          shiftGcd_mul_orbitLen]⟩)

lemma shiftOrbit_eq_image {d : ℕ} [NeZero d] (s : ZMod d) (a : Fin (shiftGcd d s)) :
    shiftOrbit s a = Finset.univ.image (orbitElem s a) := by
  ext c
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hc
    obtain ⟨⟨a', t⟩, rfl⟩ := (orbitParamEquiv s).surjective c
    change orbitElem s a' t ∈ shiftOrbit s a at hc
    have hm := orbitElem_mem_shiftOrbit s a' t
    simp only [shiftOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hc hm
    have ha : a' = a := Fin.ext (by rw [← hm, hc])
    subst ha
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact orbitElem_mem_shiftOrbit s a t

lemma orbitElem_injective {d : ℕ} [NeZero d] (s : ZMod d) (a : Fin (shiftGcd d s)) :
    Function.Injective (orbitElem s a) := by
  intro t₁ t₂ h
  have hinj := orbitParam_injective s (a₁ := (a, t₁)) (a₂ := (a, t₂)) h
  exact (Prod.mk.inj hinj).2

lemma card_shiftOrbit {d : ℕ} [NeZero d] (s : ZMod d) (a : Fin (shiftGcd d s)) :
    (shiftOrbit s a).card = shiftOrbitLen d s := by
  rw [shiftOrbit_eq_image, Finset.card_image_of_injective _ (orbitElem_injective s a)]
  simp

lemma orbitElem_succ_mod {d : ℕ} [NeZero d] (s : ZMod d)
    (a : Fin (shiftGcd d s)) (t : Fin (shiftOrbitLen d s)) :
    orbitElem s a ⟨(t.val + 1) % shiftOrbitLen d s,
      Nat.mod_lt _ (shiftOrbitLen_pos d s)⟩ = orbitElem s a t + s := by
  unfold orbitElem
  dsimp only
  by_cases hlt : t.val + 1 < shiftOrbitLen d s
  · rw [Nat.mod_eq_of_lt hlt]
    push_cast
    ring
  · have heq : t.val + 1 = shiftOrbitLen d s := by
      have := t.isLt
      omega
    have hmod : (t.val + 1) % shiftOrbitLen d s = 0 := by rw [heq, Nat.mod_self]
    rw [hmod]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hcast_t : ((t.val : ZMod d) + 1) = ((shiftOrbitLen d s : ℕ) : ZMod d) := by
      simpa [Nat.cast_add] using congrArg (Nat.cast (R := ZMod d)) heq
    have hns : ((t.val : ZMod d) * s) + s = ((shiftOrbitLen d s : ℕ) : ZMod d) * s := by
      calc (t.val : ZMod d) * s + s
          = ((t.val : ZMod d) + 1) * s := by ring
        _ = ((shiftOrbitLen d s : ℕ) : ZMod d) * s := by rw [hcast_t]
    rw [add_assoc, hns, orbitLen_nsmul_shift_eq_zero, add_zero]

lemma orbitRunCount_le_sub_orbitClassCard {d : ℕ} [NeZero d] {M : ℕ}
    (p : ZMod d → Fin M) (s : ZMod d) (a : Fin (shiftGcd d s)) (m : Fin M) :
    orbitRunCount p s m a ≤ shiftOrbitLen d s - orbitClassCard p s m a := by
  let R := (shiftOrbit s a).filter fun c => p c = m ∧ p (c + s) ≠ m
  let Comp := (shiftOrbit s a).filter fun c => p c ≠ m
  have hmap_sub : R.image (fun c => c + s) ⊆ Comp := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_filter, R, Comp] at hy ⊢
    obtain ⟨c, ⟨hc_orb, _, hne⟩, rfl⟩ := hy
    exact ⟨(mem_shiftOrbit_add_shift_iff s a c).mpr hc_orb, hne⟩
  have hinj : Set.InjOn (fun c : ZMod d => c + s) R := fun c₁ _ c₂ _ h => add_right_cancel h
  have hle : R.card ≤ Comp.card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hmap_sub
  have hsum : orbitClassCard p s m a + Comp.card = shiftOrbitLen d s := by
    unfold orbitClassCard
    rw [← card_shiftOrbit s a]
    exact Finset.card_filter_add_card_filter_not (fun c => p c = m)
  change R.card ≤ _
  omega

lemma orbitRunCount_le_orbitClassCard {d : ℕ} [NeZero d] {M : ℕ}
    (p : ZMod d → Fin M) (s : ZMod d) (a : Fin (shiftGcd d s)) (m : Fin M) :
    orbitRunCount p s m a ≤ orbitClassCard p s m a := by
  unfold orbitRunCount orbitClassCard
  exact Finset.card_le_card (fun c hc => by
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.1⟩)

lemma sum_orbitClassCard_eq {d : ℕ} [NeZero d] {M : ℕ}
    (p : ZMod d → Fin M) (s : ZMod d) (a : Fin (shiftGcd d s)) :
    ∑ m : Fin M, orbitClassCard p s m a = shiftOrbitLen d s := by
  rw [← card_shiftOrbit s a]
  unfold orbitClassCard
  rw [← Finset.card_biUnion]
  · congr 1
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨_, hc, _⟩; exact hc
    · intro hc; exact ⟨p c, hc, rfl⟩
  · intro m₁ _ m₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    simp only [Finset.mem_filter] at hc₁ hc₂
    exact hne (hc₁.2.symm.trans hc₂.2)

lemma orbitClassCard_le_orbitLen {d : ℕ} [NeZero d] {M : ℕ}
    (p : ZMod d → Fin M) (s : ZMod d) (a : Fin (shiftGcd d s)) (m : Fin M) :
    orbitClassCard p s m a ≤ shiftOrbitLen d s := by
  rw [← card_shiftOrbit s a]
  exact Finset.card_filter_le _ _

/-- If `J_m ∩ O_a` is nonempty and proper (`0 < d_{m,a} < n`), every `c ∈ J_m ∩ O_a` walks forward
under `+ s` to a run-endpoint `c + k * s ∈ J_m ∩ O_a` with `p (c + (k + 1) * s) ≠ m`. -/
lemma exists_forward_runEndpoint {d : ℕ} [NeZero d] {M : ℕ}
    (p : ZMod d → Fin M) (s : ZMod d) (a : Fin (shiftGcd d s)) (m : Fin M)
    (hlt : orbitClassCard p s m a < shiftOrbitLen d s)
    (c : ZMod d) (hc_orb : c ∈ shiftOrbit s a) (hc_cls : p c = m) :
    ∃ k : ℕ,
      (∀ j ≤ k, p (c + (j : ZMod d) * s) = m) ∧
      p (c + ((k + 1 : ℕ) : ZMod d) * s) ≠ m := by
  classical
  have hcomp_pos : 0 < ((shiftOrbit s a).filter fun x => p x ≠ m).card := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := shiftOrbit s a) (fun x => p x = m)
    rw [card_shiftOrbit] at hsum
    simp_rw [← ne_eq] at hsum
    change orbitClassCard p s m a + ((shiftOrbit s a).filter fun x => p x ≠ m).card = _ at hsum
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcomp_pos
  simp only [Finset.mem_filter] at hy
  rw [shiftOrbit_eq_image] at hc_orb
  have hy_orb := hy.1
  rw [shiftOrbit_eq_image] at hy_orb
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc_orb hy_orb
  obtain ⟨t₀, rfl⟩ := hc_orb
  obtain ⟨t₁, rfl⟩ := hy_orb
  let n := shiftOrbitLen d s
  let r : ℕ := (t₁.val + n - t₀.val) % n
  have hr_eq : orbitElem s a t₀ + (r : ZMod d) * s = orbitElem s a t₁ := by
    unfold orbitElem
    have hdiv : t₀.val + r = (t₀.val + r) % n + n * ((t₀.val + r) / n) :=
      (Nat.mod_add_div (t₀.val + r) n).symm
    have hmod_eq : (t₀.val + r) % n = t₁.val := by
      have ht₀ : t₀.val < n := t₀.isLt
      have ht₁ : t₁.val < n := t₁.isLt
      have hadd : t₀.val + (t₁.val + n - t₀.val) = t₁.val + n := by omega
      calc (t₀.val + r) % n
          = (t₀.val + (t₁.val + n - t₀.val)) % n := by
              dsimp [r]
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        _ = (t₁.val + n) % n := by rw [hadd]
        _ = t₁.val % n := Nat.add_mod_right t₁.val n
        _ = t₁.val := Nat.mod_eq_of_lt ht₁
    have hsum_s : ((t₀.val : ZMod d) + (r : ZMod d)) * s = (t₁.val : ZMod d) * s := by
      have hcast : ((t₀.val + r : ℕ) : ZMod d) * s =
          ((t₁.val : ZMod d) + ((n : ℕ) : ZMod d) * (((t₀.val + r) / n : ℕ) : ZMod d)) * s := by
        congr 1
        conv_lhs => rw [hdiv, hmod_eq]
        push_cast
        ring
      have hns : ((n : ℕ) : ZMod d) * s = 0 := orbitLen_nsmul_shift_eq_zero s
      calc ((t₀.val : ZMod d) + (r : ZMod d)) * s
          = ((t₀.val + r : ℕ) : ZMod d) * s := by push_cast; ring
        _ = (t₁.val : ZMod d) * s +
              (((t₀.val + r) / n : ℕ) : ZMod d) * (((n : ℕ) : ZMod d) * s) := by
            rw [hcast]; ring
        _ = (t₁.val : ZMod d) * s := by rw [hns, mul_zero, add_zero]
    calc (a.val : ZMod d) + (t₀.val : ZMod d) * s + (r : ZMod d) * s
        = (a.val : ZMod d) + ((t₀.val : ZMod d) + (r : ZMod d)) * s := by ring
      _ = (a.val : ZMod d) + (t₁.val : ZMod d) * s := by rw [hsum_s]
  have hex : ∃ u : ℕ, p (orbitElem s a t₀ + (u : ZMod d) * s) ≠ m :=
    ⟨r, by rw [hr_eq]; exact hy.2⟩
  let u₀ := Nat.find hex
  have hu₀_spec : p (orbitElem s a t₀ + (u₀ : ZMod d) * s) ≠ m := Nat.find_spec hex
  have hu₀_pos : 0 < u₀ := by
    by_contra h0
    have hz : u₀ = 0 := by omega
    rw [hz] at hu₀_spec
    simp only [Nat.cast_zero, zero_mul, add_zero] at hu₀_spec
    exact hu₀_spec hc_cls
  refine ⟨u₀ - 1, ?_, ?_⟩
  · intro j hj
    have hlt_u : j < u₀ := by omega
    by_contra hne
    exact Nat.find_min hex hlt_u hne
  · have hsucc : u₀ - 1 + 1 = u₀ := by omega
    rwa [hsucc]

lemma orbitClassCard_eq_orbitLen_of_runCount_zero {d : ℕ} [NeZero d] {M : ℕ}
    (p : ZMod d → Fin M) (s : ZMod d) (a : Fin (shiftGcd d s)) (m : Fin M)
    (hpos : 0 < orbitClassCard p s m a) (hzero : orbitRunCount p s m a = 0) :
    orbitClassCard p s m a = shiftOrbitLen d s := by
  by_contra hne
  have hlt : orbitClassCard p s m a < shiftOrbitLen d s :=
    lt_of_le_of_ne (orbitClassCard_le_orbitLen p s a m) hne
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter] at hc
  obtain ⟨k, hstay, hleave⟩ := exists_forward_runEndpoint p s a m hlt c hc.1 hc.2
  let e := c + (k : ZMod d) * s
  have he_orb : e ∈ shiftOrbit s a := by
    have hstep : ∀ j : ℕ, c + (j : ZMod d) * s ∈ shiftOrbit s a := by
      intro j
      induction j with
      | zero => simpa using hc.1
      | succ j ih =>
        have hrw : c + ((j + 1 : ℕ) : ZMod d) * s = (c + (j : ZMod d) * s) + s := by
          push_cast; ring
        rw [hrw]
        exact (mem_shiftOrbit_add_shift_iff s a _).mpr ih
    exact hstep k
  have he_mem : e ∈ (shiftOrbit s a).filter (fun x => p x = m ∧ p (x + s) ≠ m) := by
    simp only [Finset.mem_filter]
    refine ⟨he_orb, hstay k le_rfl, ?_⟩
    have hrw : e + s = c + ((k + 1 : ℕ) : ZMod d) * s := by
      dsimp [e]; push_cast; ring
    rwa [hrw]
  have hpos_run : 0 < orbitRunCount p s m a := Finset.card_pos.mpr ⟨e, he_mem⟩
  omega

end OrbitCombinatorics

section PolynomialVanishingBound

/-- Subspace of coefficient tuples `w : Fin D → K` whose polynomial `∑ i, w i * z^i` vanishes on
all `z ∈ S`. -/
def vanishCoeffs (K : Type*) [Field K] (D : ℕ) (S : Finset K) : Submodule K (Fin D → K) where
  carrier := {w | ∀ z ∈ S, ∑ i : Fin D, w i * z ^ i.val = 0}
  add_mem' {u v} hu hv z hz := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hu z hz, hv z hz, add_zero]
  zero_mem' _ _ := by simp
  smul_mem' a {u} hu z hz := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hu z hz, mul_zero]

private lemma sub_mul_geom_range {K : Type*} [CommRing K] (z z₀ : K) :
    ∀ m : ℕ, (z - z₀) * ∑ j ∈ Finset.range m, z₀ ^ (m - 1 - j) * z ^ j = z ^ m - z₀ ^ m
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel]
    have hsplit :
        ∑ x ∈ Finset.range m, z₀ ^ (m - x) * z ^ x =
          z₀ * ∑ x ∈ Finset.range m, z₀ ^ (m - 1 - x) * z ^ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hlt : x < m := Finset.mem_range.mp hx
      have hexp : m - x = (m - 1 - x) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [hsplit, Nat.sub_self, pow_zero, one_mul, mul_add]
    have hmul : (z - z₀) * (z₀ * ∑ x ∈ Finset.range m, z₀ ^ (m - 1 - x) * z ^ x) =
        z₀ * ((z - z₀) * ∑ x ∈ Finset.range m, z₀ ^ (m - 1 - x) * z ^ x) := by ring
    rw [hmul, sub_mul_geom_range z z₀ m]
    ring

private def polyQuotLinearMap (K : Type*) [Field K] (D : ℕ) (z₀ : K) :
    (Fin (D + 1) → K) →ₗ[K] (Fin D → K) where
  toFun w j := ∑ k : Fin (D + 1), if j.val < k.val then w k * z₀ ^ (k.val - 1 - j.val) else 0
  map_add' u v := by
    funext j
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  map_smul' a u := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring

private lemma polyQuotLinearMap_spec {K : Type*} [Field K] (D : ℕ) (z₀ z : K)
    (w : Fin (D + 1) → K) :
    (z - z₀) * ∑ j : Fin D, polyQuotLinearMap K D z₀ w j * z ^ j.val =
      (∑ k : Fin (D + 1), w k * z ^ k.val) - (∑ k : Fin (D + 1), w k * z₀ ^ k.val) := by
  simp only [polyQuotLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hinner :
      (∑ j : Fin D, (if j.val < k.val then w k * z₀ ^ (k.val - 1 - j.val) else 0) * z ^ j.val) =
        w k * ∑ j ∈ Finset.range k.val, z₀ ^ (k.val - 1 - j) * z ^ j := by
    have hk_le : k.val ≤ D := Nat.le_of_lt_succ k.isLt
    have hite : ∀ j : Fin D,
        (if j.val < k.val then w k * z₀ ^ (k.val - 1 - j.val) else 0) * z ^ j.val =
          if j.val < k.val then w k * (z₀ ^ (k.val - 1 - j.val) * z ^ j.val) else 0 := by
      intro j
      split_ifs <;> ring
    simp_rw [hite]
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_bij
      (fun (j : Fin D) _ => j.val)
      (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
      (fun j₁ _ j₂ _ h => Fin.ext h)
      (fun m hm =>
        let hlt := Finset.mem_range.mp hm
        ⟨⟨m, lt_of_lt_of_le hlt hk_le⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩)
      (fun _ _ => rfl)
  rw [hinner]
  calc (z - z₀) * (w k * ∑ j ∈ Finset.range k.val, z₀ ^ (k.val - 1 - j) * z ^ j)
      = w k * ((z - z₀) * ∑ j ∈ Finset.range k.val, z₀ ^ (k.val - 1 - j) * z ^ j) := by ring
    _ = w k * (z ^ k.val - z₀ ^ k.val) := by rw [sub_mul_geom_range]
    _ = w k * z ^ k.val - w k * z₀ ^ k.val := by ring

private lemma coeff_succ_eq_sub_polyQuot {K : Type*} [Field K] (D : ℕ) (z₀ : K)
    (w : Fin (D + 1) → K) (j : Fin D) :
    w j.succ =
      polyQuotLinearMap K D z₀ w j -
        if h : j.val + 1 < D then z₀ * polyQuotLinearMap K D z₀ w ⟨j.val + 1, h⟩ else 0 := by
  by_cases h : j.val + 1 < D
  · simp only [h, ↓reduceDIte, polyQuotLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single j.succ]
    · simp
    · intro k _ hk_ne
      by_cases hgt : j.val + 1 < k.val
      · have hgt1 : j.val < k.val := by omega
        have hexp : k.val - 1 - j.val = (k.val - 1 - (j.val + 1)) + 1 := by omega
        simp only [hgt1, hgt, ↓reduceIte, hexp, pow_succ]
        ring
      · have hnot1 : ¬ (j.val < k.val) := by
          intro hlt1
          have heq : k.val = j.val + 1 := by omega
          exact hk_ne (Fin.ext heq)
        simp [hgt, hnot1]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))
  · simp only [h, ↓reduceDIte, sub_zero, polyQuotLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    have hj_eq : j.val = D - 1 := by have := j.isLt; omega
    rw [Finset.sum_eq_single j.succ]
    · simp
    · intro k _ hk_ne
      have hk_le : k.val ≤ D := Nat.le_of_lt_succ k.isLt
      have hnot : ¬ (j.val < k.val) := by
        intro hlt1
        have heq : k.val = j.val + 1 := by omega
        exact hk_ne (Fin.ext heq)
      simp [hnot]
    · intro habs; exact False.elim (habs (Finset.mem_univ _))

/-- A polynomial in `K` of degree `< D` vanishing on `S : Finset K` lies in a subspace of
dimension at most `D - S.card`. -/
theorem finrank_vanishCoeffs_le (K : Type*) [Field K] :
    ∀ (D : ℕ) (S : Finset K), finrank K (vanishCoeffs K D S) ≤ D - S.card
  | 0, S => by
    have hle := Submodule.finrank_le (vanishCoeffs K 0 S)
    rw [Module.finrank_pi, Fintype.card_fin] at hle
    omega
  | D + 1, S => by
    classical
    rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
    · have hle := Submodule.finrank_le (vanishCoeffs K (D + 1) ∅)
      rw [Module.finrank_pi, Fintype.card_fin] at hle
      simpa using hle
    · let S' := S.erase z₀
      have hS_eq : insert z₀ S' = S := Finset.insert_erase hz₀
      have hz₀_not : z₀ ∉ S' := Finset.notMem_erase z₀ S
      have hcard : S.card = S'.card + 1 := by
        rw [← hS_eq, Finset.card_insert_of_notMem hz₀_not]
      let f : vanishCoeffs K (D + 1) S →ₗ[K] vanishCoeffs K D S' :=
        { toFun := fun w => ⟨polyQuotLinearMap K D z₀ w.1, by
            intro z hz
            have hz_S : z ∈ S := Finset.mem_of_mem_erase hz
            have hz_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hz)
            have hspec := polyQuotLinearMap_spec D z₀ z w.1
            rw [w.2 z hz_S, w.2 z₀ hz₀, sub_self] at hspec
            exact (mul_eq_zero.mp hspec).resolve_left hz_ne⟩
          map_add' := fun u v => Subtype.ext (map_add _ u.1 v.1)
          map_smul' := fun a u => Subtype.ext (map_smul _ a u.1) }
      have hinj : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro w hw
        have hq : polyQuotLinearMap K D z₀ w.1 = 0 := congrArg Subtype.val hw
        have hsucc_zero : ∀ j : Fin D, w.1 j.succ = 0 := by
          intro j
          rw [coeff_succ_eq_sub_polyQuot D z₀ w.1 j, hq]
          simp
        have h0_zero : w.1 0 = 0 := by
          have heval := w.2 z₀ hz₀
          rw [Fin.sum_univ_succ] at heval
          simp only [Fin.val_zero, pow_zero, mul_one, hsucc_zero, zero_mul,
            Finset.sum_const_zero, add_zero] at heval
          exact heval
        ext k
        refine Fin.cases h0_zero hsucc_zero k
      exact le_trans (LinearMap.finrank_le_finrank_of_injective hinj)
        (by
          have ih := finrank_vanishCoeffs_le K D S'
          omega)

end PolynomialVanishingBound

section FourierRunFiltration

/-- Stepwise degree-`D` parameter bound on a single `(orbit a, class m, column-orbit a')` block. -/
def stepRunBound (d_ma T_ma D : ℕ) : ℕ :=
  if d_ma = 0 then 0
  else if T_ma = 0 then 1
  else min T_ma (1 + (D - d_ma))

private lemma two_mul_sum_range_succ :
    ∀ T : ℕ, 2 * (∑ k ∈ Finset.range T, (k + 1)) = T * (T + 1)
  | 0 => by simp
  | T + 1 => by
    rw [Finset.sum_range_succ, mul_add, two_mul_sum_range_succ T]
    ring

private lemma two_mul_sum_stepRunBound_eq {n d_ma T_ma : ℕ}
    (hd_le : d_ma ≤ n) (hT_le_d : T_ma ≤ d_ma) (hT_le_sub : T_ma ≤ n - d_ma)
    (hmono : 0 < d_ma → T_ma = 0 → d_ma = n) :
    2 * (∑ D : Fin n, stepRunBound d_ma T_ma D.val) + T_ma ^ 2 =
      2 * d_ma + 2 * T_ma * (n - d_ma) + T_ma := by
  rw [Fin.sum_univ_eq_sum_range (fun D => stepRunBound d_ma T_ma D)]
  by_cases hd0 : d_ma = 0
  · have hT0 : T_ma = 0 := by omega
    subst hd0; subst hT0
    simp [stepRunBound]
  · by_cases hT0 : T_ma = 0
    · have hdn : d_ma = n := hmono (Nat.pos_of_ne_zero hd0) hT0
      subst hT0; subst hdn
      simp [stepRunBound, hd0]
    · have hT_pos : 0 < T_ma := Nat.pos_of_ne_zero hT0
      have hsimp_step : ∀ D, stepRunBound d_ma T_ma D = min T_ma (1 + (D - d_ma)) := by
        intro D
        simp [stepRunBound, hd0, hT0]
      simp_rw [hsimp_step]
      have hge : d_ma + T_ma ≤ n := by omega
      have hind : ∀ m ≥ d_ma + T_ma,
          2 * (∑ D ∈ Finset.range m, min T_ma (1 + (D - d_ma))) + T_ma ^ 2 =
            2 * d_ma + 2 * T_ma * (m - d_ma) + T_ma := by
        refine Nat.le_induction ?_ ?_
        · rw [Finset.sum_range_add]
          have hfirst : ∑ x ∈ Finset.range d_ma, min T_ma (1 + (x - d_ma)) = d_ma := by
            have hconst : ∀ x ∈ Finset.range d_ma, min T_ma (1 + (x - d_ma)) = 1 := by
              intro x hx
              have hlt : x < d_ma := Finset.mem_range.mp hx
              have hsub : x - d_ma = 0 := by omega
              rw [hsub]
              omega
            rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul,
              mul_one]
          have hsecond :
              ∑ x ∈ Finset.range T_ma, min T_ma (1 + (d_ma + x - d_ma)) =
                ∑ x ∈ Finset.range T_ma, (x + 1) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hlt : x < T_ma := Finset.mem_range.mp hx
            omega
          rw [hfirst, hsecond, mul_add, two_mul_sum_range_succ, Nat.add_sub_cancel_left]
          ring
        · intro m hm ih
          rw [Finset.sum_range_succ, mul_add]
          have hlast : min T_ma (1 + (m - d_ma)) = T_ma := by omega
          have hsub_succ : m + 1 - d_ma = (m - d_ma) + 1 := by omega
          rw [hlast, hsub_succ]
          linarith
      exact hind n hge

private lemma sum_stepRunBound_real_eq {n d_ma T_ma : ℕ}
    (hd_le : d_ma ≤ n) (hT_le_d : T_ma ≤ d_ma) (hT_le_sub : T_ma ≤ n - d_ma)
    (hmono : 0 < d_ma → T_ma = 0 → d_ma = n) :
    (∑ D : Fin n, (stepRunBound d_ma T_ma D.val : ℝ)) =
      (d_ma : ℝ) + ((T_ma : ℝ) * ((n : ℝ) - (d_ma : ℝ)) -
        (1 / 2 : ℝ) * (T_ma : ℝ) ^ 2 + (1 / 2 : ℝ) * (T_ma : ℝ)) := by
  have hnat := two_mul_sum_stepRunBound_eq hd_le hT_le_d hT_le_sub hmono
  have hreal : (2 * (∑ D : Fin n, stepRunBound d_ma T_ma D.val) + T_ma ^ 2 : ℝ) =
      ((2 * d_ma + 2 * T_ma * (n - d_ma) + T_ma : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast [Nat.cast_sub hd_le] at hreal
  linarith

private lemma sum_pow_mul_inv_pow {K : Type*} [Field K] {n : ℕ} [NeZero n]
    {ω : K} (hω : IsPrimitiveRoot ω n) (a b : Fin n) :
    ∑ r : Fin n, (ω ^ a.val * (ω ^ b.val)⁻¹) ^ r.val =
      if a = b then (n : K) else 0 := by
  have hω_ne : ω ≠ 0 := hω.ne_zero (NeZero.ne n)
  let ζ : K := ω ^ a.val * (ω ^ b.val)⁻¹
  by_cases hab : a = b
  · subst hab
    have hζ1 : ζ = 1 := mul_inv_cancel₀ (pow_ne_zero a.val hω_ne)
    simp [ζ, hζ1]
  · simp only [hab, ↓reduceIte]
    have hζ_ne1 : ζ ≠ 1 := by
      intro h1
      dsimp [ζ] at h1
      have heq_pow : ω ^ a.val = ω ^ b.val := by
        calc ω ^ a.val = (ω ^ a.val * (ω ^ b.val)⁻¹) * ω ^ b.val := by
              rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero b.val hω_ne), mul_one]
          _ = 1 * ω ^ b.val := by rw [h1]
          _ = ω ^ b.val := one_mul _
      have hinj := (hω.pow_inj a.isLt b.isLt) heq_pow
      exact hab (Fin.ext hinj)
    have hζ_pow : ζ ^ n = 1 := by
      dsimp [ζ]
      rw [mul_pow, inv_pow, pow_right_comm ω a.val n, pow_right_comm ω b.val n,
        hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
    have hmul_zero : (∑ r : Fin n, ζ ^ r.val) * (ζ - 1) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun r => ζ ^ r), geom_sum_mul, hζ_pow, sub_self]
    exact (mul_eq_zero.mp hmul_zero).resolve_right (sub_ne_zero.mpr hζ_ne1)

/-- Mode-lift map reconstructing the `η`-th `laneRot s`-eigenspace from orbit representatives
`ZMod d → Fin g_s → Fin b → K`. -/
noncomputable def modeLift {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    (ω : K) (s : ZMod d) (η : Fin (shiftOrbitLen d s)) :
    (ZMod d → Fin (shiftGcd d s) → Fin b → K) →ₗ[K] Matrix (ZMod d) (ZMod d) (Fin b → K) where
  toFun f := Matrix.of fun i j =>
    let pq := (orbitParamEquiv s).symm j
    (ω ^ (pq.2.val * η.val)) • f i pq.1
  map_add' f₁ f₂ := by
    ext i j u
    simp [smul_add]
  map_smul' c f := by
    ext i j u
    simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Matrix.smul_apply]
    ring

private lemma modeLift_orbitElem {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    (ω : K) (s : ZMod d) (η : Fin (shiftOrbitLen d s))
    (f : ZMod d → Fin (shiftGcd d s) → Fin b → K)
    (i : ZMod d) (a' : Fin (shiftGcd d s)) (q : Fin (shiftOrbitLen d s)) :
    modeLift ω s η f i (orbitElem s a' q) = (ω ^ (q.val * η.val)) • f i a' := by
  change (let pq := (orbitParamEquiv s).symm ((orbitParamEquiv s) (a', q));
    (ω ^ (pq.2.val * η.val)) • f i pq.1) = _
  rw [(orbitParamEquiv s).symm_apply_apply]

private lemma pow_mod_orbitLen_mul {K : Type*} [CommMonoid K] {n : ℕ}
    {ω : K} (hωn : ω ^ n = 1) (m k : ℕ) :
    ω ^ ((m % n) * k) = ω ^ (m * k) := by
  have hdiv : m = m % n + n * (m / n) := (Nat.mod_add_div m n).symm
  conv_rhs => rw [hdiv]
  rw [add_mul, pow_add]
  have h1 : ω ^ (n * (m / n) * k) = 1 := by
    have hrw : n * (m / n) * k = n * ((m / n) * k) := by ring
    rw [hrw, pow_mul, hωn, one_pow]
  rw [h1, mul_one]

private lemma laneRot_s_modeLift {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    {ω : K} {s : ZMod d} (hω : IsPrimitiveRoot ω (shiftOrbitLen d s))
    (η : Fin (shiftOrbitLen d s))
    (f : ZMod d → Fin (shiftGcd d s) → Fin b → K) :
    laneRot s (modeLift ω s η f) = (ω ^ η.val) • modeLift ω s η f := by
  ext i j u
  obtain ⟨⟨a', q⟩, rfl⟩ := (orbitParamEquiv s).surjective j
  change modeLift ω s η f i (orbitElem s a' q + s) u =
    ((ω ^ η.val) • modeLift ω s η f) i (orbitElem s a' q) u
  rw [← orbitElem_succ_mod s a' q, modeLift_orbitElem]
  simp only [Matrix.smul_apply, modeLift_orbitElem, Pi.smul_apply, smul_eq_mul]
  rw [pow_mod_orbitLen_mul hω.pow_eq_one (q.val + 1) η.val]
  have hexp : (q.val + 1) * η.val = η.val + q.val * η.val := by ring
  rw [hexp, pow_add, mul_assoc]

private lemma laneRot_orbitElem_modeLift {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    {ω : K} {s : ZMod d} (hω : IsPrimitiveRoot ω (shiftOrbitLen d s))
    (η : Fin (shiftOrbitLen d s))
    (f : ZMod d → Fin (shiftGcd d s) → Fin b → K)
    (a : Fin (shiftGcd d s)) (t : Fin (shiftOrbitLen d s)) :
    laneRot (orbitElem s a t) (modeLift ω s η f) =
      (ω ^ (t.val * η.val)) • laneRot (a.val : ZMod d) (modeLift ω s η f) := by
  have hiter : ∀ k : ℕ,
      laneRot ((a.val : ZMod d) + (k : ZMod d) * s) (modeLift ω s η f) =
        (ω ^ (k * η.val)) • laneRot (a.val : ZMod d) (modeLift ω s η f) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hadd : ∀ x y : ZMod d, ∀ M : Matrix (ZMod d) (ZMod d) (Fin b → K),
          laneRot (x + y) M = laneRot x (laneRot y M) := by
        intro x y M; ext i j u; simp only [laneRot_apply]
        exact congrArg (fun z => M i z u) (by ring)
      have hrw : (a.val : ZMod d) + ((k + 1 : ℕ) : ZMod d) * s =
          ((a.val : ZMod d) + (k : ZMod d) * s) + s := by push_cast; ring
      rw [hrw, hadd, laneRot_s_modeLift hω, map_smul, ih, smul_smul]
      have hexp : (k + 1) * η.val = η.val + k * η.val := by ring
      rw [hexp, pow_add]
  exact hiter t.val

/-- Inverse Fourier coefficient extraction along column `s`-orbits. -/
noncomputable def fourierCoeffs {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    (ω : K) (s : ZMod d) :
    Matrix (ZMod d) (ZMod d) (Fin b → K) →ₗ[K]
      (Fin (shiftOrbitLen d s) → ZMod d → Fin (shiftGcd d s) → Fin b → K) where
  toFun X μ c a' :=
    ((shiftOrbitLen d s : K)⁻¹) •
      ∑ q : Fin (shiftOrbitLen d s),
        ((ω ^ μ.val)⁻¹ ^ q.val) • X c (orbitElem s a' q)
  map_add' X Y := by
    funext μ c a' u
    simp only [Pi.add_apply, Matrix.add_apply, smul_add, Finset.sum_add_distrib, Finset.sum_apply,
      Pi.smul_apply]
  map_smul' r X := by
    funext μ c a' u
    simp only [Pi.smul_apply, Matrix.smul_apply, Finset.sum_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring

private lemma fourierCoeffs_modeLift {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    {ω : K} {s : ZMod d} (hω : IsPrimitiveRoot ω (shiftOrbitLen d s))
    (hnK : ((shiftOrbitLen d s : ℕ) : K) ≠ 0)
    (η μ : Fin (shiftOrbitLen d s))
    (f : ZMod d → Fin (shiftGcd d s) → Fin b → K) :
    fourierCoeffs ω s (modeLift ω s η f) μ = if η = μ then f else 0 := by
  funext c a' u
  simp only [fourierCoeffs, LinearMap.coe_mk, AddHom.coe_mk, modeLift_orbitElem,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  have hterm : ∀ q : Fin (shiftOrbitLen d s),
      ((ω ^ μ.val)⁻¹ ^ q.val) * (ω ^ (q.val * η.val) * f c a' u) =
        ((ω ^ η.val * (ω ^ μ.val)⁻¹) ^ q.val) * f c a' u := by
    intro q
    rw [mul_pow, pow_right_comm ω η.val q.val]
    ring
  simp_rw [hterm, ← Finset.sum_mul, sum_pow_mul_inv_pow hω η μ]
  by_cases h : η = μ
  · subst h
    simp [inv_mul_cancel_left₀ hnK]
  · simp [h]

private lemma matrix_sum_apply_lane {K : Type*} [AddCommMonoid K] {d b : ℕ} {ι : Type*}
    (S : Finset ι) (G : ι → Matrix (ZMod d) (ZMod d) (Fin b → K))
    (i j : ZMod d) (u : Fin b) :
    (∑ η ∈ S, G η) i j u = ∑ η ∈ S, G η i j u := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_apply, Pi.add_apply, ih]

private lemma sum_modeLift_fourierCoeffs {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    {ω : K} {s : ZMod d} (hω : IsPrimitiveRoot ω (shiftOrbitLen d s))
    (hnK : ((shiftOrbitLen d s : ℕ) : K) ≠ 0)
    (X : Matrix (ZMod d) (ZMod d) (Fin b → K)) :
    ∑ η : Fin (shiftOrbitLen d s), modeLift ω s η (fourierCoeffs ω s X η) = X := by
  ext i j u
  obtain ⟨⟨a', q₀⟩, rfl⟩ := (orbitParamEquiv s).surjective j
  change (∑ η : Fin (shiftOrbitLen d s),
    modeLift ω s η (fourierCoeffs ω s X η)) i (orbitElem s a' q₀) u =
    X i (orbitElem s a' q₀) u
  rw [matrix_sum_apply_lane]
  simp only [modeLift_orbitElem, fourierCoeffs, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  have hswap :
      (∑ η : Fin (shiftOrbitLen d s), ∑ q : Fin (shiftOrbitLen d s),
        ω ^ (q₀.val * η.val) * ((shiftOrbitLen d s : K)⁻¹ *
          ((((ω ^ η.val)⁻¹) ^ q.val) * X i (orbitElem s a' q) u))) =
      (shiftOrbitLen d s : K)⁻¹ * ∑ q : Fin (shiftOrbitLen d s),
        (∑ η : Fin (shiftOrbitLen d s), (ω ^ q₀.val * (ω ^ q.val)⁻¹) ^ η.val) *
          X i (orbitElem s a' q) u := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    have hpow_inv : ((ω ^ η.val)⁻¹) ^ q.val = ((ω ^ q.val)⁻¹) ^ η.val := by
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow_inv, mul_pow, ← pow_mul, Nat.mul_comm q₀.val η.val]
    ring
  rw [hswap]
  simp_rw [sum_pow_mul_inv_pow hω q₀]
  simp [inv_mul_cancel_left₀ hnK]

private lemma fourierCoeffs_injective {K : Type*} [Field K] {d b : ℕ} [NeZero d]
    {ω : K} {s : ZMod d} (hω : IsPrimitiveRoot ω (shiftOrbitLen d s))
    (hnK : ((shiftOrbitLen d s : ℕ) : K) ≠ 0) :
    Function.Injective (fourierCoeffs ω s (b := b)) := by
  intro X Y hXY
  rw [← sum_modeLift_fourierCoeffs hω hnK X, ← sum_modeLift_fourierCoeffs hω hnK Y, hXY]

private def matFlatEquiv (R : Type*) [Semiring R] (d b : ℕ) :
    Matrix (ZMod d) (ZMod d) (Fin b → R) ≃ₗ[R] ((ZMod d × ZMod d × Fin b) → R) where
  toFun X idx := X idx.1 idx.2.1 idx.2.2
  invFun f := Matrix.of fun i j u => f (i, j, u)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rowFlatEquiv (R : Type*) [Semiring R] (d b : ℕ) :
    (ZMod d → Fin b → R) ≃ₗ[R] ((ZMod d × Fin b) → R) where
  toFun r idx := r idx.1 idx.2
  invFun f j u := f (j, u)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Proof of `Extension_Theorem1A_SingleShiftSpec`. -/
theorem extension_Theorem1A_SingleShift : Extension_Theorem1A_SingleShiftSpec := by
  intro F _ d M b _ _ _ p s
  refine ⟨fun a m => orbitRunCount_le_sub_orbitClassCard p s a m, ?_⟩
  intro hchar 𝒳 hLin
  classical
  let g := shiftGcd d s
  let n := shiftOrbitLen d s
  let K := AlgebraicClosure F
  let φ : F →+* K := algebraMap F K
  obtain ⟨ω, hω⟩ := exists_isPrimitiveRoot_algebraicClosure F n hchar
  have hnF : ((n : ℕ) : F) ≠ 0 := (coprimeToChar_iff_natCast_ne_zero F n).mp hchar
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    intro hz
    exact hnF (φ.injective (by simpa using hz))
  obtain ⟨dec, hdec⟩ := hLin
  let matEquivF := matFlatEquiv F d b
  let matEquivK := matFlatEquiv K d b
  let rowEquivF := rowFlatEquiv F d b
  let rowEquivK := rowFlatEquiv K d b
  let decK : Fin M → (Matrix (ZMod d) (ZMod d) (Fin b → K) →ₗ[K] (ZMod d → Fin b → K)) :=
    fun m =>
      rowEquivK.symm.toLinearMap ∘ₗ
        extendLinearMapPi φ
          (rowEquivF.toLinearMap ∘ₗ dec m ∘ₗ matEquivF.symm.toLinearMap) ∘ₗ
        matEquivK.toLinearMap
  let WK : Submodule K (Matrix (ZMod d) (ZMod d) (Fin b → K)) :=
    { carrier := {X |
        (∀ c : ZMod d, X c = decK (p c) (laneRot c X)) ∧
        (∀ c : ZMod d, (laneRot s X) c = decK (p c) (laneRot c (laneRot s X)))}
      add_mem' := fun {X Y} hX hY =>
        ⟨fun c => by
          funext j u
          have hx := congrFun (congrFun (hX.1 c) j) u
          have hy := congrFun (congrFun (hY.1 c) j) u
          simp only [Matrix.add_apply, map_add, Pi.add_apply] at hx hy ⊢
          exact congrArg₂ (· + ·) hx hy,
         fun c => by
          funext j u
          have hx := congrFun (congrFun (hX.2 c) j) u
          have hy := congrFun (congrFun (hY.2 c) j) u
          simp only [Matrix.add_apply, map_add, Pi.add_apply] at hx hy ⊢
          exact congrArg₂ (· + ·) hx hy⟩
      zero_mem' := ⟨fun _ => by funext j u; simp, fun _ => by funext j u; simp⟩
      smul_mem' := fun a {X} hX =>
        ⟨fun c => by
          funext j u
          have hx := congrFun (congrFun (hX.1 c) j) u
          simp only [Matrix.smul_apply, map_smul, Pi.smul_apply] at hx ⊢
          exact congrArg (a • ·) hx,
         fun c => by
          funext j u
          have hx := congrFun (congrFun (hX.2 c) j) u
          simp only [Matrix.smul_apply, map_smul, Pi.smul_apply] at hx ⊢
          exact congrArg (a • ·) hx⟩ }
  -- Step 1: Base change bound finrank F (𝒳 ⊓ 𝒳.comap (laneRot s)) ≤ finrank K WK
  have hbase_le : finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) ≤ finrank K WK := by
    let UF := (𝒳 ⊓ 𝒳.comap (laneRot s)).map matEquivF.toLinearMap
    let UK := WK.map matEquivK.toLinearMap
    rw [← LinearEquiv.finrank_map_eq matEquivF (𝒳 ⊓ 𝒳.comap (laneRot s)),
        ← LinearEquiv.finrank_map_eq matEquivK WK]
    refine finrank_le_of_pi_ringHom φ UF UK ?_
    rintro _ ⟨X, ⟨hX0, hXs⟩, rfl⟩
    let XK : Matrix (ZMod d) (ZMod d) (Fin b → K) := Matrix.of fun i j u => φ (X i j u)
    refine ⟨XK, ⟨?_, ?_⟩, rfl⟩
    · intro c
      have hcomp := extendLinearMapPi_comp_map φ
        (rowEquivF.toLinearMap ∘ₗ dec (p c) ∘ₗ matEquivF.symm.toLinearMap)
        (matEquivF (laneRot c X))
      have hrot_map : matEquivK (laneRot c XK) = fun idx => φ (matEquivF (laneRot c X) idx) :=
        rfl
      funext j u
      have hXc := congrFun (congrFun (hdec X hX0 c) j) u
      dsimp [decK]
      rw [hrot_map, hcomp]
      simpa [XK, matEquivF, matEquivK, rowEquivF, rowEquivK, matFlatEquiv, rowFlatEquiv] using
        congrArg φ hXc
    · intro c
      have hcomp := extendLinearMapPi_comp_map φ
        (rowEquivF.toLinearMap ∘ₗ dec (p c) ∘ₗ matEquivF.symm.toLinearMap)
        (matEquivF (laneRot c (laneRot s X)))
      have hrot_map : matEquivK (laneRot c (laneRot s XK)) =
          fun idx => φ (matEquivF (laneRot c (laneRot s X)) idx) := rfl
      funext j u
      have hXc := congrFun (congrFun (hdec (laneRot s X) hXs c) j) u
      dsimp [decK]
      rw [hrot_map, hcomp]
      simpa [XK, matEquivF, matEquivK, rowEquivF, rowEquivK, matFlatEquiv, rowFlatEquiv] using
        congrArg φ hXc
  -- Step 2: Push WK injectively into Fourier coordinates C ≤ (Fin n → A)
  let A := ZMod d → Fin g → Fin b → K
  let C : Submodule K (Fin n → A) := WK.map (fourierCoeffs ω s)
  have hWK_eq_C : finrank K WK = finrank K C := by
    refine le_antisymm ?_ (Submodule.finrank_map_le (fourierCoeffs ω s) WK)
    let fWK : WK →ₗ[K] C :=
      { toFun := fun x => ⟨fourierCoeffs ω s x.1, Submodule.mem_map_of_mem x.2⟩
        map_add' := fun x y => Subtype.ext (map_add (fourierCoeffs ω s) x.1 y.1)
        map_smul' := fun r x => Subtype.ext (map_smul (fourierCoeffs ω s) r x.1) }
    have hfWK_inj : Function.Injective fWK := fun x y h =>
      Subtype.ext (fourierCoeffs_injective hω hnK (Subtype.ext_iff.mp h))
    exact LinearMap.finrank_le_finrank_of_injective hfWK_inj
  -- Step 3: Define block subspaces S_{D, a, m} ≤ ({c ∈ O_a | p c = m} → Fin b → K)
  let BlockIdx (a : Fin g) (m : Fin M) :=
    {c : ZMod d // c ∈ (shiftOrbit s a).filter (fun x => p x = m)}
  let BlockSpace (a : Fin g) (m : Fin M) (D : Fin n) :
      Submodule K (BlockIdx a m → Fin b → K) :=
    let rootsFinset : Finset K :=
      ((Finset.univ : Finset (Fin n)).filter (fun t => p (orbitElem s a t) = m)).image
        (fun t => ω ^ t.val)
    let PolyCoeffSub : Submodule K (Fin (D.val + 1) → Fin b → K) :=
      { carrier := {v | ∀ u : Fin b,
          (fun j : Fin D.val => (ω ^ j.val - ω ^ D.val) * v j.castSucc u) ∈
            vanishCoeffs K D.val rootsFinset}
        add_mem' := fun {v₁ v₂} h₁ h₂ u => by
          have hsum := (vanishCoeffs K D.val rootsFinset).add_mem (h₁ u) (h₂ u)
          convert hsum using 1
          funext j
          simp only [Pi.add_apply, mul_add]
        zero_mem' := fun u => by
          convert (vanishCoeffs K D.val rootsFinset).zero_mem using 1
          funext j
          simp
        smul_mem' := fun r {v} hv u => by
          have hsm := (vanishCoeffs K D.val rootsFinset).smul_mem r (hv u)
          convert hsm using 1
          funext j
          simp only [Pi.smul_apply, smul_eq_mul]
          ring }
    let evalMap : (Fin (D.val + 1) → Fin b → K) →ₗ[K] (BlockIdx a m → Fin b → K) :=
      { toFun := fun v c =>
          let t := ((orbitParamEquiv s).symm c.1).2
          ∑ η : Fin (D.val + 1), (ω ^ (t.val * η.val)) • v η
        map_add' := fun v₁ v₂ => by
          funext c u
          simp [smul_add, Finset.sum_add_distrib]
        map_smul' := fun r v => by
          funext c u
          simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun η _ => by ring }
    let RunStepSub : Submodule K (BlockIdx a m → Fin b → K) :=
      { carrier := {h | ∀ (c : BlockIdx a m)
          (hcs : c.1 + s ∈ (shiftOrbit s a).filter (fun x => p x = m)),
          h ⟨c.1 + s, hcs⟩ = (ω ^ D.val) • h c}
        add_mem' := fun {h₁ h₂} hh₁ hh₂ c hcs => by
          simp [hh₁ c hcs, hh₂ c hcs, smul_add]
        zero_mem' := fun _ _ => by simp
        smul_mem' := fun r {h} hh c hcs => by
          funext u
          have hc := congrFun (hh c hcs) u
          simp only [Pi.smul_apply, smul_eq_mul] at hc ⊢
          rw [hc]
          ring }
    PolyCoeffSub.map evalMap ⊓ RunStepSub
  -- Bound finrank K (BlockSpace a m D) ≤ b * stepRunBound d_{m,a} T_{m,a} D.val
  have hBlock_finrank : ∀ (a : Fin g) (m : Fin M) (D : Fin n),
      finrank K (BlockSpace a m D) ≤
        b * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) D.val := by
    intro a m D
    let d_ma := orbitClassCard p s m a
    let T_ma := orbitRunCount p s m a
    change finrank K (BlockSpace a m D) ≤ b * stepRunBound d_ma T_ma D.val
    by_cases hd0 : d_ma = 0
    · have hempty : IsEmpty (BlockIdx a m) := by
        refine ⟨fun c => ?_⟩
        have hpos : 0 < d_ma := Finset.card_pos.mpr ⟨c.1, c.2⟩
        omega
      have hle := Submodule.finrank_le (BlockSpace a m D)
      rw [Module.finrank_pi_fintype, Finset.sum_eq_zero (fun c _ => False.elim (hempty.false c))]
        at hle
      simp [stepRunBound, hd0] at hle ⊢
      omega
    · -- First bound: finrank K (PolyCoeffSub.map evalMap) ≤ b * (1 + (D.val - d_ma))
      let rootsFinset : Finset K :=
        ((Finset.univ : Finset (Fin n)).filter (fun t => p (orbitElem s a t) = m)).image
          (fun t => ω ^ t.val)
      have hroots_card : rootsFinset.card = d_ma := by
        dsimp [rootsFinset, d_ma]
        rw [Finset.card_image_of_injective _ (fun t₁ t₂ h =>
          Fin.ext (hω.pow_inj t₁.isLt t₂.isLt h))]
        unfold orbitClassCard
        rw [shiftOrbit_eq_image, Finset.filter_image,
          Finset.card_image_of_injective _ (orbitElem_injective s a)]
      have hpoly_le : finrank K (BlockSpace a m D) ≤ b * (1 + (D.val - d_ma)) := by
        let PolyCoeffSub : Submodule K (Fin (D.val + 1) → Fin b → K) :=
          { carrier := {v | ∀ u : Fin b,
              (fun j : Fin D.val => (ω ^ j.val - ω ^ D.val) * v j.castSucc u) ∈
                vanishCoeffs K D.val rootsFinset}
            add_mem' := fun {v₁ v₂} h₁ h₂ u => by
              have hsum := (vanishCoeffs K D.val rootsFinset).add_mem (h₁ u) (h₂ u)
              convert hsum using 1
              funext j
              simp only [Pi.add_apply, mul_add]
            zero_mem' := fun u => by
              convert (vanishCoeffs K D.val rootsFinset).zero_mem using 1
              funext j
              simp
            smul_mem' := fun r {v} hv u => by
              have hsm := (vanishCoeffs K D.val rootsFinset).smul_mem r (hv u)
              convert hsm using 1
              funext j
              simp only [Pi.smul_apply, smul_eq_mul]
              ring }
        have hstep1 : finrank K (BlockSpace a m D) ≤ finrank K PolyCoeffSub := by
          dsimp only [BlockSpace]
          exact (Submodule.finrank_mono inf_le_left).trans (Submodule.finrank_map_le _ _)
        refine le_trans hstep1 ?_
        -- Inject PolyCoeffSub into (Fin b → vanishCoeffs K D.val rootsFinset) × (Fin b → K)
        let diagInj : PolyCoeffSub →ₗ[K]
            ((Fin b → vanishCoeffs K D.val rootsFinset) × (Fin b → K)) :=
          { toFun := fun v =>
              (fun u => ⟨fun j => (ω ^ j.val - ω ^ D.val) * v.1 j.castSucc u, v.2 u⟩,
               fun u => v.1 (Fin.last D.val) u)
            map_add' := fun v₁ v₂ => by
              ext u j
              · simp [mul_add]
              · simp
            map_smul' := fun r v => by
              ext u j
              · simp only [Prod.smul_fst, Pi.smul_apply, Submodule.coe_smul_of_tower,
                  smul_eq_mul, RingHom.id_apply]
                ring
              · simp }
        have hdiag_inj : Function.Injective diagInj := by
          rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
          intro v hv
          have hv1 := congrArg Prod.fst hv
          have hv2 := congrArg Prod.snd hv
          ext η u
          refine Fin.lastCases ?_ ?_ η
          · exact congrFun hv2 u
          · intro j
            have hj := congrFun (congrArg Subtype.val (congrFun hv1 u)) j
            change (ω ^ j.val - ω ^ D.val) * v.1 j.castSucc u = 0 at hj
            have hdiff_ne : ω ^ j.val - ω ^ D.val ≠ 0 := by
              intro hsub
              have heq := sub_eq_zero.mp hsub
              have hj_lt : j.val < n := lt_trans j.isLt D.isLt
              have heq_val := hω.pow_inj hj_lt D.isLt heq
              exact absurd heq_val (Nat.ne_of_lt j.isLt)
            exact (mul_eq_zero.mp hj).resolve_left hdiff_ne
        refine le_trans (LinearMap.finrank_le_finrank_of_injective hdiag_inj) ?_
        rw [Module.finrank_prod]
        have hv_le := finrank_vanishCoeffs_le K D.val rootsFinset
        rw [hroots_card] at hv_le
        have hmul_le : b * finrank K (vanishCoeffs K D.val rootsFinset) ≤
            b * (D.val - d_ma) := Nat.mul_le_mul_left b hv_le
        calc finrank K (Fin b → vanishCoeffs K D.val rootsFinset) + finrank K (Fin b → K)
            = b * finrank K (vanishCoeffs K D.val rootsFinset) + b := by
                rw [Module.finrank_pi_fintype, Module.finrank_pi]
                simp [Finset.sum_const]
          _ ≤ b * (D.val - d_ma) + b := Nat.add_le_add_right hmul_le b
          _ = b * (1 + (D.val - d_ma)) := by ring
      by_cases hT0 : T_ma = 0
      · have hdn : d_ma = n :=
          orbitClassCard_eq_orbitLen_of_runCount_zero p s a m (Nat.pos_of_ne_zero hd0) hT0
        have hsub0 : D.val - d_ma = 0 := by
          have := D.isLt
          omega
        simp only [stepRunBound, hd0, hT0, ↓reduceIte]
        rw [hsub0, add_zero] at hpoly_le
        exact hpoly_le
      · -- Also bound finrank K (BlockSpace a m D) ≤ b * T_ma via restriction to run-endpoints
        have hrun_le : finrank K (BlockSpace a m D) ≤ b * T_ma := by
          let RunStepSub : Submodule K (BlockIdx a m → Fin b → K) :=
            { carrier := {h | ∀ (c : BlockIdx a m)
                (hcs : c.1 + s ∈ (shiftOrbit s a).filter (fun x => p x = m)),
                h ⟨c.1 + s, hcs⟩ = (ω ^ D.val) • h c}
              add_mem' := fun {h₁ h₂} hh₁ hh₂ c hcs => by
                simp [hh₁ c hcs, hh₂ c hcs, smul_add]
              zero_mem' := fun _ _ => by simp
              smul_mem' := fun r {h} hh c hcs => by
                funext u
                have hc := congrFun (hh c hcs) u
                simp only [Pi.smul_apply, smul_eq_mul] at hc ⊢
                rw [hc]
                ring }
          have hstep2 : finrank K (BlockSpace a m D) ≤ finrank K RunStepSub := by
            dsimp only [BlockSpace]
            exact Submodule.finrank_mono inf_le_right
          refine le_trans hstep2 ?_
          let EndIdx :=
            {e : ZMod d // e ∈ (shiftOrbit s a).filter (fun x => p x = m ∧ p (x + s) ≠ m)}
          let resEnd : RunStepSub →ₗ[K] (EndIdx → Fin b → K) :=
            { toFun := fun h e => h.1 ⟨e.1, by
                have he := e.2
                simp only [Finset.mem_filter] at he ⊢
                exact ⟨he.1, he.2.1⟩⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          have hres_inj : Function.Injective resEnd := by
            rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
            intro h hh
            have hlt_n : d_ma < n := by
              have := orbitRunCount_le_sub_orbitClassCard p s a m
              change T_ma ≤ n - d_ma at this
              omega
            ext c u
            have hc_mem := c.2
            simp only [Finset.mem_filter] at hc_mem
            obtain ⟨k, hstay, hleave⟩ :=
              exists_forward_runEndpoint p s a m hlt_n c.1 hc_mem.1 hc_mem.2
            have hwalk : ∀ j ≤ k,
                ∀ (hj_mem : c.1 + (j : ZMod d) * s ∈ (shiftOrbit s a).filter (fun x => p x = m)),
                h.1 ⟨c.1 + (j : ZMod d) * s, hj_mem⟩ = (ω ^ (j * D.val)) • h.1 c := by
              intro j
              induction j with
              | zero =>
                intro _ hj_mem
                have heq_sub : (⟨c.1 + (0 : ℕ) * s, hj_mem⟩ : BlockIdx a m) = c := by
                  apply Subtype.ext; simp
                rw [Nat.cast_zero] at *
                simp
              | succ j ih =>
                intro hj_le hj_mem
                have hj_prev_orb : c.1 + (j : ZMod d) * s ∈ shiftOrbit s a := by
                  have hrw : c.1 + ((j + 1 : ℕ) : ZMod d) * s =
                      (c.1 + (j : ZMod d) * s) + s := by push_cast; ring
                  have h1 := hj_mem
                  simp only [Finset.mem_filter] at h1
                  rw [hrw, mem_shiftOrbit_add_shift_iff] at h1
                  exact h1.1
                have hj_prev_mem :
                    c.1 + (j : ZMod d) * s ∈ (shiftOrbit s a).filter (fun x => p x = m) :=
                  Finset.mem_filter.mpr ⟨hj_prev_orb, hstay j (by omega)⟩
                have hcs_mem :
                    (c.1 + (j : ZMod d) * s) + s ∈
                      (shiftOrbit s a).filter (fun x => p x = m) := by
                  have hrw : (c.1 + (j : ZMod d) * s) + s =
                      c.1 + ((j + 1 : ℕ) : ZMod d) * s := by push_cast; ring
                  rwa [hrw]
                have hstep := h.2 ⟨c.1 + (j : ZMod d) * s, hj_prev_mem⟩ hcs_mem
                have heq_sub : (⟨(c.1 + (j : ZMod d) * s) + s, hcs_mem⟩ : BlockIdx a m) =
                    ⟨c.1 + ((j + 1 : ℕ) : ZMod d) * s, hj_mem⟩ := by
                  apply Subtype.ext; push_cast; ring
                rw [← heq_sub, hstep, ih (by omega) hj_prev_mem, smul_smul]
                have hexp : (j + 1) * D.val = D.val + j * D.val := by ring
                rw [hexp, pow_add]
            have he_orb : c.1 + (k : ZMod d) * s ∈ shiftOrbit s a := by
              have hstep_orb : ∀ j : ℕ, c.1 + (j : ZMod d) * s ∈ shiftOrbit s a := by
                intro j
                induction j with
                | zero => simpa using hc_mem.1
                | succ j ih =>
                  have hrw : c.1 + ((j + 1 : ℕ) : ZMod d) * s =
                      (c.1 + (j : ZMod d) * s) + s := by push_cast; ring
                  rw [hrw, mem_shiftOrbit_add_shift_iff]
                  exact ih
              exact hstep_orb k
            have he_blk : c.1 + (k : ZMod d) * s ∈ (shiftOrbit s a).filter (fun x => p x = m) :=
              Finset.mem_filter.mpr ⟨he_orb, hstay k le_rfl⟩
            have he_end : c.1 + (k : ZMod d) * s ∈
                (shiftOrbit s a).filter (fun x => p x = m ∧ p (x + s) ≠ m) := by
              simp only [Finset.mem_filter]
              refine ⟨he_orb, hstay k le_rfl, ?_⟩
              have hrw : (c.1 + (k : ZMod d) * s) + s = c.1 + ((k + 1 : ℕ) : ZMod d) * s := by
                push_cast; ring
              rwa [hrw]
            have hend_zero : h.1 ⟨c.1 + (k : ZMod d) * s, he_blk⟩ u = 0 :=
              congrFun (congrFun hh ⟨c.1 + (k : ZMod d) * s, he_end⟩) u
            have hrel := congrFun (hwalk k le_rfl he_blk) u
            rw [hend_zero] at hrel
            simp only [Pi.smul_apply, smul_eq_mul] at hrel
            have hpow_ne : ω ^ (k * D.val) ≠ 0 :=
              pow_ne_zero _ (hω.ne_zero (NeZero.ne n))
            exact (mul_eq_zero.mp hrel.symm).resolve_left hpow_ne
          refine le_trans (LinearMap.finrank_le_finrank_of_injective hres_inj) ?_
          rw [Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_pi, Fintype.card_fin,
            Finset.card_univ, Fintype.card_coe]
          simp only [smul_eq_mul]
          exact le_of_eq (Nat.mul_comm _ _)
        simp only [stepRunBound, hd0, hT0, ↓reduceIte]
        rcases le_total T_ma (1 + (D.val - d_ma)) with hmin | hmin
        · rw [min_eq_left hmin]
          exact hrun_le
        · rw [min_eq_right hmin]
          exact hpoly_le
  -- Step 4: Assemble total space S D ≤ A = ZMod d → Fin g → Fin b → K
  let S : Fin n → Submodule K A := fun k =>
    let D : Fin n := ⟨n - 1 - k.val, by omega⟩
    { carrier := {f | ∀ (a : Fin g) (m : Fin M) (a' : Fin g),
        (fun c : BlockIdx a m => f c.1 a') ∈ BlockSpace a m D}
      add_mem' := fun {f₁ f₂} h₁ h₂ a m a' => (BlockSpace a m D).add_mem (h₁ a m a') (h₂ a m a')
      zero_mem' := fun a m a' => (BlockSpace a m D).zero_mem
      smul_mem' := fun r {f} hf a m a' => (BlockSpace a m D).smul_mem r (hf a m a') }
  have hS_finrank : ∀ k : Fin n,
      finrank K (S k) ≤
        ∑ a : Fin g, ∑ m : Fin M,
          b * g * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) (n - 1 - k.val) := by
    intro k
    let D : Fin n := ⟨n - 1 - k.val, by omega⟩
    let embS : S k →ₗ[K] (∀ (a : Fin g) (m : Fin M) (_ : Fin g), BlockSpace a m D) :=
      { toFun := fun f a m a' => ⟨fun c => f.1 c.1 a', f.2 a m a'⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hemb_inj : Function.Injective embS := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro f hf
      ext c a' u
      obtain ⟨⟨a, t⟩, rfl⟩ := (orbitParamEquiv s).surjective c
      let m := p (orbitParamEquiv s (a, t))
      have hc_mem : orbitParamEquiv s (a, t) ∈ (shiftOrbit s a).filter (fun x => p x = m) :=
        Finset.mem_filter.mpr ⟨orbitElem_mem_shiftOrbit s a t, rfl⟩
      have hval := congrArg Subtype.val (congrFun (congrFun (congrFun hf a) m) a')
      exact congrFun (congrFun hval ⟨orbitParamEquiv s (a, t), hc_mem⟩) u
    refine le_trans (LinearMap.finrank_le_finrank_of_injective hemb_inj) ?_
    rw [Module.finrank_pi_fintype]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Module.finrank_pi_fintype]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    have hb_le := hBlock_finrank a m D
    calc g * finrank K (BlockSpace a m D)
        ≤ g * (b * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) D.val) :=
          Nat.mul_le_mul_left g hb_le
      _ = b * g * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) (n - 1 - k.val) := by
          dsimp [D]; ring
  -- Step 5: Verify prefix hypothesis for LeanMachine.SequentialDimension.finrank_le_sum_of_prefix
  let σ : Equiv.Perm (Fin n) :=
    { toFun := fun k => ⟨n - 1 - k.val, by omega⟩
      invFun := fun k => ⟨n - 1 - k.val, by omega⟩
      left_inv := fun k => by ext; dsimp; have := k.isLt; omega
      right_inv := fun k => by ext; dsimp; have := k.isLt; omega }
  have hprefix : ∀ (k : Fin n) (α : Fin n → A),
      α ∈ C → (∀ u < k, α (σ u) = 0) → α (σ k) ∈ S k := by
    intro k α hα hprev a m a'
    obtain ⟨X, ⟨hX0, hXs⟩, hXα⟩ := hα
    let D : Fin n := σ k
    have hvanish_gt : ∀ η : Fin n, D.val < η.val → α η = 0 := by
      intro η hgt
      have hu_lt : σ η < k := by
        show n - 1 - η.val < k.val
        have := η.isLt
        dsimp [D, σ] at hgt ⊢
        omega
      have h0 := hprev (σ η) hu_lt
      have hσσ : σ (σ η) = η := σ.left_inv η
      rwa [hσσ] at h0
    have hX_trunc :
        X = ∑ η : Fin (D.val + 1), modeLift ω s ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩
          (α ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩) := by
      rw [← sum_modeLift_fourierCoeffs hω hnK X, hXα]
      let emb : Fin (D.val + 1) ↪ Fin n :=
        ⟨fun η => ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩,
         fun η₁ η₂ h => Fin.ext (Fin.mk.inj h)⟩
      rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin (D.val + 1))).map emb))]
      · rw [Finset.sum_map]
        rfl
      · intro η _ hnot
        have hgt : D.val < η.val := by
          by_contra hle
          exact hnot (Finset.mem_map.mpr
            ⟨⟨η.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        rw [hvanish_gt η hgt, map_zero]
    -- Define coefficient tuple v : Fin (D.val + 1) → Fin b → K
    let v : Fin (D.val + 1) → Fin b → K := fun η =>
      ((n : K)⁻¹) • ∑ q : Fin n, ((ω ^ D.val)⁻¹ ^ q.val) •
        decK m (laneRot (a.val : ZMod d)
          (modeLift ω s ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩
            (α ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩)))
          (orbitElem s a' q)
    -- Prove equations (1) and (2) for every t : Fin n with p (orbitElem s a t) = m
    have heq1 : ∀ (t : Fin n), p (orbitElem s a t) = m →
        α D (orbitElem s a t) a' = ∑ η : Fin (D.val + 1), (ω ^ (t.val * η.val)) • v η := by
      intro t hpt
      have hαD : α D (orbitElem s a t) a' = fourierCoeffs ω s X D (orbitElem s a t) a' := by
        rw [hXα]
      rw [hαD]
      dsimp only [fourierCoeffs, LinearMap.coe_mk, AddHom.coe_mk]
      have hrow : X (orbitElem s a t) = decK m (laneRot (orbitElem s a t) X) := by
        have h := hX0 (orbitElem s a t)
        rwa [hpt] at h
      have hrot_sum : laneRot (orbitElem s a t) X =
          ∑ η : Fin (D.val + 1), (ω ^ (t.val * η.val)) •
            laneRot (a.val : ZMod d)
              (modeLift ω s ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩
                (α ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩)) := by
        conv_lhs => rw [hX_trunc]
        rw [map_sum]
        refine Finset.sum_congr rfl fun η _ =>
          laneRot_orbitElem_modeLift hω ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩ _ a t
      funext u
      simp only [hrow, hrot_sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, v]
      dsimp only [n, K]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η _ => ?_
      refine Finset.sum_congr rfl fun q _ => by ring
    have heq2 : ∀ (t : Fin n), p (orbitElem s a t) = m →
        (ω ^ D.val) • α D (orbitElem s a t) a' =
          ∑ η : Fin (D.val + 1), (ω ^ ((t.val + 1) * η.val)) • v η := by
      intro t hpt
      have hrot_s_X : fourierCoeffs ω s (laneRot s X) D = (ω ^ D.val) • α D := by
        conv_lhs => rw [← sum_modeLift_fourierCoeffs hω hnK X, hXα]
        rw [map_sum, map_sum, Finset.sum_apply]
        rw [Finset.sum_eq_single D]
        · rw [laneRot_s_modeLift hω, map_smul, Pi.smul_apply, fourierCoeffs_modeLift hω hnK]
          simp
        · intro η _ hne
          rw [laneRot_s_modeLift hω, map_smul, Pi.smul_apply, fourierCoeffs_modeLift hω hnK]
          simp [hne]
        · intro habs; exact False.elim (habs (Finset.mem_univ D))
      have hαD : (ω ^ D.val) • α D (orbitElem s a t) a' =
          fourierCoeffs ω s (laneRot s X) D (orbitElem s a t) a' := by
        rw [hrot_s_X]; rfl
      rw [hαD]
      dsimp only [fourierCoeffs, LinearMap.coe_mk, AddHom.coe_mk]
      have hrow : (laneRot s X) (orbitElem s a t) =
          decK m (laneRot (orbitElem s a t) (laneRot s X)) := by
        have h := hXs (orbitElem s a t)
        rwa [hpt] at h
      let t' : Fin n := ⟨(t.val + 1) % n, Nat.mod_lt _ (shiftOrbitLen_pos d s)⟩
      have hrot_comb : laneRot (orbitElem s a t) (laneRot s X) =
          laneRot (orbitElem s a t') X := by
        ext i j u
        simp only [laneRot_apply]
        have hsucc := orbitElem_succ_mod s a t
        dsimp only [t']
        rw [hsucc]
        exact congrArg (fun z => X i z u) (by ring)
      have hrot_sum : laneRot (orbitElem s a t') X =
          ∑ η : Fin (D.val + 1), (ω ^ ((t.val + 1) * η.val)) •
            laneRot (a.val : ZMod d)
              (modeLift ω s ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩
                (α ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩)) := by
        conv_lhs => rw [hX_trunc]
        rw [map_sum]
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [laneRot_orbitElem_modeLift hω ⟨η.val, lt_of_lt_of_le η.isLt D.isLt⟩ _ a t']
        dsimp [t']
        rw [pow_mod_orbitLen_mul hω.pow_eq_one (t.val + 1) η.val]
      funext u
      simp only [hrow, hrot_comb, hrot_sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, v]
      dsimp only [n, K]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun η _ => ?_
      refine Finset.sum_congr rfl fun q _ => by ring
    -- Show membership in PolyCoeffSub.map evalMap ⊓ RunStepSub
    refine ⟨?_, ?_⟩
    · refine ⟨v, ?_, ?_⟩
      · intro u z hz
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨t, hpt, rfl⟩ := hz
        have h1 := congrFun (heq1 t hpt) u
        have h2 := congrFun (heq2 t hpt) u
        simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h1 h2
        have hdiff :
            ∑ η : Fin (D.val + 1),
              (ω ^ ((t.val + 1) * η.val) - ω ^ D.val * ω ^ (t.val * η.val)) * v η u = 0 := by
          simp only [sub_mul, Finset.sum_sub_distrib]
          rw [← h2]
          have hmul1 : ∑ x : Fin (D.val + 1), ω ^ D.val * ω ^ (t.val * x.val) * v x u =
              ω ^ D.val * ∑ x : Fin (D.val + 1), ω ^ (t.val * x.val) * v x u := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
          rw [hmul1, ← h1, sub_self]
        rw [Fin.sum_univ_castSucc] at hdiff
        have hlast0 :
            (ω ^ ((t.val + 1) * (Fin.last D.val).val) -
              ω ^ D.val * ω ^ (t.val * (Fin.last D.val).val)) * v (Fin.last D.val) u = 0 := by
          simp only [Fin.val_last]
          have hexp : (t.val + 1) * D.val = D.val + t.val * D.val := by ring
          rw [hexp, pow_add, sub_self, zero_mul]
        rw [hlast0, add_zero] at hdiff
        rw [← hdiff]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Fin.val_castSucc]
        have hexp : (t.val + 1) * j.val = j.val + t.val * j.val := by ring
        have hpowD : ω ^ D.val = ω ^ (n - 1 - k.val) := rfl
        rw [hexp, pow_add, pow_mul, hpowD]
        ring
      · funext c u
        have hc := c.2
        simp only [Finset.mem_filter] at hc
        obtain ⟨⟨a₁, t⟩, heq_c⟩ := (orbitParamEquiv s).surjective c.1
        have hm₁ := orbitElem_mem_shiftOrbit s a₁ t
        have hc_orb := hc.1
        have heq_elem : orbitElem s a₁ t = c.1 := heq_c
        rw [← heq_elem] at hc_orb
        simp only [shiftOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hc_orb
        have ha_eq : a₁ = a := Fin.ext (by rw [← hm₁, hc_orb])
        subst a₁
        have hsymm : ((orbitParamEquiv s).symm c.1).2 = t := by
          rw [← heq_c, (orbitParamEquiv s).symm_apply_apply]
        have hpt : p (orbitElem s a t) = m := by
          rw [heq_elem]
          exact hc.2
        have h1 := congrFun (heq1 t hpt) u
        change (∑ η : Fin (D.val + 1),
          (ω ^ (((orbitParamEquiv s).symm c.1).2.val * η.val)) • v η) u = α D c.1 a' u
        rw [hsymm, ← heq_elem]
        exact h1.symm
    · intro c hcs
      have hc := c.2
      simp only [Finset.mem_filter] at hc hcs
      obtain ⟨⟨a₁, t⟩, heq_c⟩ := (orbitParamEquiv s).surjective c.1
      have hm₁ := orbitElem_mem_shiftOrbit s a₁ t
      have hc_orb := hc.1
      have heq_elem : orbitElem s a₁ t = c.1 := heq_c
      rw [← heq_elem] at hc_orb
      simp only [shiftOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hc_orb
      have ha_eq : a₁ = a := Fin.ext (by rw [← hm₁, hc_orb])
      subst a₁
      have hpt : p (orbitElem s a t) = m := by
        rw [heq_elem]; exact hc.2
      let t' : Fin n := ⟨(t.val + 1) % n, Nat.mod_lt _ (shiftOrbitLen_pos d s)⟩
      have hsucc : orbitElem s a t' = c.1 + s := by
        dsimp [t']
        rw [orbitElem_succ_mod, heq_elem]
      have hpt' : p (orbitElem s a t') = m := by
        rw [hsucc]; exact hcs.2
      have h1' := heq1 t' hpt'
      have h2 := heq2 t hpt
      rw [hsucc] at h1'
      have hrhs_eq :
          (∑ η : Fin (D.val + 1), (ω ^ (t'.val * η.val)) • v η) =
          (∑ η : Fin (D.val + 1), (ω ^ ((t.val + 1) * η.val)) • v η) := by
        refine Finset.sum_congr rfl fun η _ => ?_
        dsimp [t']
        rw [pow_mod_orbitLen_mul hω.pow_eq_one (t.val + 1) η.val]
      change α D (c.1 + s) a' = (ω ^ D.val) • α D c.1 a'
      rw [h1', hrhs_eq, ← h2, heq_elem]
  -- Step 6: Sum over k : Fin n and simplify to theorem1ASingleShiftBound
  have hseq := LeanMachine.SequentialDimension.finrank_le_sum_of_prefix C σ S hprefix
  have hnat_bound :
      finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) ≤
        ∑ k : Fin n, ∑ a : Fin g, ∑ m : Fin M,
          b * g * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) (n - 1 - k.val) := by
    calc finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s))
        ≤ finrank K WK := hbase_le
      _ = finrank K C := hWK_eq_C
      _ ≤ ∑ k : Fin n, finrank K (S k) := hseq
      _ ≤ ∑ k : Fin n, ∑ a : Fin g, ∑ m : Fin M,
            b * g * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) (n - 1 - k.val) :=
          Finset.sum_le_sum fun k _ => hS_finrank k
  -- Reindex D = σ k and cast to ℝ
  have hreal_le : (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤
      ((∑ k : Fin n, ∑ a : Fin g, ∑ m : Fin M,
          b * g * stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a)
            (n - 1 - k.val) : ℕ) : ℝ) := by
    exact_mod_cast hnat_bound
  refine le_trans hreal_le (le_of_eq ?_)
  push_cast
  have hswap1 :
      (∑ k : Fin n, ∑ a : Fin g, ∑ m : Fin M,
        (b : ℝ) * (g : ℝ) *
          (stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) (n - 1 - k.val) : ℝ)) =
      (b * g : ℝ) * ∑ a : Fin g, ∑ m : Fin M,
        ∑ D : Fin n, (stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) D.val : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := Finset.univ (α := Fin n))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Equiv.sum_comp σ (fun D : Fin n =>
      (b * g : ℝ) *
        (stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) D.val : ℝ))
  rw [hswap1]
  have hsum_D : ∀ (a : Fin g) (m : Fin M),
      (∑ D : Fin n, (stepRunBound (orbitClassCard p s m a) (orbitRunCount p s m a) D.val : ℝ)) =
        (orbitClassCard p s m a : ℝ) +
          ((orbitRunCount p s m a : ℝ) * ((n : ℝ) - (orbitClassCard p s m a : ℝ)) -
            (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ)) := by
    intro a m
    exact sum_stepRunBound_real_eq
      (orbitClassCard_le_orbitLen p s a m)
      (orbitRunCount_le_orbitClassCard p s a m)
      (orbitRunCount_le_sub_orbitClassCard p s a m)
      (orbitClassCard_eq_orbitLen_of_runCount_zero p s a m)
  simp_rw [hsum_D]
  have hsplit :
      (∑ a : Fin g, ∑ m : Fin M,
        ((orbitClassCard p s m a : ℝ) +
          ((orbitRunCount p s m a : ℝ) * ((n : ℝ) - (orbitClassCard p s m a : ℝ)) -
            (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ) ^ 2 +
            (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ)))) =
      (∑ a : Fin g, ∑ m : Fin M, (orbitClassCard p s m a : ℝ)) +
      (∑ a : Fin g, ∑ m : Fin M,
        ((orbitRunCount p s m a : ℝ) * ((n : ℝ) - (orbitClassCard p s m a : ℝ)) -
          (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ) ^ 2 +
          (1 / 2 : ℝ) * (orbitRunCount p s m a : ℝ))) := by
    simp_rw [Finset.sum_add_distrib]
  have hsum_cards :
      (∑ a : Fin g, ∑ m : Fin M, (orbitClassCard p s m a : ℝ)) = (d : ℝ) := by
    have h1 : ∀ a : Fin g, (∑ m : Fin M, (orbitClassCard p s m a : ℝ)) = (n : ℝ) := by
      intro a
      exact_mod_cast sum_orbitClassCard_eq p s a
    simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hgn : (g : ℝ) * (n : ℝ) = (d : ℝ) := by
      exact_mod_cast shiftGcd_mul_orbitLen d s
    exact hgn
  rw [hsplit, hsum_cards]
  unfold theorem1ASingleShiftBound
  dsimp only [g, n]
  ring

/-- Direct unpacked theorem for `Theorem 1A`: single-shift intersection bound for `b`-lane linear
class-uniform codes when `gcd(d / gcd(d, s), char F) = 1`. -/
theorem linearClassUniform_singleShift_finrank_le
    (F : Type*) [Field F] {d M b : ℕ} [NeZero d] [NeZero M] [NeZero b]
    (p : ZMod d → Fin M) (s : ZMod d)
    (hchar : CoprimeToChar F (shiftOrbitLen d s))
    (𝒳 : Submodule F (Matrix (ZMod d) (ZMod d) (Fin b → F)))
    (hLin : IsLinearClassUniformCode p 𝒳) :
    (finrank F ↥(𝒳 ⊓ 𝒳.comap (laneRot s)) : ℝ) ≤ theorem1ASingleShiftBound b p s :=
  (extension_Theorem1A_SingleShift F d M b p s).2 hchar 𝒳 hLin

end FourierRunFiltration

end BoundedArityDecoders
