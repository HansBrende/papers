import SharedDecoders.CompositionAnchored
import Mathlib.Data.Set.Finite.Lemmas

/-! # From literal local binary moves to global word transitivity -/

namespace SharedDecoders

variable {d : ℕ} [NeZero d]

abbrev BitWord (d : ℕ) := ScalarWord d (ZMod 2)

noncomputable def bitSupport (x : BitWord d) : Finset (ZMod d) := by
  classical
  exact Finset.univ.filter (fun i => x i = 1)

@[simp] lemma mem_bitSupport (x : BitWord d) (i : ZMod d) :
    i ∈ bitSupport x ↔ x i = 1 := by
  classical
  simp [bitSupport]

lemma bit_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  have hn : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
  have hlt := ZMod.val_lt a
  have he : a.val = 1 := by omega
  simpa [he] using (ZMod.natCast_zmod_val a).symm

lemma bitSupport_nonempty {x : BitWord d} (hx : x ≠ 0) : (bitSupport x).Nonempty := by
  have h : ∃ i, x i ≠ 0 := by simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hx
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (mem_bitSupport x i).mpr (bit_eq_one_of_ne_zero hi)⟩

lemma bitSupport_reindex_card (e : Equiv.Perm (ZMod d)) (x : BitWord d) :
    (bitSupport (fun i => x (e i))).card = (bitSupport x).card := by
  classical
  have h := Nat.card_congr (e.subtypeEquiv
    (p := fun i => x (e i) = 1) (q := fun i => x i = 1) (fun _ => Iff.rfl))
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, bitSupport] using h

lemma bitSupport_rotation_card (s : ZMod d) (x : BitWord d) :
    (bitSupport (scalarRotation s x)).card = (bitSupport x).card :=
  bitSupport_reindex_card (Equiv.addRight s) x

lemma bitSupport_move_card (_h01 : (0 : ZMod d) ≠ 1) (x y : BitWord d)
    (hx0 : x 0 = 1) (hx1 : x 1 = 0) (hy0 : y 0 = 0) (hy1 : y 1 = 1)
    (hout : ∀ i, i ≠ 0 → i ≠ 1 → y i = x i) :
    (bitSupport y).card = (bitSupport x).card := by
  classical
  have he : y = fun i => x (Equiv.swap 0 1 i) := by
    funext i
    by_cases hi0 : i = 0
    · subst i
      simp [hy0, hx1]
    · by_cases hi1 : i = 1
      · subst i
        simp [hy1, hx0]
      · simp [Equiv.swap_apply_of_ne_of_ne hi0 hi1, hout i hi0 hi1]
  rw [he]
  exact bitSupport_reindex_card _ _

lemma bitSupport_unit_of_card_le_one (x : BitWord d) (hx0 : x 0 = 1)
    (hc : (bitSupport x).card ≤ 1) : x = Pi.single 0 1 := by
  classical
  funext i
  by_cases hi : i = 0
  · simp [hi, hx0]
  · have hz : x i = 0 := by
      by_contra hn
      have hm : i ∈ bitSupport x := (mem_bitSupport x i).mpr (bit_eq_one_of_ne_zero hn)
      exact hi (Finset.card_le_one.mp hc i hm 0 ((mem_bitSupport x 0).mpr hx0))
    simp [hi, hz]

/-- Reachability is through actual permutations in one fixed subgroup. -/
def wordReach (G : Subgroup (Equiv.Perm (BitWord d))) (x y : BitWord d) : Prop :=
  ∃ g : G, g.val x = y

omit [NeZero d] in
lemma wordReach_refl (G : Subgroup (Equiv.Perm (BitWord d))) (x : BitWord d) :
    wordReach G x x := ⟨1, rfl⟩

omit [NeZero d] in
lemma wordReach_trans {G : Subgroup (Equiv.Perm (BitWord d))} {x y z : BitWord d}
    (hxy : wordReach G x y) (hyz : wordReach G y z) : wordReach G x z := by
  obtain ⟨g, rfl⟩ := hxy
  obtain ⟨h, hh⟩ := hyz
  exact ⟨h * g, hh⟩

omit [NeZero d] in
lemma wordReach_symm {G : Subgroup (Equiv.Perm (BitWord d))} {x y : BitWord d}
    (hxy : wordReach G x y) : wordReach G y x := by
  obtain ⟨g, rfl⟩ := hxy
  exact ⟨g⁻¹, g.val.symm_apply_apply x⟩

omit [NeZero d] in
lemma wordReach_nonzero {G : Subgroup (Equiv.Perm (BitWord d))}
    (hzero : ∀ g : G, g.val 0 = 0) {x y : BitWord d}
    (hx : x ≠ 0) (hxy : wordReach G x y) : y ≠ 0 := by
  obtain ⟨g, rfl⟩ := hxy
  intro he
  exact hx (g.val.injective (he.trans (hzero g).symm))

/-- A move across two zeroes, together with a local merge, suffices for global
transitivity.  The proof minimizes support first and the next occupied address
second; all intermediate words lie in the same actual permutation orbit. -/
theorem local_moves_reach_unit (hd : 3 ≤ d)
    (G : Subgroup (Equiv.Perm (BitWord d)))
    (hzero : ∀ g : G, g.val 0 = 0)
    (hrot : ∀ s, scalarRotation s ∈ G)
    (hmove : ∀ x : BitWord d, x 0 = 1 → x 1 = 0 → x 2 = 0 →
      ∃ y, wordReach G x y ∧ y 0 = 0 ∧ y 1 = 1 ∧
        ∀ i, i ≠ 0 → i ≠ 1 → y i = x i)
    (hmerge : ∀ x : BitWord d, x 0 = 1 → (x 1 = 1 ∨ x 2 = 1) →
      ∃ y, wordReach G x y ∧ (bitSupport y).card < (bitSupport x).card)
    (x : BitWord d) (hx : x ≠ 0) : wordReach G x (Pi.single 0 1) := by
  classical
  let O : Set (BitWord d) := {y | wordReach G x y}
  obtain ⟨y, hy, hmin⟩ := Set.exists_min_image O (fun y => (bitSupport y).card)
    O.toFinite ⟨x, wordReach_refl G x⟩
  have hyne : y ≠ 0 := wordReach_nonzero hzero hx hy
  obtain ⟨a, ha⟩ := bitSupport_nonempty hyne
  let z := scalarRotation a y
  have hzy : wordReach G y z := ⟨⟨_, hrot a⟩, rfl⟩
  have hz : wordReach G x z := wordReach_trans hy hzy
  have hz0 : z 0 = 1 := by simpa [z, scalarRotation] using (mem_bitSupport y a).mp ha
  have hzc : (bitSupport z).card = (bitSupport y).card := bitSupport_rotation_card a y
  by_cases hc : (bitSupport z).card ≤ 1
  · exact (bitSupport_unit_of_card_le_one z hz0 hc) ▸ hz
  have hlarge : 1 < (bitSupport z).card := by omega
  obtain ⟨c, hc, hc0⟩ := Finset.exists_mem_ne hlarge 0
  let S : Set (BitWord d × ZMod d) := {v | wordReach G x v.1 ∧
    (bitSupport v.1).card = (bitSupport y).card ∧ v.1 0 = 1 ∧
      v.1 v.2 = 1 ∧ v.2 ≠ 0}
  have hSne : S.Nonempty := ⟨(z,c), hz, hzc, hz0, (mem_bitSupport z c).mp hc, hc0⟩
  obtain ⟨⟨v,j⟩, hv, hjmin⟩ := Set.exists_min_image S (fun v => v.2.val) S.toFinite hSne
  rcases hv with ⟨hv, hvc, hv0, hvj, hj0⟩
  change (bitSupport v).card = (bitSupport y).card at hvc
  have hnnear : ¬(v 1 = 1 ∨ v 2 = 1) := by
    intro he
    obtain ⟨w, hw, hwc⟩ := hmerge v hv0 he
    have hm := hmin w (wordReach_trans hv hw)
    omega
  have hv1 : v 1 = 0 := by
    by_contra h
    exact hnnear (Or.inl (bit_eq_one_of_ne_zero h))
  have hv2 : v 2 = 0 := by
    by_contra h
    exact hnnear (Or.inr (bit_eq_one_of_ne_zero h))
  have hj1 : j ≠ 1 := by intro h; subst j; simp [hv1] at hvj
  have hjv : 1 < j.val := by
    have h0 : j.val ≠ 0 := fun h => hj0 ((ZMod.val_eq_zero j).mp h)
    have h1 : j.val ≠ 1 := by
      intro h
      apply hj1
      simpa [h] using (ZMod.natCast_zmod_val j).symm
    omega
  have h01 : (0 : ZMod d) ≠ 1 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < d by omega)] at hv
  obtain ⟨w, hw, hw0, hw1, hwout⟩ := hmove v hv0 hv1 hv2
  have hwc := bitSupport_move_card h01 v w hv0 hv1 hw0 hw1 hwout
  let v' := scalarRotation 1 w
  have hv'w : wordReach G w v' := ⟨⟨_, hrot 1⟩, rfl⟩
  have hv' : wordReach G x v' := wordReach_trans hv (wordReach_trans hw hv'w)
  have hv'0 : v' 0 = 1 := by simpa [v', scalarRotation] using hw1
  have hv'j : v' (j-1) = 1 := by
    simpa [v', scalarRotation] using (hwout j hj0 hj1).trans hvj
  have hpred : (j-1).val = j.val - 1 := by
    have h1val : (1 : ZMod d).val = 1 := by
      simp [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < d by omega)]
    rw [ZMod.val_sub (by omega), h1val]
  have hjpred : j-1 ≠ 0 := by
    intro h
    have hh := congrArg ZMod.val h
    simp only [hpred, ZMod.val_zero] at hh
    omega
  have hmem : (v',j-1) ∈ S := ⟨hv',
    (bitSupport_rotation_card 1 w).trans (hwc.trans hvc), hv'0, hv'j, hjpred⟩
  have hh := hjmin (v',j-1) hmem
  change j.val ≤ (j-1).val at hh
  omega

theorem local_moves_transitive (hd : 3 ≤ d)
    (G : Subgroup (Equiv.Perm (BitWord d)))
    (hzero : ∀ g : G, g.val 0 = 0)
    (hrot : ∀ s, scalarRotation s ∈ G)
    (hmove : ∀ x : BitWord d, x 0 = 1 → x 1 = 0 → x 2 = 0 →
      ∃ y, wordReach G x y ∧ y 0 = 0 ∧ y 1 = 1 ∧
        ∀ i, i ≠ 0 → i ≠ 1 → y i = x i)
    (hmerge : ∀ x : BitWord d, x 0 = 1 → (x 1 = 1 ∨ x 2 = 1) →
      ∃ y, wordReach G x y ∧ (bitSupport y).card < (bitSupport x).card)
    (x y : BitWord d) (hx : x ≠ 0) (hy : y ≠ 0) : wordReach G x y :=
  wordReach_trans (local_moves_reach_unit hd G hzero hrot hmove hmerge x hx)
    (wordReach_symm (local_moves_reach_unit hd G hzero hrot hmove hmerge y hy))

end SharedDecoders
