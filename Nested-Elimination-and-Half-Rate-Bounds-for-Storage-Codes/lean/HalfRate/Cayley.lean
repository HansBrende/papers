import HalfRate.Circulant
import HalfRate.U3

/-!
# Corollary CC: Cayley relations `Cay(G, {s, s⁻¹, t})`

For a finite group `G` and `S = {s, s⁻¹, t}` with `|S| = 3` and `1 ∉ S`, the Cayley digraph with
arcs `g → g x` (`x ∈ S`) is a recovery relation whose in-neighbourhoods are
`N(q) = {q s⁻¹, q s, q t⁻¹}`. If it has no transitive triangle, the weighted half bound holds.
* If `t = t⁻¹`, the underlying graph is cubic and Theorem U3 applies.
* Otherwise the blocks are the cosets `g⟨s⟩`: every vertex has exactly one in-neighbour outside
  its coset (`q t⁻¹`), outside parents are private, and each coset is a digon cycle of length
  `ord(s)`. It is chordless if `t ∉ ⟨s⟩` (`elimOn_cycle`), and a circulant with offset `k` if
  `t = s^k` (`elimOn_circulant`, applied with the generator `s` or `s⁻¹` as Proposition CC
  dictates). Theorem PC (`rateBound_pc_ac`) combines the cosets.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The recovery relation of `Cay(G, {s, s⁻¹, t})` with arcs `g → g x`: the in-neighbours of `q`
are `q s⁻¹`, `q s` and `q t⁻¹`. -/
def cayN (s t : G) (q : G) : Finset G := {q * s⁻¹, q * s, q * t⁻¹}

omit [Fintype G] in
theorem mem_cayN {s t q x : G} : x ∈ cayN s t q ↔ x = q * s⁻¹ ∨ x = q * s ∨ x = q * t⁻¹ := by
  simp [cayN]

omit [Fintype G] [DecidableEq G] in
/-- In a coset indexed by the powers of `u`, an in-neighbour `g u^i` of `g u^j` through `u` or
`u⁻¹` sits at the neighbouring position. -/
theorem coset_steps {u g : G} {m i j : ℕ} (hm : orderOf u = m) (hi : i < m) (hj : j < m)
    (h : g * u ^ i = g * u ^ j * u ∨ g * u ^ i = g * u ^ j * u⁻¹) :
    i = (j + 1) % m ∨ j = (i + 1) % m := by
  rcases h with h | h
  · left
    rw [mul_assoc, ← pow_succ, mul_right_inj] at h
    have := (pow_eq_pow_iff_modEq.mp h)
    rw [hm] at this
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hi] at this
  · right
    have h' : u ^ (i + 1) = u ^ j := by
      rw [pow_succ, ← mul_right_inj g, ← mul_assoc, h]; group
    have := (pow_eq_pow_iff_modEq.mp h')
    rw [hm] at this
    unfold Nat.ModEq at this
    rw [Nat.mod_eq_of_lt hj] at this
    exact this.symm

omit [Fintype G] in
/-- The cosets of `⟨u⟩` are indexed by the powers of `u`. -/
theorem mem_coset_iff [Finite G] (u g : G) {m : ℕ} (hm : orderOf u = m) {H : Subgroup G}
    (hH : H = Subgroup.zpowers u) (x : G) :
    (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk g ↔ ∃ j : Fin m, g * u ^ j.val = x := by
  subst hm; subst hH
  constructor
  · intro h
    have hx : g⁻¹ * x ∈ Subgroup.zpowers u := by
      have := QuotientGroup.eq.mp h.symm
      simpa using this
    rw [(isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf] at hx
    obtain ⟨j, hj, hju⟩ := mem_image.mp hx
    refine ⟨⟨j, mem_range.mp hj⟩, ?_⟩
    simp only
    rw [hju]; group
  · rintro ⟨j, rfl⟩
    apply QuotientGroup.eq.mpr
    have : (g * u ^ j.val)⁻¹ * g = (u ^ j.val)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers u j.val)

/-- **Corollary CC.** -/
theorem rateBound_cayley {s t : G} (hS : ({s, s⁻¹, t} : Finset G).card = 3)
    (h1S : (1 : G) ∉ ({s, s⁻¹, t} : Finset G)) (hTT : TTFree (cayN s t)) :
    RateBound (cayN s t) (1 / 2) := by
  classical
  -- the generators are distinct and nontrivial
  have hss : s ≠ s⁻¹ := by
    intro h
    have e : ({s, s⁻¹, t} : Finset G) = {s, t} := by rw [← h]; ext x; simp
    have := card_le_two (a := s) (b := t); rw [e] at hS; omega
  have hst : s ≠ t := by
    intro h
    have e : ({s, s⁻¹, t} : Finset G) = {s, s⁻¹} := by rw [← h]; ext x; simp; tauto
    have := card_le_two (a := s) (b := s⁻¹); rw [e] at hS; omega
  have hs't : s⁻¹ ≠ t := by
    intro h
    have e : ({s, s⁻¹, t} : Finset G) = {s, s⁻¹} := by rw [← h]; ext x; simp
    have := card_le_two (a := s) (b := s⁻¹); rw [e] at hS; omega
  have hs1 : s ≠ 1 := fun h => h1S (by simp [h])
  have ht1 : t ≠ 1 := fun h => h1S (by simp [h])
  have hss1 : s * s ≠ 1 := fun h => hss (eq_inv_of_mul_eq_one_left h)
  have hs_ss : s ≠ s * s := fun h => hs1 (mul_left_cancel (h.symm.trans (mul_one s).symm))
  have hloop : ∀ q, q ∉ cayN s t q := by
    intro q hq
    rcases mem_cayN.mp hq with h | h | h
    · exact hs1 (inv_eq_one.mp (by simpa using h.symm))
    · exact hs1 (by simpa using h.symm)
    · exact ht1 (inv_eq_one.mp (by simpa using h.symm))
  -- a transitive triangle from three memberships
  have tt : ∀ x y z : G, x ≠ y → y ≠ z → x ≠ z → x ∈ cayN s t y → y ∈ cayN s t z →
      x ∈ cayN s t z → False := hTT
  by_cases htt : t * t = 1
  · -- `t = t⁻¹`: the underlying graph is cubic, Theorem U3
    have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left htt).symm
    refine rateBound_u3 hloop hTT fun v => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    refine (card_le_card (s := univ.filter ((und (cayN s t)).Adj v)) (t := {v * s, v * s⁻¹, v * t})
      ?_).trans card_le_three
    intro u hu
    simp only [mem_filter, mem_univ, true_and, und_adj] at hu
    obtain ⟨-, hu⟩ := hu
    simp only [mem_insert, mem_singleton]
    rcases hu with hu | hu
    · rcases mem_cayN.mp hu with h | h | h
      · left; rw [h]; group
      · right; left; rw [h]; group
      · right; right; rw [h]; group
    · rcases mem_cayN.mp hu with h | h | h
      · right; left; exact h
      · left; exact h
      · right; right; rw [h, htinv]
  -- `t ≠ t⁻¹`: the cosets of `⟨s⟩` are blocks with private outside parents
  have hfin : Fintype (G ⧸ Subgroup.zpowers s) := Fintype.ofFinite _
  let κ : G → G ⧸ Subgroup.zpowers s := fun x => x
  have hκs : ∀ q, κ (q * s) = κ q := fun q => by
    apply QuotientGroup.eq.mpr
    have : (q * s)⁻¹ * q = s⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers s)
  have hκs' : ∀ q, κ (q * s⁻¹) = κ q := fun q => by
    apply QuotientGroup.eq.mpr
    have : (q * s⁻¹)⁻¹ * q = s := by group
    rw [this]; exact Subgroup.mem_zpowers s
  obtain ⟨m, hm⟩ : ∃ m, orderOf s = m := ⟨_, rfl⟩
  have hm0 : 0 < m := hm ▸ orderOf_pos s
  have hsm : s ^ m = 1 := hm ▸ pow_orderOf_eq_one s
  have hm4 : 4 ≤ m := by
    rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h | h
    · exact absurd (orderOf_eq_one_iff.mp (hm.trans h)) hs1
    · rw [h, pow_two] at hsm; exact absurd hsm hss1
    · -- `s³ = 1` closes the transitive triangle `1 → s → s²` with `1 = s² · s`
      rw [h, pow_succ, pow_two] at hsm
      refine (tt 1 s (s * s) (Ne.symm hs1) hs_ss (Ne.symm hss1) ?_ ?_ ?_).elim
      · exact mem_cayN.mpr (Or.inl (by group))
      · exact mem_cayN.mpr (Or.inl (by group))
      · exact mem_cayN.mpr (Or.inr (Or.inl hsm.symm))
    · exact h
  refine rateBound_pc_ac hloop κ ?_ ?_ ?_
  · -- at most one in-neighbour outside the coset: `q t⁻¹`
    intro v u hu u' hu' huv hu'v
    have key : ∀ w ∈ cayN s t v, κ w ≠ κ v → w = v * t⁻¹ := by
      intro w hw hwv
      rcases mem_cayN.mp hw with h | h | h
      · exact absurd (h ▸ hκs' v) hwv
      · exact absurd (h ▸ hκs v) hwv
      · exact h
    rw [key u hu huv, key u' hu' hu'v]
  · -- outside parents are private: `w ∈ N v` across cosets forces `v = w t`
    intro w v v' hvv' hwv hw hw'
    have key : ∀ x, κ w ≠ κ x → w ∈ cayN s t x → x = w * t := by
      intro x hwx hx
      rcases mem_cayN.mp hx with h | h | h
      · exact absurd (by rw [h, hκs']) hwx
      · exact absurd (by rw [h, hκs]) hwx
      · rw [h]; group
    rw [key v hwv hw, key v' (hvv' ▸ hwv) hw']
  · -- every coset has an elimination certificate
    intro i
    right
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective i
    have hblock : univ.filter (fun x => κ x = (g : G ⧸ Subgroup.zpowers s)) =
        univ.image (fun j : Fin m => g * s ^ j.val) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_image]
      exact mem_coset_iff s g hm rfl x
    -- the in-neighbours of a coset vertex inside the coset, through `s` and `s⁻¹`
    have hsteps : ∀ (u : G), orderOf u = m → (u = s ∨ u = s⁻¹) → ∀ i j (hi : i < m) (hj : j < m),
        g * u ^ i ∈ cayN s t (g * u ^ j) →
        i = (j + 1) % m ∨ j = (i + 1) % m ∨ g * u ^ i = g * u ^ j * t⁻¹ := by
      intro u hum hu i j hi hj h
      rcases mem_cayN.mp h with h | h | h
      · rcases hu with rfl | rfl
        · rcases coset_steps hum hi hj (Or.inr h) with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · rcases coset_steps hum hi hj (Or.inl h) with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
      · rcases hu with rfl | rfl
        · rcases coset_steps hum hi hj (Or.inl h) with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · rcases coset_steps hum hi hj (Or.inr (h.trans (by rw [inv_inv]))) with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr h)
    have hinj : ∀ u : G, orderOf u = m → Function.Injective (fun j : Fin m => g * u ^ j.val) := by
      intro u hum a b hab
      have h' : u ^ a.val = u ^ b.val := mul_left_cancel hab
      have := pow_eq_pow_iff_modEq.mp h'
      rw [hum] at this
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at this
      exact Fin.ext this
    by_cases htin : t ∈ Subgroup.zpowers s
    · -- a circulant coset
      rw [(isOfFinOrder_of_finite s).mem_zpowers_iff_mem_range_orderOf] at htin
      obtain ⟨k, hk, hkt⟩ := mem_image.mp htin
      rw [mem_range, hm] at hk
      -- arithmetic conditions from `|S| = 3`, `1 ∉ S` and the absence of transitive triangles
      have hk0 : k ≠ 0 := by rintro rfl; exact ht1 (by rw [← hkt, pow_zero])
      have hk1 : k ≠ 1 := by rintro rfl; exact hst (by rw [← hkt, pow_one])
      have hkm1 : k ≠ m - 1 := by
        rintro rfl
        apply hs't
        rw [← hkt]
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel hm0, hsm]
      have hk2 : k ≠ 2 := by
        rintro rfl
        have ht2 : t = s * s := by rw [← hkt, pow_two]
        refine tt 1 s (s * s) (Ne.symm hs1) hs_ss (Ne.symm hss1) ?_ ?_ ?_
        · exact mem_cayN.mpr (Or.inl (by group))
        · exact mem_cayN.mpr (Or.inl (by group))
        · exact mem_cayN.mpr (Or.inr (Or.inr (by rw [ht2]; group)))
      have hkm2 : k ≠ m - 2 := by
        rintro hk'
        have ht' : t⁻¹ = s * s := by
          rw [← hkt]
          refine (eq_inv_of_mul_eq_one_left ?_).symm
          rw [hk', ← pow_two, ← pow_add, show 2 + (m - 2) = m by omega, hsm]
        refine tt (s * s) s 1 (fun h => hs1 (by simpa using h)) (Ne.symm hs1).symm
          hss1 ?_ ?_ ?_
        · exact mem_cayN.mpr (Or.inr (Or.inl rfl))
        · exact mem_cayN.mpr (Or.inr (Or.inl (by group)))
        · exact mem_cayN.mpr (Or.inr (Or.inr (by rw [ht']; group)))
      have hk3 : 3 ≤ k := by omega
      have hkm3 : k + 3 ≤ m := by omega
      have hp : 2 * k ≠ m + 1 := by
        intro h2k
        have hts : t * t = s := by
          rw [← hkt, ← pow_add, show k + k = 2 * k by omega, h2k, pow_succ, hsm, one_mul]
        refine tt 1 t s (Ne.symm ht1) hst.symm (Ne.symm hs1) ?_ ?_ ?_
        · exact mem_cayN.mpr (Or.inr (Or.inr (by group)))
        · exact mem_cayN.mpr (Or.inr (Or.inr (by rw [← hts]; group)))
        · exact mem_cayN.mpr (Or.inl (by group))
      have hn : 2 * k + 1 ≠ m := by
        intro h2k
        have hts : t * t = s⁻¹ := by
          rw [← hkt]
          refine eq_inv_of_mul_eq_one_left ?_
          rw [← pow_add, ← pow_succ, show k + k + 1 = 2 * k + 1 by omega, h2k, hsm]
        refine tt 1 t s⁻¹ (Ne.symm ht1) hs't.symm
          (fun h => hs1 (inv_eq_one.mp h.symm)) ?_ ?_ ?_
        · exact mem_cayN.mpr (Or.inr (Or.inr (by group)))
        · exact mem_cayN.mpr (Or.inr (Or.inr (by rw [← hts]; group)))
        · exact mem_cayN.mpr (Or.inr (Or.inl (by group)))
      rw [hblock]
      rcases circulant_sweep hk3 hkm3 hp hn with ⟨h1', h3'⟩ | ⟨h1', h3'⟩
      · -- the sweep with the generator `s` and offset `k`
        refine elimOn_circulant hk3 hkm3 _ (hinj s hm) h1' h3' ?_
        intro i j hi hj h
        rcases hsteps s hm (Or.inl rfl) i j hi hj h with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · right; right
          have e2 : s ^ i = s ^ j * t⁻¹ := mul_left_cancel (e.trans (mul_assoc _ _ _))
          have h' : s ^ (i + k) = s ^ j := by
            rw [pow_add, hkt, e2]; group
          have := pow_eq_pow_iff_modEq.mp h'
          rw [hm] at this
          unfold Nat.ModEq at this
          rw [Nat.mod_eq_of_lt hj] at this
          exact this.symm
      · -- the mirror sweep: the generator `s⁻¹` and offset `m - k`
        have hm' : orderOf s⁻¹ = m := (orderOf_inv s).trans hm
        have hblock' : univ.image (fun j : Fin m => g * s ^ j.val) =
            univ.image (fun j : Fin m => g * s⁻¹ ^ j.val) := by
          ext x
          simp only [mem_univ, true_and, mem_image]
          rw [← mem_coset_iff s g hm rfl x, mem_coset_iff s⁻¹ g hm' Subgroup.zpowers_inv.symm x]
        rw [hblock']
        have ht' : t = s⁻¹ ^ (m - k) := by
          rw [← hkt, inv_pow]
          refine (inv_eq_of_mul_eq_one_right ?_).symm
          rw [← pow_add, show m - k + k = m by omega, hsm]
        refine elimOn_circulant (k := m - k) (by omega) (by omega) _ (hinj s⁻¹ hm') h1' h3' ?_
        intro i j hi hj h
        rcases hsteps s⁻¹ hm' (Or.inr rfl) i j hi hj h with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
        · right; right
          have e2 : s⁻¹ ^ i = s⁻¹ ^ j * t⁻¹ := mul_left_cancel (e.trans (mul_assoc _ _ _))
          have h' : s⁻¹ ^ (i + (m - k)) = s⁻¹ ^ j := by
            rw [pow_add, ← ht', e2]; group
          have := pow_eq_pow_iff_modEq.mp h'
          rw [hm'] at this
          unfold Nat.ModEq at this
          rw [Nat.mod_eq_of_lt hj] at this
          exact this.symm
    · -- a chordless coset
      rw [hblock]
      refine elimOn_cycle hm4 _ (hinj s hm) ?_
      intro i j hi hj h
      rcases hsteps s hm (Or.inl rfl) i j hi hj h with e | e | e
      · exact Or.inl e
      · exact Or.inr e
      · exfalso
        apply htin
        have e2 : s ^ i = s ^ j * t⁻¹ := mul_left_cancel (e.trans (mul_assoc _ _ _))
        have : t = (s ^ i)⁻¹ * s ^ j := by rw [e2]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers s i))
          (Subgroup.npow_mem_zpowers s j)

/-- Storage codes on TT-free `Cay(G, {s, s⁻¹, t})` have `|C|² ≤ |α|^|G|`. -/
theorem card_sq_le_cayley {α : Type*} [Fintype α] [Nonempty α] {s t : G}
    (hS : ({s, s⁻¹, t} : Finset G).card = 3) (h1S : (1 : G) ∉ ({s, s⁻¹, t} : Finset G))
    (hTT : TTFree (cayN s t)) {C : Finset (G → α)} (hC : IsStorageCode (cayN s t) C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card G :=
  card_sq_le_of_rateBound_half (rateBound_cayley hS h1S hTT) hC

end HalfRate
