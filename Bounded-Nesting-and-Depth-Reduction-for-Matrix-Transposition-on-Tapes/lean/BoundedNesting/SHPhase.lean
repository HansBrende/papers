import BoundedNesting.SHBase

/-!
# Theorem SH: Phase E and the odd-state lemma

For a minimal counterexample `W` and runs from `v₀` (`St`), with bound `s` on the non-closed heavy
vertices:

* `OSAt M W v₀ s`: the conclusion of the odd-state lemma, no odd state `X ≠ W` with `|NC(X)| ≤ s`.
* `F1`: no early singles. `F2`: pair coincidence, with the end of its proof as the hypothesis
  `F2Mode` (from (S1), `F2Mode.of_S1`, or from `s ≤ 1`, `F2Mode.of_le_one`). `F3`: the final count,
  for a triple block of a vertex `h` from an odd set `Z`, whose members are light or of which at
  most one is heavy (`s ≤ 1`).
* `odd_state`: **the odd-state lemma**, `OSAt M W v₀ t` for every `t`, under (★4) and either at most
  two heavy vertices or (S1) and (S2).

Where the paper writes a row as a combination of the rows of a run, the proofs here use codewords:
a test vector at the move of `h` (`test_vec`) and the rows of the members of the block.
-/

namespace BoundedNesting

open Finset Module MotionDepthCodes

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

variable {M : Matrix V V F} {W : Finset V} {v₀ : V}

/-- The conclusion of the odd-state lemma at bound `s`. -/
def OSAt (M : Matrix V V F) (W : Finset V) (v₀ : V) (s : ℕ) : Prop :=
  ∀ X, St M W v₀ X → Odd X.card → X ≠ W → (NC M W X).card ≤ s → False

theorem OSAt.mono {s s' : ℕ} (h : OSAt M W v₀ s) (hs : s' ≤ s) : OSAt M W v₀ s' :=
  fun X hX ho hne hc => h X hX ho hne (hc.trans hs)

/-- The end of the pair-coincidence argument: two non-closed members of a pending set are not
both heavy. -/
def F2Mode (M : Matrix V V F) (W : Finset V) (v₀ : V) (s : ℕ) : Prop :=
  ∀ X u c c', St M W v₀ X → (NC M W X).card ≤ s → u ∈ X → c ∈ pend M W X u → c' ∈ pend M W X u →
    c ≠ c' → c ∈ NC M W X → c' ∈ NC M W X → False

theorem F2Mode.of_S1 {s : ℕ} (hS1 : S1On M W) : F2Mode M W v₀ s :=
  fun X u c c' hX _ hu hc hc' hcc hcN hc'N => hS1 u (hX.sub hu) c (pend_subset_rs X u hc) c'
    (pend_subset_rs X u hc') hcc (NC_subset hcN) (NC_subset hc'N)

theorem F2Mode.of_le_one {s : ℕ} (hs : s ≤ 1) : F2Mode M W v₀ s := by
  intro X u c c' _ hNC _ _ _ hcc hcN hc'N
  have : ({c, c'} : Finset V) ⊆ NC M W X := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hcN
    · exact hc'N
  have := card_le_card this
  rw [card_pair hcc] at this
  omega

omit [Fintype V] [DecidableEq V] [DecidableEq F] in
/-- Two rows with the same two live coordinates: the arithmetic of the last case of (F3). -/
theorem two_rows_zero {A₁ B₁ A₂ B₂ ya yb xa xb xt : F} (hya : ya ≠ 0) (hB₁ : B₁ ≠ 0)
    (e1 : A₁ * ya + B₁ * yb = 0) (e2 : A₂ * ya + B₂ * yb = 0) (e3 : A₁ * xa + B₁ * xb = 0)
    (e4 : xt + A₂ * xa + B₂ * xb = 0) : xt = 0 := by
  have hdet : xa * yb - xb * ya = 0 := by
    have : B₁ * (xa * yb - xb * ya) = 0 := by linear_combination xa * e1 - ya * e3
    exact (mul_eq_zero.mp this).resolve_left hB₁
  have h2 : ya * (A₂ * xa + B₂ * xb) = 0 := by linear_combination xa * e2 - B₂ * hdet
  have h3 : A₂ * xa + B₂ * xb = 0 := (mul_eq_zero.mp h2).resolve_left hya
  linear_combination e4 - h3

section Phase

variable (hW : MinCE M W) (hyp : ThmSHyp M)
include hW hyp

/-- **(F1) No early singles.** At an even state with at least three vertices outside, no vertex has
exactly one pending vertex. -/
theorem F1 {s : ℕ} (hOS : OSAt M W v₀ s) {X : Finset V} (hX : St M W v₀ X) (heven : Even X.card)
    (hY : 3 ≤ W.card - X.card) (hNC : (NC M W X).card ≤ s) {u : V} (hu : u ∈ X)
    (h1 : (pend M W X u).card = 1) : False := by
  obtain ⟨hX', -⟩ := hX.move hW hyp hu (Or.inr (Or.inl ⟨h1, heven⟩))
  have hcard : (X ∪ pend M W X u).card = X.card + 1 := by
    rw [card_union_of_disjoint (disjoint_pend X u), h1]
  refine hOS _ hX' ?_ ?_ ((card_le_card (NC_anti subset_union_left)).trans hNC)
  · rw [hcard]
    exact heven.add_one
  · intro he
    have := congrArg card he
    rw [hcard] at this
    omega

/-- **(F2) Pair coincidence.** At an even state with at least three vertices outside, any two
pending sets of size exactly two are equal. -/
theorem F2 {s : ℕ} (hOS : OSAt M W v₀ s) (hmode : F2Mode M W v₀ s) :
    ∀ n X, St M W v₀ X → Even X.card → W.card - X.card = n → 3 ≤ n → (NC M W X).card ≤ s →
      ∀ u₁ ∈ X, ∀ u₂ ∈ X, (pend M W X u₁).card = 2 → (pend M W X u₂).card = 2 →
        pend M W X u₁ = pend M W X u₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro X hX heven hn h3 hNC u₁ hu₁ u₂ hu₂ hq₁ hq₂
  by_contra hne
  have hq₁W : pend M W X u₁ ⊆ W \ X := fun v hv =>
    mem_sdiff.mpr ⟨pend_subset X u₁ hv, (mem_sdiff.mp hv).2⟩
  have hq₂W : pend M W X u₂ ⊆ W \ X := fun v hv =>
    mem_sdiff.mpr ⟨pend_subset X u₂ hv, (mem_sdiff.mp hv).2⟩
  have hY : (W \ X).card = n := by rw [card_sdiff_of_subset hX.sub]; omega
  have hinter : (pend M W X u₁ ∩ pend M W X u₂).card ≤ 1 := by
    by_contra h
    push Not at h
    have e1 : pend M W X u₁ ∩ pend M W X u₂ = pend M W X u₁ :=
      eq_of_subset_of_card_le inter_subset_left (by omega)
    have e2 : pend M W X u₁ ∩ pend M W X u₂ = pend M W X u₂ :=
      eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hne (e1.symm.trans e2)
  have hui := card_union_add_card_inter (pend M W X u₁) (pend M W X u₂)
  have hcW := card_le_card hX.sub
  obtain ⟨k, hk⟩ := hW.odd
  obtain ⟨a, ha⟩ := heven
  obtain ⟨hX₁, hdrop₁⟩ := hX.move hW hyp hu₁ (Or.inl hq₁)
  have hX₁card : (X ∪ pend M W X u₁).card = X.card + 2 := by
    rw [card_union_of_disjoint (disjoint_pend X u₁), hq₁]
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  · -- three vertices outside: the row of a common pending vertex
    have hunion : pend M W X u₁ ∪ pend M W X u₂ = W \ X :=
      eq_of_subset_of_card_le (union_subset hq₁W hq₂W) (by omega)
    obtain ⟨p, hp⟩ : (pend M W X u₁ ∩ pend M W X u₂).Nonempty := by
      rw [← card_pos]
      have := card_le_card (union_subset hq₁W hq₂W)
      omega
    obtain ⟨hp₁, hp₂⟩ := mem_inter.mp hp
    obtain ⟨q, hq, hqp⟩ := exists_mem_ne (show 1 < (pend M W X u₁).card by omega) p
    obtain ⟨x, hx, hxX, -, hxp⟩ := test_vec hyp hX.sub hu₁ hdrop₁ hp₁ hq (Ne.symm hqp)
    refine hxp (zero_of_rs hyp hx (pend_subset X u₁ hp₁) fun v hv => ?_)
    by_cases hvX : v ∈ X
    · exact hxX v hvX
    · exfalso
      have hvY : v ∈ W \ X := mem_sdiff.mpr ⟨rs_subset p hv, hvX⟩
      rw [← hunion] at hvY
      have hvp : v ∈ recSet M p := (mem_inter.mp hv).1
      rcases mem_union.mp hvY with hv1 | hv2
      · exact hyp.triangleFree u₁ p v (mem_inter.mp (pend_subset_rs X u₁ hp₁)).1
          (mem_inter.mp (pend_subset_rs X u₁ hv1)).1 hvp
      · exact hyp.triangleFree u₂ p v (mem_inter.mp (pend_subset_rs X u₂ hp₂)).1
          (mem_inter.mp (pend_subset_rs X u₂ hv2)).1 hvp
  · by_cases hmeet : (pend M W X u₁ ∩ pend M W X u₂).Nonempty
    · -- after the move of `u₁`, `u₂` has a single pending vertex
      have hpend : pend M W (X ∪ pend M W X u₁) u₂ = pend M W X u₂ \ pend M W X u₁ := by
        ext v
        simp only [pend, mem_sdiff, mem_union]
        tauto
      have hc : (pend M W X u₂ \ pend M W X u₁).card = 1 := by
        have := card_sdiff_add_card_inter (pend M W X u₂) (pend M W X u₁)
        rw [inter_comm] at this
        have := card_pos.mpr hmeet
        omega
      exact F1 hW hyp hOS hX₁ (by rw [hX₁card]; exact ⟨a + 1, by omega⟩) (by rw [hX₁card]; omega)
        ((card_le_card (NC_anti subset_union_left)).trans hNC) (mem_union_left _ hu₂)
        (by rw [hpend, hc])
    · have hdisj : Disjoint (pend M W X u₁) (pend M W X u₂) :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet)
      obtain ⟨hX₂, hdrop₂⟩ := hX.move hW hyp hu₂ (Or.inl hq₂)
      have hX₂card : (X ∪ pend M W X u₂).card = X.card + 2 := by
        rw [card_union_of_disjoint (disjoint_pend X u₂), hq₂]
      have hpend12 : pend M W (X ∪ pend M W X u₁) u₂ = pend M W X u₂ := by
        ext v
        simp only [pend, mem_sdiff, mem_union]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h2 (Or.inl h)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rintro (h | ⟨h3, h4⟩)
          · exact h2 h
          · exact disjoint_left.mp hdisj (mem_sdiff.mpr ⟨h3, h4⟩) (mem_sdiff.mpr ⟨h1, h2⟩)
      have hpend21 : pend M W (X ∪ pend M W X u₂) u₁ = pend M W X u₁ := by
        ext v
        simp only [pend, mem_sdiff, mem_union]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h2 (Or.inl h)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rintro (h | ⟨h3, h4⟩)
          · exact h2 h
          · exact disjoint_left.mp hdisj (mem_sdiff.mpr ⟨h1, h2⟩) (mem_sdiff.mpr ⟨h3, h4⟩)
      obtain ⟨hX₁₂, hdrop₁₂⟩ := hX₁.move hW hyp (mem_union_left _ hu₂)
        (Or.inl (by rw [hpend12]; exact hq₂))
      have hX₂even : Even (X ∪ pend M W X u₂).card := by rw [hX₂card]; exact ⟨a + 1, by omega⟩
      have hNC₂ : (NC M W (X ∪ pend M W X u₂)).card ≤ s :=
        (card_le_card (NC_anti subset_union_left)).trans hNC
      -- every member of the second pair is heavy and not closed
      have key : ∀ c ∈ pend M W X u₂, c ∈ NC M W X := by
        intro c hc
        have hne' := imm_closure hyp hX.sub hu₂ hdrop₂ (by omega) hc
        have hcX₂ : c ∈ X ∪ pend M W X u₂ := mem_union_right _ hc
        have hcv₀ : c ≠ v₀ := fun e => (mem_sdiff.mp hc).2 (e ▸ hX.mem)
        have hn1 : (pend M W (X ∪ pend M W X u₂) c).card ≠ 1 := fun h1 =>
          F1 hW hyp hOS hX₂ hX₂even (by rw [hX₂card]; omega) hNC₂ hcX₂ h1
        have hn2 : (pend M W (X ∪ pend M W X u₂) c).card ≠ 2 := by
          intro h2
          have heq := ihn (n - 2) (by omega) _ hX₂ hX₂even (by rw [hX₂card]; omega) (by omega) hNC₂
            c hcX₂ u₁ (mem_union_left _ hu₁) h2 (by rw [hpend21]; exact hq₁)
          rw [hpend21] at heq
          have hc' : c ∈ pend M W (X ∪ pend M W X u₁) u₂ := by rw [hpend12]; exact hc
          obtain ⟨v, hv⟩ := imm_closure hyp hX₁.sub (mem_union_left _ hu₂) hdrop₁₂
            (by rw [hpend12]; omega) hc'
          obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
          have hv3 : v ∈ pend M W (X ∪ pend M W X u₂) c := by
            refine mem_sdiff.mpr ⟨hv1, fun hvX => hv2 ?_⟩
            rcases mem_union.mp hvX with hvX | hvP
            · exact mem_union_left _ (mem_union_left _ hvX)
            · exact mem_union_right _ (by rw [hpend12]; exact hvP)
          rw [heq] at hv3
          exact hv2 (mem_union_left _ (mem_union_right _ hv3))
        have hheavy : c ∈ heavySet M W := by
          refine mem_filter.mpr ⟨pend_subset X u₂ hc, fun hl => ?_⟩
          have := hX₂.pend_light hcX₂ hcv₀ hl
          have := card_pos.mpr hne'
          omega
        exact NC_anti subset_union_left (mem_filter.mpr ⟨hheavy, Or.inr hne'⟩)
      obtain ⟨c, hc⟩ : (pend M W X u₂).Nonempty := by rw [← card_pos]; omega
      obtain ⟨c', hc', hcc⟩ := exists_mem_ne (show 1 < (pend M W X u₂).card by omega) c
      exact hmode X u₂ c c' hX hNC hu₂ hc hc' (Ne.symm hcc) (key c hc) (key c' hc')

omit hW in
/-- A row with two live coordinates `a ≠ b`. -/
theorem row_pair {x : V → F} (hx : x ∈ subCode M W) {v : V} (hv : v ∈ W) {a b : V}
    (ha : a ∈ rs M W v) (hb : b ∈ rs M W v) (hab : a ≠ b)
    (h0 : ∀ u ∈ rs M W v, u ≠ a → u ≠ b → x u = 0) : x v + M v a * x a + M v b * x b = 0 := by
  have hrow := row_rs hyp hx hv
  have hsum : ∑ u ∈ rs M W v, M v u * x u = ∑ u ∈ ({a, b} : Finset V), M v u * x u := by
    refine (sum_subset (fun u hu => ?_) fun u hu hu' => ?_).symm
    · simp only [mem_insert, mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact ha
      · exact hb
    · simp only [mem_insert, mem_singleton, not_or] at hu'
      rw [h0 u hu hu'.1 hu'.2, mul_zero]
  rw [hsum, sum_pair hab] at hrow
  linear_combination hrow

/-- **(F3) The final count.** Let `Z ⊆ W` be odd, `h ∈ Z` with three pending vertices `P` such that
the move `(h, P)` is neutral and reaches the state `X₀ = Z ∪ P`. If the members of `P` are light, or
`|NC(X₀)| ≤ s ≤ 1`, there is a contradiction. -/
theorem F3 {s : ℕ} (hOS : OSAt M W v₀ s) (hmode : F2Mode M W v₀ s) {Z : Finset V} (hZW : Z ⊆ W)
    (hZodd : Odd Z.card) {h : V} (hh : h ∈ Z) (hP3 : (pend M W Z h).card = 3)
    (hX₀ : St M W v₀ (Z ∪ pend M W Z h))
    (hdrop : cdim M W Z = ((pend M W Z h).card - 1) + cdim M W (Z ∪ pend M W Z h))
    (hv₀ : v₀ ∉ pend M W Z h) (hNC : (NC M W (Z ∪ pend M W Z h)).card ≤ s)
    (hP : (∀ t ∈ pend M W Z h, StarOn M W t) ∨ s ≤ 1) : False := by
  have hdisjZP : Disjoint Z (pend M W Z h) := disjoint_pend Z h
  have hX₀card : (Z ∪ pend M W Z h).card = Z.card + 3 := by
    rw [card_union_of_disjoint hdisjZP, hP3]
  obtain ⟨k, hk⟩ := hW.odd
  obtain ⟨z, hz⟩ := hZodd
  have hX₀even : Even (Z ∪ pend M W Z h).card := ⟨z + 2, by omega⟩
  have hcW := card_le_card hX₀.sub
  have hPW : pend M W Z h ⊆ W := pend_subset Z h
  have hnp : ∀ t ∈ pend M W Z h, ∀ t' ∈ pend M W Z h, t' ∉ recSet M t := fun t ht t' ht' =>
    hyp.triangleFree h t t' (mem_inter.mp (pend_subset_rs Z h ht)).1
      (mem_inter.mp (pend_subset_rs Z h ht')).1
  have hrsZ : ∀ t ∈ pend M W Z h, ∀ v ∈ rs M W t, v ∈ Z ∪ pend M W Z h → v ∈ Z := by
    intro t ht v hv hvX
    rcases mem_union.mp hvX with hvZ | hvP
    · exact hvZ
    · exact absurd (mem_inter.mp hv).1 (hnp t ht v hvP)
  have hIC : ∀ t ∈ pend M W Z h, (pend M W (Z ∪ pend M W Z h) t).Nonempty := fun t ht =>
    imm_closure hyp hZW hh hdrop (by omega) ht
  have hpX₀ : ∀ t ∈ pend M W Z h, t ∈ Z ∪ pend M W Z h := fun t ht => mem_union_right _ ht
  have htv₀ : ∀ t ∈ pend M W Z h, t ≠ v₀ := fun t ht e => hv₀ (e ▸ ht)
  -- the pending pairs of the light members
  have hpair : 3 ≤ W.card - (Z ∪ pend M W Z h).card → ∀ t ∈ pend M W Z h, StarOn M W t →
      (pend M W (Z ∪ pend M W Z h) t).card = 2 := by
    intro hY t ht hl
    have h1 := hX₀.pend_light (hpX₀ t ht) (htv₀ t ht) hl
    have h2 := card_pos.mpr (hIC t ht)
    have h3 : (pend M W (Z ∪ pend M W Z h) t).card ≠ 1 := fun h1 =>
      F1 hW hyp hOS hX₀ hX₀even hY hNC (hpX₀ t ht) h1
    omega
  obtain ⟨t₁, t₂, t₃, h12, h13, h23, hPeq⟩ := card_eq_three.mp hP3
  have ht₁ : t₁ ∈ pend M W Z h := by rw [hPeq]; simp
  have ht₂ : t₂ ∈ pend M W Z h := by rw [hPeq]; simp
  have ht₃ : t₃ ∈ pend M W Z h := by rw [hPeq]; simp
  rcases Nat.lt_or_ge (W.card - (Z ∪ pend M W Z h).card) 3 with hY1 | hY3
  · -- one vertex `w` outside: `t₁` and `t₂` point to it
    obtain ⟨w, hw⟩ := card_eq_one.mp (show (W \ (Z ∪ pend M W Z h)).card = 1 by
      rw [card_sdiff_of_subset hX₀.sub]; omega)
    have hpw : ∀ t ∈ pend M W Z h, ∀ v ∈ rs M W t, v ∉ Z → v = w := by
      intro t ht v hv hvZ
      have hvX : v ∉ Z ∪ pend M W Z h := fun hvX => hvZ (hrsZ t ht v hv hvX)
      have : v ∈ W \ (Z ∪ pend M W Z h) := mem_sdiff.mpr ⟨rs_subset t hv, hvX⟩
      rw [hw] at this
      exact mem_singleton.mp this
    have hwt₁ : w ∈ rs M W t₁ := by
      obtain ⟨v, hv⟩ := hIC t₁ ht₁
      have hvZ : v ∉ Z := fun hvZ => (mem_sdiff.mp hv).2 (mem_union_left _ hvZ)
      have := hpw t₁ ht₁ v (mem_sdiff.mp hv).1 hvZ
      rw [← this]
      exact (mem_sdiff.mp hv).1
    obtain ⟨x, hx, hxZ, hxP, hx2⟩ := test_vec hyp hZW hh hdrop ht₂ ht₃ h23
    have hx1 : x t₁ = 0 := hxP t₁ ht₁ h12 h13
    have hxw : x w = 0 := by
      refine zero_of_rs_but hyp hx (hPW ht₁) hwt₁ hx1 fun u hu huw => ?_
      by_contra hxu
      exact huw (hpw t₁ ht₁ u hu fun huZ => hxu (hxZ u huZ))
    refine hx2 (zero_of_rs hyp hx (hPW ht₂) fun u hu => ?_)
    by_cases huZ : u ∈ Z
    · exact hxZ u huZ
    · rw [hpw t₂ ht₂ u hu huZ]
      exact hxw
  · by_cases hlight : ∀ t ∈ pend M W Z h, StarOn M W t
    · -- all light: the Hall count
      have hp2 := fun t ht => hpair hY3 t ht (hlight t ht)
      have hsame : ∀ t ∈ pend M W Z h, pend M W (Z ∪ pend M W Z h) t =
          pend M W (Z ∪ pend M W Z h) t₁ := fun t ht =>
        F2 hW hyp hOS hmode _ _ hX₀ hX₀even rfl hY3 hNC t (hpX₀ t ht) t₁ (hpX₀ t₁ ht₁) (hp2 t ht)
          (hp2 t₁ ht₁)
      have hrs : ∀ t ∈ pend M W Z h, rs M W t ⊆ insert h (pend M W (Z ∪ pend M W Z h) t₁) := by
        intro t ht
        rw [← hsame t ht]
        rcases hlight t ht with hle2 | ⟨h3, hrec⟩
        · have heq : pend M W (Z ∪ pend M W Z h) t = rs M W t :=
            eq_of_subset_of_card_le (pend_subset_rs _ t) (by rw [hp2 t ht]; exact hle2)
          rw [heq]
          exact subset_insert _ _
        · have hht : h ∈ rs M W t := hrec h (hZW hh) (pend_subset_rs Z h ht)
          have hsub : insert h (pend M W (Z ∪ pend M W Z h) t) ⊆ rs M W t :=
            insert_subset hht (pend_subset_rs _ t)
          have hhn : h ∉ pend M W (Z ∪ pend M W Z h) t := fun hm =>
            (mem_sdiff.mp hm).2 (mem_union_left _ hh)
          have hcard : (insert h (pend M W (Z ∪ pend M W Z h) t)).card = 3 := by
            rw [card_insert_of_notMem hhn, hp2 t ht]
          exact (eq_of_subset_of_card_le hsub (by rw [hcard, h3])).symm.subset
      have hall := hW.hall_count hyp hPW ⟨t₁, ht₁⟩ hnp
      have hsub : pend M W Z h ∪ (pend M W Z h).biUnion (rs M W) ⊆
          pend M W Z h ∪ insert h (pend M W (Z ∪ pend M W Z h) t₁) :=
        union_subset_union le_rfl (biUnion_subset.mpr hrs)
      have h1 := card_le_card hsub
      have h2 := card_union_le (pend M W Z h) (insert h (pend M W (Z ∪ pend M W Z h) t₁))
      have h3 := card_insert_le h (pend M W (Z ∪ pend M W Z h) t₁)
      have h4 := hp2 t₁ ht₁
      omega
    · -- one heavy member `g`, the others light
      have hs1 : s ≤ 1 := hP.resolve_left hlight
      push Not at hlight
      obtain ⟨g, hgP, hgh⟩ := hlight
      have hgNC : g ∈ NC M W (Z ∪ pend M W Z h) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨hPW hgP, hgh⟩, Or.inr (hIC g hgP)⟩
      have honly : ∀ c ∈ NC M W (Z ∪ pend M W Z h), c = g := by
        intro c hc
        by_contra hcg
        have : ({c, g} : Finset V) ⊆ NC M W (Z ∪ pend M W Z h) := by
          intro v hv
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact hc
          · exact hgNC
        have := card_le_card this
        rw [card_pair hcg] at this
        omega
      have hlt : ∀ t ∈ pend M W Z h, t ≠ g → StarOn M W t := by
        intro t ht htg
        by_contra hth
        exact htg (honly t (mem_filter.mpr ⟨mem_filter.mpr ⟨hPW ht, hth⟩, Or.inr (hIC t ht)⟩))
      -- the two light members `u₁`, `u₂`
      obtain ⟨u₁, u₂, hu12, he⟩ := card_eq_two.mp (show ((pend M W Z h).erase g).card = 2 by
        rw [card_erase_of_mem hgP, hP3])
      have hu₁ : u₁ ∈ pend M W Z h := mem_of_mem_erase (by rw [he]; simp)
      have hu₂ : u₂ ∈ pend M W Z h := mem_of_mem_erase (by rw [he]; simp)
      have hu₁g : u₁ ≠ g := ne_of_mem_erase (by rw [he]; simp)
      have hu₂g : u₂ ≠ g := ne_of_mem_erase (by rw [he]; simp)
      have hp2₁ := hpair hY3 u₁ hu₁ (hlt u₁ hu₁ hu₁g)
      have hp2₂ := hpair hY3 u₂ hu₂ (hlt u₂ hu₂ hu₂g)
      have hsame := F2 hW hyp hOS hmode _ _ hX₀ hX₀even rfl hY3 hNC u₁ (hpX₀ u₁ hu₁) u₂
        (hpX₀ u₂ hu₂) hp2₁ hp2₂
      obtain ⟨a, b, hab, hpab⟩ := card_eq_two.mp hp2₁
      have ha : a ∈ pend M W (Z ∪ pend M W Z h) u₁ := by rw [hpab]; simp
      have hb : b ∈ pend M W (Z ∪ pend M W Z h) u₁ := by rw [hpab]; simp
      have ha₂ : a ∈ pend M W (Z ∪ pend M W Z h) u₂ := by rw [← hsame]; exact ha
      have hb₂ : b ∈ pend M W (Z ∪ pend M W Z h) u₂ := by rw [← hsame]; exact hb
      obtain ⟨hX₁, hdrop₁⟩ := hX₀.move hW hyp (hpX₀ u₁ hu₁) (Or.inl hp2₁)
      have hX₁card : (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁).card =
          (Z ∪ pend M W Z h).card + 2 := by
        rw [card_union_of_disjoint (disjoint_pend _ u₁), hp2₁]
      -- outside `X₀`, the rows of `u₁`, `u₂` live on `a`, `b`
      have hout : ∀ u ∈ ({u₁, u₂} : Finset V), ∀ v ∈ rs M W u, v ≠ a → v ≠ b →
          v ∈ Z := by
        intro u hu v hv hva hvb
        have hu' : u ∈ pend M W Z h := by
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hu₁
          · exact hu₂
        by_contra hvZ
        have hvX : v ∉ Z ∪ pend M W Z h := fun hvX => hvZ (hrsZ u hu' v hv hvX)
        have hvp : v ∈ pend M W (Z ∪ pend M W Z h) u := mem_sdiff.mpr ⟨hv, hvX⟩
        have hvp₁ : v ∈ pend M W (Z ∪ pend M W Z h) u₁ := by
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hvp
          · rw [hsame]
            exact hvp
        rw [hpab] at hvp₁
        simp only [mem_insert, mem_singleton] at hvp₁
        rcases hvp₁ with rfl | rfl
        · exact hva rfl
        · exact hvb rfl
      rcases Nat.lt_or_ge (W.card - (Z ∪ pend M W Z h).card) 5 with hY5 | hY5
      · -- three vertices outside: a codeword vanishing on `X₀`
        have hc1 : cdim M W (Z ∪ pend M W Z h) = 1 := by
          have := hX₀.good
          unfold Good at this
          omega
        have hc0 : cdim M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) = 0 := by
          have := hX₁.good
          unfold Good at this
          omega
        have hrowy : ∀ y ∈ subCode M W ⊓ zeroOn (Z ∪ pend M W Z h), ∀ u ∈ ({u₁, u₂} : Finset V),
            M u a * y a + M u b * y b = 0 := by
          rintro y ⟨hy, hyX⟩ u hu
          have hu' : u ∈ pend M W Z h := by
            simp only [mem_insert, mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact hu₁
            · exact hu₂
          have haU : a ∈ rs M W u := by
            simp only [mem_insert, mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact pend_subset_rs _ _ ha
            · exact pend_subset_rs _ _ ha₂
          have hbU : b ∈ rs M W u := by
            simp only [mem_insert, mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact pend_subset_rs _ _ hb
            · exact pend_subset_rs _ _ hb₂
          have := row_pair hyp hy (hPW hu') haU hbU hab fun v hv hva hvb =>
            hyX v (mem_union_left _ (hout u hu v hv hva hvb))
          rw [hyX u (hpX₀ u hu'), zero_add] at this
          exact this
        obtain ⟨y, hyC, hya⟩ : ∃ y ∈ subCode M W ⊓ zeroOn (Z ∪ pend M W Z h), y a ≠ 0 := by
          by_contra hno
          push Not at hno
          have hle : subCode M W ⊓ zeroOn (Z ∪ pend M W Z h) ≤
              subCode M W ⊓ zeroOn (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) := by
            intro y hyC
            refine ⟨hyC.1, fun v hv => ?_⟩
            rcases mem_union.mp hv with hv | hv
            · exact hyC.2 v hv
            · rw [hpab] at hv
              simp only [mem_insert, mem_singleton] at hv
              rcases hv with rfl | rfl
              · exact hno y hyC
              · have := hrowy y hyC u₁ (by simp)
                rw [hno y hyC, mul_zero, zero_add] at this
                exact (mul_eq_zero.mp this).resolve_left
                  (mem_recSet.mp (mem_inter.mp (pend_subset_rs _ _ hb)).1).2
          have := Submodule.finrank_mono hle
          unfold cdim at hc1 hc0
          omega
        obtain ⟨x, hx, hxZ, hxP, hx2⟩ := test_vec hyp hZW hh hdrop hu₂ hgP hu₂g
        have hx1 : x u₁ = 0 := hxP u₁ hu₁ hu12 hu₁g
        have e3 := row_pair hyp hx (hPW hu₁) (pend_subset_rs _ _ ha) (pend_subset_rs _ _ hb) hab
          fun v hv hva hvb => hxZ v (hout u₁ (by simp) v hv hva hvb)
        rw [hx1, zero_add] at e3
        have e4 := row_pair hyp hx (hPW hu₂) (pend_subset_rs _ _ ha₂) (pend_subset_rs _ _ hb₂) hab
          fun v hv hva hvb => hxZ v (hout u₂ (by simp) v hv hva hvb)
        exact hx2 (two_rows_zero hya (mem_recSet.mp (mem_inter.mp (pend_subset_rs _ _ hb)).1).2
          (hrowy y hyC u₁ (by simp)) (hrowy y hyC u₂ (by simp)) e3 e4)
      · -- five or more vertices outside: the pair `{a, b}` and the Hall count
        have hX₁even : Even (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁).card := by
          rw [hX₁card]
          exact ⟨z + 3, by omega⟩
        have hY₁ : 3 ≤ W.card - (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁).card := by
          rw [hX₁card]
          omega
        have hNC₁ : (NC M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁)).card ≤ s :=
          (card_le_card (NC_anti subset_union_left)).trans hNC
        have hcab : ∀ c ∈ pend M W (Z ∪ pend M W Z h) u₁, StarOn M W c ∧
            (pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) c).card = 2 := by
          intro c hc
          have hcX : c ∉ Z ∪ pend M W Z h := (mem_sdiff.mp hc).2
          have hcl : StarOn M W c := by
            by_contra hch
            have := honly c (mem_filter.mpr ⟨mem_filter.mpr ⟨pend_subset _ _ hc, hch⟩, Or.inl hcX⟩)
            exact hcX (this ▸ hpX₀ g hgP)
          refine ⟨hcl, ?_⟩
          have hcX₁ : c ∈ Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁ := mem_union_right _ hc
          have hcv₀ : c ≠ v₀ := fun e => hcX (e ▸ hX₀.mem)
          have h1 := hX₁.pend_light hcX₁ hcv₀ hcl
          have h2 := card_pos.mpr (imm_closure hyp hX₀.sub (hpX₀ u₁ hu₁) hdrop₁ (by omega) hc)
          have h3 : (pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) c).card ≠ 1 :=
            fun h1 => F1 hW hyp hOS hX₁ hX₁even hY₁ hNC₁ hcX₁ h1
          omega
        have hsame₂ := F2 hW hyp hOS hmode _ _ hX₁ hX₁even rfl hY₁ hNC₁ a (mem_union_right _ ha) b
          (mem_union_right _ hb) (hcab a ha).2 (hcab b hb).2
        -- the recovery sets of `a` and `b` are their common pending pair
        have hrsc : ∀ c ∈ pend M W (Z ∪ pend M W Z h) u₁, rs M W c =
            pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) a := by
          intro c hc
          have hc₂ : c ∈ pend M W (Z ∪ pend M W Z h) u₂ := by rw [← hsame]; exact hc
          have hpc : pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) c =
              pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) a := by
            rw [hpab] at hc
            simp only [mem_insert, mem_singleton] at hc
            rcases hc with rfl | rfl
            · rfl
            · exact hsame₂.symm
          rw [← hpc]
          rw [hpab] at hc
          have hc' : c ∈ pend M W (Z ∪ pend M W Z h) u₁ := by rw [hpab]; exact hc
          rcases (hcab c hc').1 with hle2 | ⟨h3, hrec⟩
          · exact (eq_of_subset_of_card_le (pend_subset_rs _ c)
              (by rw [(hcab c hc').2]; exact hle2)).symm
          · exfalso
            have hu₁c : u₁ ∈ rs M W c := hrec u₁ (hPW hu₁) (pend_subset_rs _ _ hc')
            have hu₂c : u₂ ∈ rs M W c := hrec u₂ (hPW hu₂) (pend_subset_rs _ _ hc₂)
            have hsub : insert u₁ (insert u₂
                (pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) c)) ⊆ rs M W c :=
              insert_subset hu₁c (insert_subset hu₂c (pend_subset_rs _ c))
            have hX₁u : ∀ u ∈ pend M W Z h, u ∉
                pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) c :=
              fun u hu hm => (mem_sdiff.mp hm).2 (mem_union_left _ (hpX₀ u hu))
            have hcard : (insert u₁ (insert u₂
                (pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) c))).card = 4 := by
              rw [card_insert_of_notMem, card_insert_of_notMem (hX₁u u₂ hu₂), (hcab c hc').2]
              simp only [mem_insert, not_or]
              exact ⟨hu12, hX₁u u₁ hu₁⟩
            have := card_le_card hsub
            omega
        have hall := hW.hall_count hyp (show ({a, b} : Finset V) ⊆ W by
            intro v hv
            simp only [mem_insert, mem_singleton] at hv
            rcases hv with rfl | rfl
            · exact pend_subset _ _ ha
            · exact pend_subset _ _ hb) ⟨a, by simp⟩ (by
            intro v hv v' hv'
            simp only [mem_insert, mem_singleton] at hv hv'
            have hva : ∀ c ∈ ({a, b} : Finset V), c ∈ recSet M u₁ := by
              intro c hc
              simp only [mem_insert, mem_singleton] at hc
              rcases hc with rfl | rfl
              · exact (mem_inter.mp (pend_subset_rs _ _ ha)).1
              · exact (mem_inter.mp (pend_subset_rs _ _ hb)).1
            rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
            · exact fun hm => (mem_recSet.mp hm).1 rfl
            · exact hyp.triangleFree u₁ v v' (hva v (by simp)) (hva v' (by simp))
            · exact hyp.triangleFree u₁ v v' (hva v (by simp)) (hva v' (by simp))
            · exact fun hm => (mem_recSet.mp hm).1 rfl)
        have hsub : ({a, b} : Finset V) ∪ ({a, b} : Finset V).biUnion (rs M W) ⊆
            {a, b} ∪ pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) a := by
          refine union_subset_union le_rfl (biUnion_subset.mpr fun c hc => ?_)
          rw [hrsc c (by
            simp only [mem_insert, mem_singleton] at hc
            rcases hc with rfl | rfl
            · exact ha
            · exact hb)]
        have h1 := card_le_card hsub
        have h2 := card_union_le ({a, b} : Finset V)
          (pend M W (Z ∪ pend M W Z h ∪ pend M W (Z ∪ pend M W Z h) u₁) a)
        rw [card_pair hab, (hcab a ha).2] at h2
        rw [card_pair hab] at hall
        omega

/-- **The odd-state lemma.** Under (★4), and at most two heavy vertices or (S1) and (S2), no neutral
run with at least one move reaches an odd good state other than `W`. -/
theorem odd_state (h4 : ∀ v ∈ W, Star4On M W v)
    (hmode : (heavySet M W).card ≤ 2 ∨ (S1On M W ∧ S2On M W)) : ∀ t, OSAt M W v₀ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
  suffices hsuf : ∀ n X, St M W v₀ X → Odd X.card → X ≠ W → W.card - X.card = n →
      (NC M W X).card ≤ t → False from fun X hX ho hne hc => hsuf _ X hX ho hne rfl hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro X hX hodd hne hn hNC
  have hXW := hX.sub
  have hcW : X.card < W.card := card_lt_card (ssubset_of_subset_of_ne hXW hne)
  obtain ⟨k, hk⟩ := hW.odd
  obtain ⟨a, ha⟩ := hodd
  -- (O1)
  by_cases hO1 : ∃ u ∈ X, (pend M W X u).card = 1
  · obtain ⟨u, hu, h1⟩ := hO1
    exact hW.single_odd_false hyp hXW hX.good hu h1 ⟨a, ha⟩
  push Not at hO1
  -- (O2), (O3)
  by_cases hO2 : ∃ u ∈ X, (pend M W X u).card = 2
  · obtain ⟨u, hu, h2⟩ := hO2
    obtain ⟨hX', hdrop⟩ := hX.move hW hyp hu (Or.inl h2)
    have hX'card : (X ∪ pend M W X u).card = X.card + 2 := by
      rw [card_union_of_disjoint (disjoint_pend X u), h2]
    have hX'odd : Odd (X ∪ pend M W X u).card := ⟨a + 1, by omega⟩
    by_cases hW' : X ∪ pend M W X u = W
    · obtain ⟨w, hw⟩ : (pend M W X u).Nonempty := by rw [← card_pos]; omega
      obtain ⟨v, hv⟩ := imm_closure hyp hXW hu hdrop (by omega) hw
      rw [hW'] at hv
      exact (mem_sdiff.mp hv).2 (rs_subset w (mem_sdiff.mp hv).1)
    by_cases hlight : StarOn M W u
    · exact ihn _ (by omega) _ hX' hX'odd hW' rfl
        ((card_le_card (NC_anti subset_union_left)).trans hNC)
    · have huNC : u ∈ NC M W X :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨hXW hu, hlight⟩, Or.inr (by rw [← card_pos]; omega)⟩
      have hsub : NC M W (X ∪ pend M W X u) ⊆ (NC M W X).erase u := by
        intro g hg
        refine mem_erase.mpr ⟨?_, NC_anti subset_union_left hg⟩
        rintro rfl
        obtain ⟨-, hg'⟩ := mem_filter.mp hg
        rcases hg' with hg' | ⟨v, hv⟩
        · exact hg' (mem_union_left _ hu)
        · obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
          exact hv2 (mem_union_right _ (mem_sdiff.mpr ⟨hv1, fun hvX => hv2 (mem_union_left _ hvX)⟩))
      have hc := card_le_card hsub
      rw [card_erase_of_mem huNC] at hc
      have hpos := card_pos.mpr ⟨u, huNC⟩
      exact IH (t - 1) (by omega) _ hX' hX'odd hW' (by omega)
  push Not at hO2
  -- (O4): a heavy vertex with a pending triple
  obtain ⟨h, hhX, hhout⟩ : ∃ h ∈ X, ¬ rs M W h ⊆ X := by
    have := (hW.out_card hXW hX.nonempty hne).2 ⟨a, ha⟩
    obtain ⟨h, hh⟩ := card_pos.mp (show 0 < (X.filter fun v => ¬ rs M W v ⊆ X).card by omega)
    exact ⟨h, (mem_filter.mp hh).1, (mem_filter.mp hh).2⟩
  have hpne : (pend M W X h).Nonempty := by
    obtain ⟨v, hv, hvX⟩ := not_subset.mp hhout
    exact ⟨v, mem_sdiff.mpr ⟨hv, hvX⟩⟩
  have hhv₀ : h ≠ v₀ := by
    rintro rfl
    rw [hX.pend_start] at hpne
    exact not_nonempty_empty hpne
  have hp0 := card_pos.mpr hpne
  have hheavy : ¬ StarOn M W h := fun hl => by
    have := hX.pend_light hhX hhv₀ hl
    have := hO1 h hhX
    have := hO2 h hhX
    omega
  have hP3 : (pend M W X h).card = 3 := by
    have := hX.pend_le_three hhX hhv₀ (h4 h (hXW hhX))
    have := hO1 h hhX
    have := hO2 h hhX
    omega
  -- Phase E
  obtain ⟨hX₀, hdropE⟩ := hX.move hW hyp hhX (Or.inr (Or.inr ⟨hP3, ⟨a, ha⟩⟩))
  have hhNC : h ∈ NC M W X := mem_filter.mpr ⟨mem_filter.mpr ⟨hXW hhX, hheavy⟩, Or.inr hpne⟩
  have hsub : NC M W (X ∪ pend M W X h) ⊆ (NC M W X).erase h := by
    intro g hg
    refine mem_erase.mpr ⟨?_, NC_anti subset_union_left hg⟩
    rintro rfl
    obtain ⟨-, hg'⟩ := mem_filter.mp hg
    rcases hg' with hg' | ⟨v, hv⟩
    · exact hg' (mem_union_left _ hhX)
    · obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
      exact hv2 (mem_union_right _ (mem_sdiff.mpr ⟨hv1, fun hvX => hv2 (mem_union_left _ hvX)⟩))
  have hc := card_le_card hsub
  rw [card_erase_of_mem hhNC] at hc
  have hpos := card_pos.mpr ⟨h, hhNC⟩
  have hOS : OSAt M W v₀ (NC M W (X ∪ pend M W X h)).card :=
    fun X' hX' ho hne' hc' => IH (t - 1) (by omega) X' hX' ho hne' (by omega)
  refine F3 hW hyp hOS ?_ hXW ⟨a, ha⟩ hhX hP3 hX₀ hdropE
    (fun hv => (mem_sdiff.mp hv).2 hX.mem) le_rfl ?_
  · rcases hmode with hfew | ⟨hS1, -⟩
    · refine F2Mode.of_le_one ?_
      have := card_le_card (NC_subset (M := M) (W := W) (X := X))
      omega
    · exact F2Mode.of_S1 hS1
  · rcases hmode with hfew | ⟨-, hS2⟩
    · right
      have := card_le_card (NC_subset (M := M) (W := W) (X := X))
      omega
    · left
      intro t' ht'
      by_contra hl
      exact hS2 h (mem_filter.mpr ⟨hXW hhX, hheavy⟩) t' (pend_subset_rs X h ht')
        (mem_filter.mpr ⟨pend_subset X h ht', hl⟩)

end Phase

end BoundedNesting
