import BoundedNesting.TheoremSH

/-!
# Theorem SH*: sparse heavy vertices under `(S1)` alone

Paper 8 (`BoundedNesting.TheoremSH`) proved the half-rate kernel bound `dim ker M ≤ ⌊N/2⌋` for
triangle-free unit-diagonal matrices satisfying `(★4)` whose heavy vertices `H` either satisfy
`|H| ≤ 2` or satisfy both `(S1)` (no vertex has two heavy recovery neighbours) and `(S2)` (no
heavy vertex has a heavy recovery neighbour).

Here we eliminate `(S2)` completely:

* `SHStarOn M W`: `(★4)` on `W`, together with `(heavySet M W).card ≤ 2 ∨ S1On M W`.
* `F3_star`: in Phase E, when a pending triple `P = pend M W Z h` has at most one heavy member
  `g` (automatic under `S1On M W`, without needing `S2On`), the two light members `u₁, u₂` share
  their pending pair `{a, b}` by `F2`, and the neutral move drop
  `cdim M W X₀ = 1 + cdim M W (X₀ ∪ {a, b})` directly yields a codeword `y` vanishing on `X₀`
  with `y a ≠ 0` for *every* `|W \ X₀| ≥ 3` (avoiding the `< 5` vs. `≥ 5` split of `SHPhase.F3`).
* `MinCE.false_SHStar`: in Case 3, any `h ∈ heavySet M W` has `|rs M W h| = 4` and at most one
  heavy recovery neighbour by `S1On M W`, hence at least three light recovery neighbours `v₀`.
* `theoremSHStar`, `theoremSHStar_transpose`, `theoremSHStar_graph`: **Theorem SH*** in matrix,
  transpose, and graph forms (`NoCommonNbhd` in place of `Far3`).
* `finrank_ker_le_barrier_SHStar`, `finrank_ker_add_card_le_matching_SHStar`,
  `finrank_ker_le_matching_rhoMatch`, and `rho3_le_rhoMatch`: **Corollary SH*** with the
  adjacent-pair matching packing invariant `rhoMatch G H ≥ rho3 G H`.
-/

namespace DirectedReciprocity

open Finset Module MotionDepthCodes BoundedNesting

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

/-! ### Strengthened relative hypotheses and heredity -/

/-- The hypotheses of Theorem SH* on `W`: `(★4)` everywhere, and either at most two heavy
vertices or `(S1)` alone. -/
def SHStarOn (M : Matrix V V F) (W : Finset V) : Prop :=
  (∀ v ∈ W, Star4On M W v) ∧ ((heavySet M W).card ≤ 2 ∨ S1On M W)

theorem SHStarOn.mono {M : Matrix V V F} {W W' : Finset V} (h : W' ⊆ W) (hs : SHStarOn M W) :
    SHStarOn M W' := by
  refine ⟨fun v hv => (hs.1 v (h hv)).mono h, ?_⟩
  rcases hs.2 with hc | h1
  · exact Or.inl ((card_le_card (heavySet_mono h)).trans hc)
  · refine Or.inr fun v hv p hp q hq hpq hph hqh =>
      h1 v (h hv) p (rs_mono h v hp) q (rs_mono h v hq) hpq (heavySet_mono h hph)
        (heavySet_mono h hqh)

/-! ### Phase E and the odd-state lemma without `(S2)` -/

section PhaseStar

variable {M : Matrix V V F} {W : Finset V} {v₀ : V}
variable (hW : MinCE M W) (hyp : ThmSHyp M)
include hW hyp

/-- **(F3*) Unified final count.** If at most one member of the pending triple `pend M W Z h`
violates `StarOn M W`, Phase E reaches a contradiction for all `|W \ X₀|` without splitting at `5`. -/
theorem F3_star {s : ℕ} (hOS : OSAt M W v₀ s) (hmode : F2Mode M W v₀ s) {Z : Finset V}
    (hZW : Z ⊆ W) (hZodd : Odd Z.card) {h : V} (hh : h ∈ Z) (hP3 : (pend M W Z h).card = 3)
    (hX₀ : St M W v₀ (Z ∪ pend M W Z h))
    (hdrop : cdim M W Z = ((pend M W Z h).card - 1) + cdim M W (Z ∪ pend M W Z h))
    (hv₀ : v₀ ∉ pend M W Z h) (hNC : (NC M W (Z ∪ pend M W Z h)).card ≤ s)
    (hP : ∀ t ∈ pend M W Z h, ¬ StarOn M W t → ∀ t' ∈ pend M W Z h, ¬ StarOn M W t' → t = t') :
    False := by
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
  · -- one vertex `w` outside
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
    · -- all three members light: Hall count
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
    · -- one heavy member `g`, two light members `u₁, u₂`: unified kernel drop for all `|W \ X₀| ≥ 3`
      push Not at hlight
      obtain ⟨g, hgP, hgh⟩ := hlight
      have hlt : ∀ t ∈ pend M W Z h, t ≠ g → StarOn M W t := by
        intro t ht htg
        by_contra hth
        exact htg (hP t ht hth g hgP hgh)
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
      obtain ⟨_, hdrop₁⟩ := hX₀.move hW hyp (hpX₀ u₁ hu₁) (Or.inl hp2₁)
      have hout : ∀ u ∈ ({u₁, u₂} : Finset V), ∀ v ∈ rs M W u, v ≠ a → v ≠ b → v ∈ Z := by
        intro u hu v hv hva hvb
        have hu' : u ∈ pend M W Z h := by
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption
        by_contra hvZ
        have hvX : v ∉ Z ∪ pend M W Z h := fun hvX => hvZ (hrsZ u hu' v hv hvX)
        have hvp : v ∈ pend M W (Z ∪ pend M W Z h) u := mem_sdiff.mpr ⟨hv, hvX⟩
        have hvp₁ : v ∈ pend M W (Z ∪ pend M W Z h) u₁ := by
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hvp
          · rwa [hsame]
        rw [hpab] at hvp₁
        simp only [mem_insert, mem_singleton] at hvp₁
        rcases hvp₁ with rfl | rfl
        · exact hva rfl
        · exact hvb rfl
      have hrowy : ∀ y ∈ subCode M W ⊓ zeroOn (Z ∪ pend M W Z h), ∀ u ∈ ({u₁, u₂} : Finset V),
          M u a * y a + M u b * y b = 0 := by
        rintro y ⟨hy, hyX⟩ u hu
        have hu' : u ∈ pend M W Z h := by
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption
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
        have hmono := Submodule.finrank_mono hle
        rw [hp2₁] at hdrop₁
        unfold cdim at hdrop₁
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

/-- **The odd-state lemma without `(S2)`.** Under `(★4)` and either at most two heavy vertices or
`(S1)` alone, no neutral run with at least one move reaches an odd good state other than `W`. -/
theorem odd_state_star (h4 : ∀ v ∈ W, Star4On M W v)
    (hmode : (heavySet M W).card ≤ 2 ∨ S1On M W) : ∀ t, OSAt M W v₀ t := by
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
  by_cases hO1 : ∃ u ∈ X, (pend M W X u).card = 1
  · obtain ⟨u, hu, h1⟩ := hO1
    exact hW.single_odd_false hyp hXW hX.good hu h1 ⟨a, ha⟩
  push Not at hO1
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
  refine F3_star hW hyp hOS ?_ hXW ⟨a, ha⟩ hhX hP3 hX₀ hdropE
    (fun hv => (mem_sdiff.mp hv).2 hX.mem) le_rfl ?_
  · rcases hmode with hfew | hS1
    · refine F2Mode.of_le_one ?_
      have := card_le_card (NC_subset (M := M) (W := W) (X := X))
      omega
    · exact F2Mode.of_S1 hS1
  · intro t₁ ht₁ hnh₁ t₂ ht₂ hnh₂
    rcases hmode with hfew | hS1
    · by_contra hne12
      have hIC₁ := imm_closure hyp hXW hhX hdropE (by omega) ht₁
      have hIC₂ := imm_closure hyp hXW hhX hdropE (by omega) ht₂
      have ht₁NC : t₁ ∈ NC M W (X ∪ pend M W X h) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨pend_subset X h ht₁, hnh₁⟩, Or.inr hIC₁⟩
      have ht₂NC : t₂ ∈ NC M W (X ∪ pend M W X h) :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨pend_subset X h ht₂, hnh₂⟩, Or.inr hIC₂⟩
      have hpairNC : ({t₁, t₂} : Finset V) ⊆ NC M W (X ∪ pend M W X h) := by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
      have hle2 := card_le_card hpairNC
      rw [card_pair hne12] at hle2
      have := card_le_card (NC_subset (M := M) (W := W) (X := X))
      omega
    · by_contra hne12
      exact hS1 h (hXW hhX) t₁ (pend_subset_rs X h ht₁) t₂ (pend_subset_rs X h ht₂) hne12
        (mem_filter.mpr ⟨pend_subset X h ht₁, hnh₁⟩) (mem_filter.mpr ⟨pend_subset X h ht₂, hnh₂⟩)

end PhaseStar

/-! ### Minimal counterexample exclusion and hereditary half bound -/

section StartStar

variable {M : Matrix V V F} {W : Finset V}

/-- A minimal counterexample on which `SHStarOn` holds is impossible. -/
theorem MinCE.false_SHStar (hW : MinCE M W) (hyp : ThmSHyp M) (hSH : SHStarOn M W) : False := by
  obtain ⟨h4, hmode⟩ := hSH
  obtain ⟨k, hk⟩ := hW.odd
  have hOS : ∀ v₀ t, OSAt M W v₀ t := fun v₀ => odd_state_star hW hyp h4 hmode
  have h2 : ∀ v ∈ W, 2 ≤ (rs M W v).card := fun v hv => hW.two_le_rs hyp hv
  -- Case 1: a vertex with two recovery neighbours
  by_cases hC1 : ∃ v₀ ∈ W, (rs M W v₀).card = 2
  · obtain ⟨v₀, hv₀, hc⟩ := hC1
    obtain ⟨hX₀, hpend, hdrop⟩ := St.first hW hyp hv₀ (Or.inl hc)
    have hcard : (insert v₀ (rs M W v₀)).card = 3 := by
      rw [card_insert_of_notMem (not_mem_rs v₀), hc]
    by_cases hWeq : insert v₀ (rs M W v₀) = W
    · obtain ⟨w, hw⟩ : (rs M W v₀).Nonempty := by rw [← card_pos]; omega
      have hw' : w ∈ pend M W {v₀} v₀ := by rw [hpend]; exact hw
      have hdrop' : cdim M W {v₀} =
          ((pend M W {v₀} v₀).card - 1) + cdim M W ({v₀} ∪ pend M W {v₀} v₀) := by
        rw [hpend, ← insert_eq]
        exact hdrop
      obtain ⟨v, hv⟩ := imm_closure hyp (singleton_subset_iff.mpr hv₀) (mem_singleton_self v₀) hdrop'
        (by rw [hpend, hc]) hw'
      rw [hpend, ← insert_eq, hWeq] at hv
      exact (mem_sdiff.mp hv).2 (rs_subset w (mem_sdiff.mp hv).1)
    · exact hOS v₀ (heavySet M W).card _ hX₀ (by rw [hcard]; decide) hWeq
        (card_le_card NC_subset)
  push Not at hC1
  -- Case 2: a heavy vertex with three recovery neighbours
  by_cases hC2 : ∃ h ∈ W, ¬ StarOn M W h ∧ (rs M W h).card = 3
  · obtain ⟨h, hhW, hheavy, hc⟩ := hC2
    obtain ⟨hX₀, hpend, hdrop⟩ := St.first hW hyp hhW (Or.inr hc)
    have hins : ({h} : Finset V) ∪ pend M W {h} h = insert h (rs M W h) := by
      rw [hpend, ← insert_eq]
    have hhNC : NC M W (insert h (rs M W h)) ⊆ (heavySet M W).erase h := by
      intro g hg
      refine mem_erase.mpr ⟨?_, NC_subset hg⟩
      rintro rfl
      obtain ⟨-, hg'⟩ := mem_filter.mp hg
      rcases hg' with hg' | ⟨v, hv⟩
      · exact hg' (mem_insert_self _ _)
      · exact (mem_sdiff.mp hv).2 (mem_insert_of_mem (mem_sdiff.mp hv).1)
    have hhH : h ∈ heavySet M W := mem_filter.mpr ⟨hhW, hheavy⟩
    have hcNC := card_le_card hhNC
    rw [card_erase_of_mem hhH] at hcNC
    have hdrop0 : cdim M W {h} =
        ((pend M W {h} h).card - 1) + cdim M W ({h} ∪ pend M W {h} h) := by
      rw [hpend, ← insert_eq]
      exact hdrop
    refine F3_star hW hyp (hOS h (NC M W ({h} ∪ pend M W {h} h)).card) ?_
      (singleton_subset_iff.mpr hhW) (by simp) (mem_singleton_self h) (by rw [hpend, hc])
      (by rw [hins]; exact hX₀) hdrop0 (by rw [hpend]; exact not_mem_rs h) le_rfl ?_
    · rcases hmode with hfew | hS1
      · exact F2Mode.of_le_one (by rw [hins]; omega)
      · exact F2Mode.of_S1 hS1
    · intro t₁ ht₁ hnh₁ t₂ ht₂ hnh₂
      rcases hmode with hfew | hS1
      · by_contra hne12
        have hIC₁ := imm_closure hyp (singleton_subset_iff.mpr hhW) (mem_singleton_self h) hdrop0
          (by rw [hpend, hc]; omega) ht₁
        have hIC₂ := imm_closure hyp (singleton_subset_iff.mpr hhW) (mem_singleton_self h) hdrop0
          (by rw [hpend, hc]; omega) ht₂
        have ht₁NC : t₁ ∈ NC M W ({h} ∪ pend M W {h} h) :=
          mem_filter.mpr ⟨mem_filter.mpr ⟨pend_subset {h} h ht₁, hnh₁⟩, Or.inr hIC₁⟩
        have ht₂NC : t₂ ∈ NC M W ({h} ∪ pend M W {h} h) :=
          mem_filter.mpr ⟨mem_filter.mpr ⟨pend_subset {h} h ht₂, hnh₂⟩, Or.inr hIC₂⟩
        have hpairNC : ({t₁, t₂} : Finset V) ⊆ NC M W ({h} ∪ pend M W {h} h) := by
          intro v hv
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption
        have hle2 := card_le_card hpairNC
        rw [card_pair hne12, hins] at hle2
        omega
      · by_contra hne12
        exact hS1 h hhW t₁ (pend_subset_rs {h} h ht₁) t₂ (pend_subset_rs {h} h ht₂) hne12
          (mem_filter.mpr ⟨pend_subset {h} h ht₁, hnh₁⟩)
          (mem_filter.mpr ⟨pend_subset {h} h ht₂, hnh₂⟩)
  push Not at hC2
  -- Case 3: light vertices have three recovery neighbours, heavy ones four, all reciprocal
  have hdeg : ∀ v ∈ W, (StarOn M W v ∧ (rs M W v).card = 3) ∨
      (¬ StarOn M W v ∧ (rs M W v).card = 4) := by
    intro v hv
    have := h2 v hv
    have := hC1 v hv
    by_cases hl : StarOn M W v
    · left
      refine ⟨hl, ?_⟩
      rcases hl with hle | ⟨h3, -⟩ <;> omega
    · right
      refine ⟨hl, ?_⟩
      have h3 := hC2 v hv hl
      rcases h4 v hv with hle | ⟨h4', -⟩
      · exfalso
        exact hl (Or.inl (by omega))
      · exact h4'
  have hrecip : ∀ v ∈ W, ∀ r ∈ W, v ∈ rs M W r → r ∈ rs M W v := by
    intro v hv r hr hvr
    rcases hdeg v hv with ⟨hl, h3⟩ | ⟨hl, h4'⟩
    · rcases hl with hle | ⟨-, hrec⟩
      · omega
      · exact hrec r hr hvr
    · rcases h4 v hv with hle | ⟨-, hrec⟩
      · omega
      · exact hrec r hr hvr
  have hHodd : Odd (heavySet M W).card := by
    let G : SimpleGraph W :=
      { Adj := fun a b => (b : V) ∈ rs M W a
        symm := ⟨fun a b hab => hrecip b b.2 a a.2 hab⟩
        loopless := ⟨fun a ha => not_mem_rs (a : V) ha⟩ }
    have hdegG : ∀ a : W, G.degree a = (rs M W a).card := by
      intro a
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter (G := G)]
      have hmap : (univ.filter (G.Adj a)).map (Function.Embedding.subtype (· ∈ W)) = rs M W a := by
        ext u
        simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, G]
        constructor
        · rintro ⟨b, hb, rfl⟩; exact hb
        · intro hu; exact ⟨⟨u, rs_subset _ hu⟩, hu, rfl⟩
      rw [← card_map, hmap]
    have heven := G.even_card_odd_degree_vertices
    have hmapF : (univ.filter fun a : W => Odd (G.degree a)).map (Function.Embedding.subtype (· ∈ W)) =
        W.filter fun v => StarOn M W v := by
      ext u
      simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨b.2, ?_⟩
        rw [hdegG] at hb
        rcases hdeg b b.2 with ⟨hl, -⟩ | ⟨-, h4'⟩
        · exact hl
        · rw [h4'] at hb; exact absurd hb (by decide)
      · rintro ⟨huW, hl⟩
        refine ⟨⟨u, huW⟩, ?_, rfl⟩
        rw [hdegG]
        rcases hdeg u huW with ⟨-, h3⟩ | ⟨hl', -⟩
        · rw [h3]; decide
        · exact absurd hl hl'
    rw [← card_map, hmapF] at heven
    have hsplit := card_filter_add_card_filter_not (s := W) (fun v => StarOn M W v)
    obtain ⟨e, he⟩ := heven
    exact ⟨k - e, by unfold heavySet; omega⟩
  have hS1 : S1On M W := by
    rcases hmode with hfew | hS1
    · have h1 : (heavySet M W).card = 1 := by
        obtain ⟨j, hj⟩ := hHodd
        omega
      obtain ⟨g, hg⟩ := card_eq_one.mp h1
      intro v _ p _ q _ hpq hp hq
      rw [hg] at hp hq
      exact hpq ((mem_singleton.mp hp).trans (mem_singleton.mp hq).symm)
    · exact hS1
  obtain ⟨h, hhH⟩ : (heavySet M W).Nonempty := by
    rw [← card_pos]
    obtain ⟨j, hj⟩ := hHodd
    omega
  obtain ⟨hhW, hheavy⟩ := mem_filter.mp hhH
  have hh4 : (rs M W h).card = 4 := by
    rcases hdeg h hhW with ⟨hl, -⟩ | ⟨-, h4'⟩
    · exact absurd hl hheavy
    · exact h4'
  -- Under `S1On M W` alone, `h` has at most one heavy neighbour among its four neighbours,
  -- hence at least three light neighbours!
  obtain ⟨v₀, hv₀, hv₀l⟩ : ∃ v₀ ∈ rs M W h, StarOn M W v₀ := by
    by_contra hno
    push Not at hno
    obtain ⟨p, hp⟩ : (rs M W h).Nonempty := by rw [← card_pos]; omega
    obtain ⟨q, hq, hqp⟩ := exists_mem_ne (show 1 < (rs M W h).card by omega) p
    exact hS1 h hhW p hp q hq (Ne.symm hqp)
      (mem_filter.mpr ⟨rs_subset h hp, hno p hp⟩)
      (mem_filter.mpr ⟨rs_subset h hq, hno q hq⟩)
  have hv₀W : v₀ ∈ W := rs_subset h hv₀
  have hv₀3 : (rs M W v₀).card = 3 := by
    rcases hdeg v₀ hv₀W with ⟨-, h3⟩ | ⟨hl, -⟩
    · exact h3
    · exact absurd hv₀l hl
  have hhv₀ : h ∈ rs M W v₀ := hrecip v₀ hv₀W h hhW hv₀
  obtain ⟨s₁, s₂, hs12, hse⟩ := card_eq_two.mp (show ((rs M W v₀).erase h).card = 2 by
    rw [card_erase_of_mem hhv₀, hv₀3])
  have hs₁ : s₁ ∈ rs M W v₀ := mem_of_mem_erase (by rw [hse]; simp)
  have hs₂ : s₂ ∈ rs M W v₀ := mem_of_mem_erase (by rw [hse]; simp)
  have hs₁h : s₁ ≠ h := ne_of_mem_erase (by rw [hse]; simp)
  have hs₂h : s₂ ≠ h := ne_of_mem_erase (by rw [hse]; simp)
  have hlight : ∀ s ∈ rs M W v₀, s ≠ h → StarOn M W s := by
    intro s hs hsh
    by_contra hl
    exact hS1 v₀ hv₀W h hhv₀ s hs (Ne.symm hsh) hhH (mem_filter.mpr ⟨rs_subset v₀ hs, hl⟩)
  have hrec : ∀ a ∈ W, ∀ b ∈ W, a ∈ rs M W b → (b : V) ∈ rs M W a := fun a ha b hb hab =>
    hrecip a ha b hb hab
  have htri : ∀ p ∈ rs M W v₀, ∀ q ∈ rs M W v₀, q ∉ rs M W p := fun p hp q hq hqp =>
    hyp.triangleFree v₀ p q (mem_inter.mp hp).1 (mem_inter.mp hq).1 (mem_inter.mp hqp).1
  have hsub7 : insert h (rs M W h) ∪ {s₁, s₂} ⊆ W := by
    refine union_subset (insert_subset hhW (rs_subset h)) ?_
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact rs_subset v₀ hs₁
    · exact rs_subset v₀ hs₂
  have hsnot : ∀ s ∈ ({s₁, s₂} : Finset V), s ∉ insert h (rs M W h) := by
    intro s hs
    simp only [mem_insert, mem_singleton] at hs
    have hsv : s ∈ rs M W v₀ := by rcases hs with rfl | rfl <;> assumption
    have hsh : s ≠ h := by rcases hs with rfl | rfl <;> assumption
    simp only [mem_insert, not_or]
    exact ⟨hsh, fun hm => htri s hsv h hhv₀ (hrec s (rs_subset v₀ hsv) h hhW hm)⟩
  have hcard7 : (insert h (rs M W h) ∪ {s₁, s₂}).card = 7 := by
    rw [card_union_of_disjoint (disjoint_left.mpr fun a ha hb => hsnot a hb ha),
      card_insert_of_notMem (not_mem_rs h), hh4, card_pair hs12]
  have hW7 := card_le_card hsub7
  rw [hcard7] at hW7
  have hW9 : 9 ≤ W.card := by
    by_contra hlt
    have heqW : insert h (rs M W h) ∪ {s₁, s₂} = W := eq_of_subset_of_card_le hsub7 (by omega)
    have hn : ∀ n ∈ rs M W h, s₁ ∈ rs M W n := by
      intro n hn
      have hnW := rs_subset h hn
      have hsub : rs M W n ⊆ {h, s₁, s₂} := by
        intro v hv
        have hvW := rs_subset n hv
        rw [← heqW] at hvW
        rcases mem_union.mp hvW with hv1 | hv2
        · rcases mem_insert.mp hv1 with rfl | hv1
          · simp
          · exact absurd hv (fun hm => hyp.triangleFree h n v (mem_inter.mp hn).1
              (mem_inter.mp hv1).1 (mem_inter.mp hm).1)
        · simp only [mem_insert, mem_singleton] at hv2 ⊢
          exact Or.inr hv2
      have h3 : 3 ≤ (rs M W n).card := by
        rcases hdeg n hnW with ⟨-, h3⟩ | ⟨-, h4'⟩ <;> omega
      have heq : rs M W n = {h, s₁, s₂} := eq_of_subset_of_card_le hsub (by
        rw [card_insert_of_notMem (by simp [hs₁h.symm, hs₂h.symm]), card_pair hs12]
        exact h3)
      rw [heq]; simp
    have hsub : rs M W h ⊆ rs M W s₁ := fun n hn' =>
      hrec s₁ (rs_subset v₀ hs₁) n (rs_subset h hn') (hn n hn')
    have := card_le_card hsub
    have h3 : (rs M W s₁).card = 3 := by
      rcases hdeg s₁ (rs_subset v₀ hs₁) with ⟨-, h3⟩ | ⟨hl, -⟩
      · exact h3
      · exact absurd (hlight s₁ hs₁ hs₁h) hl
    omega
  obtain ⟨hX₀, _, _⟩ := St.first hW hyp hv₀W (Or.inr hv₀3)
  have hX₀card : (insert v₀ (rs M W v₀)).card = 4 := by
    rw [card_insert_of_notMem (not_mem_rs v₀), hv₀3]
  have hX₀even : Even (insert v₀ (rs M W v₀)).card := by rw [hX₀card]; decide
  have hNC₀ : (NC M W (insert v₀ (rs M W v₀))).card ≤ (NC M W (insert v₀ (rs M W v₀))).card := le_rfl
  have hY₀ : 3 ≤ W.card - (insert v₀ (rs M W v₀)).card := by rw [hX₀card]; omega
  have hpend2 : ∀ s ∈ rs M W v₀, s ≠ h → (pend M W (insert v₀ (rs M W v₀)) s).card = 2 := by
    intro s hs hsh
    have hsW := rs_subset v₀ hs
    have heq : pend M W (insert v₀ (rs M W v₀)) s = (rs M W s).erase v₀ := by
      ext v
      simp only [pend, mem_sdiff, mem_insert, mem_erase, not_or]
      constructor
      · rintro ⟨hv, hne, -⟩; exact ⟨hne, hv⟩
      · rintro ⟨hne, hv⟩; exact ⟨hv, hne, fun hm => htri s hs v hm hv⟩
    rw [heq, card_erase_of_mem (hrec s hsW v₀ hv₀W hs)]
    rcases hdeg s hsW with ⟨-, h3⟩ | ⟨hl, -⟩
    · omega
    · exact absurd (hlight s hs hsh) hl
  have hF2 := F2 hW hyp (hOS v₀ _) (F2Mode.of_S1 hS1) _ _ hX₀ hX₀even rfl hY₀ hNC₀ s₁
    (mem_insert_of_mem hs₁) s₂ (mem_insert_of_mem hs₂) (hpend2 s₁ hs₁ hs₁h) (hpend2 s₂ hs₂ hs₂h)
  obtain ⟨hX₁, hdrop₁⟩ := hX₀.move hW hyp (mem_insert_of_mem hs₁) (Or.inl (hpend2 s₁ hs₁ hs₁h))
  have hX₁card : (insert v₀ (rs M W v₀) ∪ pend M W (insert v₀ (rs M W v₀)) s₁).card = 6 := by
    rw [card_union_of_disjoint (disjoint_pend _ s₁), hX₀card, hpend2 s₁ hs₁ hs₁h]
  obtain ⟨a, b, hab, hpab⟩ := card_eq_two.mp (hpend2 s₁ hs₁ hs₁h)
  have ha : a ∈ pend M W (insert v₀ (rs M W v₀)) s₁ := by rw [hpab]; simp
  have hb : b ∈ pend M W (insert v₀ (rs M W v₀)) s₁ := by rw [hpab]; simp
  obtain ⟨c, hc, hcl⟩ : ∃ c ∈ pend M W (insert v₀ (rs M W v₀)) s₁, StarOn M W c := by
    by_cases hal : StarOn M W a
    · exact ⟨a, ha, hal⟩
    · refine ⟨b, hb, ?_⟩
      by_contra hbl
      exact hS1 s₁ (rs_subset v₀ hs₁) a (pend_subset_rs _ _ ha) b (pend_subset_rs _ _ hb) hab
        (mem_filter.mpr ⟨pend_subset _ _ ha, hal⟩) (mem_filter.mpr ⟨pend_subset _ _ hb, hbl⟩)
  have hcW := pend_subset _ _ hc
  have hc₂ : c ∈ pend M W (insert v₀ (rs M W v₀)) s₂ := by rw [← hF2]; exact hc
  have hs₁c : s₁ ∈ rs M W c := hrec c hcW s₁ (rs_subset v₀ hs₁) (pend_subset_rs _ _ hc)
  have hs₂c : s₂ ∈ rs M W c := hrec c hcW s₂ (rs_subset v₀ hs₂) (pend_subset_rs _ _ hc₂)
  have hc3 : (rs M W c).card = 3 := by
    rcases hdeg c hcW with ⟨-, h3⟩ | ⟨hl, -⟩
    · exact h3
    · exact absurd hcl hl
  have hle1 : (pend M W (insert v₀ (rs M W v₀) ∪ pend M W (insert v₀ (rs M W v₀)) s₁) c).card ≤ 1 := by
    have hsub : pend M W (insert v₀ (rs M W v₀) ∪ pend M W (insert v₀ (rs M W v₀)) s₁) c ⊆
        ((rs M W c).erase s₁).erase s₂ := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
      refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨?_, hv1⟩⟩
      · rintro rfl; exact hv2 (mem_union_left _ (mem_insert_of_mem hs₂))
      · rintro rfl; exact hv2 (mem_union_left _ (mem_insert_of_mem hs₁))
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_erase.mpr ⟨hs12.symm, hs₂c⟩), card_erase_of_mem hs₁c, hc3] at this
    omega
  have hpos := card_pos.mpr (imm_closure hyp hX₀.sub (mem_insert_of_mem hs₁) hdrop₁
    (by rw [hpend2 s₁ hs₁ hs₁h]) hc)
  exact F1 hW hyp (hOS v₀ _) hX₁ (by rw [hX₁card]; decide) (by rw [hX₁card]; omega)
    ((card_le_card (NC_anti subset_union_left)).trans hNC₀) (mem_union_right _ hc) (by omega)

/-- **Hereditary half bound under `SHStarOn`.** -/
theorem finrank_subCode_le_half_SHStar (hyp : ThmSHyp M) :
    ∀ W : Finset V, SHStarOn M W → finrank F (subCode M W) ≤ W.card / 2 := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
    intro hSH
    by_contra hlt
    push Not at hlt
    exact MinCE.false_SHStar ⟨fun t ht => ih t ht (hSH.mono ht.subset), hlt⟩ hyp hSH

end StartStar

/-! ### Global Theorem SH*, graph form, and Corollary SH* -/

section GlobalStar

variable {M : Matrix V V F}

theorem shStarOn_univ (h4 : ∀ v, Star4 M v) (hH : (heavyVerts M).card ≤ 2 ∨ SepS1 M) :
    SHStarOn M univ := by
  refine ⟨fun v _ => (star4On_univ_iff v).mpr (h4 v), ?_⟩
  rw [heavySet_univ]
  rcases hH with hc | h1
  · exact Or.inl hc
  · refine Or.inr fun v _ p hp q hq hpq hph => ?_
    rw [heavySet_univ] at hph ⊢
    rw [rs_univ] at hp hq
    exact h1 v p q hp hq hpq hph

/-- **Theorem SH*.** If `M` has unit diagonal and no recovery triangle, every vertex satisfies
`(★4)`, and the heavy vertices either number at most two or satisfy `(S1)` alone (no vertex has
two heavy recovery neighbours; adjacent heavy pairs are permitted), then `dim ker M ≤ ⌊N/2⌋` over
every field. -/
theorem theoremSHStar (hyp : ThmSHyp M) (h4 : ∀ v, Star4 M v)
    (hH : (heavyVerts M).card ≤ 2 ∨ SepS1 M) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ Fintype.card V / 2 := by
  have h := finrank_subCode_le_half_SHStar hyp univ (shStarOn_univ h4 hH)
  rwa [subCode_univ, card_univ] at h

/-- **Theorem SH* for the transpose.** -/
theorem theoremSHStar_transpose (hyp : ThmSHyp M) (h4 : ∀ v, Star4 M.transpose v)
    (hH : (heavyVerts M.transpose).card ≤ 2 ∨ SepS1 M.transpose) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ Fintype.card V / 2 := by
  rw [← finrank_ker_transpose]
  exact theoremSHStar (thmSHyp_transpose hyp) h4 hH

/-- `u` and `v` share no common neighbour in `G` (relaxing `Far3` by allowing `G.Adj u v`). -/
def NoCommonNbhd (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ w, ¬ (G.Adj u w ∧ G.Adj w v)

theorem sepS1_of_noCommonNbhd {G : SimpleGraph V} (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (hnocom : ∀ u ∈ heavyVerts M, ∀ v ∈ heavyVerts M, u ≠ v → NoCommonNbhd G u v) : SepS1 M :=
  fun v p q hp hq hpq hph hqh =>
    hnocom p hph q hqh hpq v ⟨(adj_of_mem_recSet hpat hp).symm, adj_of_mem_recSet hpat hq⟩

/-- **Theorem SH*, graph form.** If `G` is triangle-free of maximum degree at most `4`, the
off-diagonal support of `M` lies in `G`, and the vertices violating `(★★)` number at most two or
have no common neighbour in `G` (allowing matched heavy pairs), then `rank M ≥ ⌈N/2⌉`. -/
theorem theoremSHStar_graph {G : SimpleGraph V} [DecidableRel G.Adj] (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 4)
    (hH : (heavyVerts M).card ≤ 2 ∨
      ∀ u ∈ heavyVerts M, ∀ v ∈ heavyVerts M, u ≠ v → NoCommonNbhd G u v) :
    (Fintype.card V + 1) / 2 ≤ M.rank := by
  have h1 := theoremSHStar (thmSHyp_of_cliqueFree hdiag hpat htri)
    (star4_of_degree_le_four hpat hdeg) (hH.imp id (sepS1_of_noCommonNbhd hpat))
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have h3 : M.rank = finrank F (LinearMap.range M.mulVecLin) := rfl
  omega

/-- **Corollary SH*, barrier form.** -/
theorem finrank_ker_le_barrier_SHStar (hyp : ThmSHyp M) (U : Finset V) (P : Finset (Finset V))
    (hcover : P.biUnion id = univ \ U) (hdisj : (P : Set (Finset V)).PairwiseDisjoint id)
    (hsep : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → ∀ u ∈ B, ∀ v ∈ B', M u v = 0)
    (hblock : ∀ B ∈ P, SHStarOn M B) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ U.card + ∑ B ∈ P, B.card / 2 := by
  let G := SimpleGraph.fromRel fun v u => M v u ≠ 0
  have hpat : ∀ v u, u ∈ recSet M v → G.Adj v u := by
    intro v u hu
    obtain ⟨hne, hM⟩ := mem_recSet.mp hu
    exact (SimpleGraph.fromRel_adj _ v u).mpr ⟨Ne.symm hne, Or.inl hM⟩
  have hsep' : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → ∀ a ∈ B, ∀ b ∈ B', ¬ G.Adj a b := by
    intro B hB B' hB' hne a ha b hb hab
    obtain ⟨-, h1 | h2⟩ := (SimpleGraph.fromRel_adj _ a b).mp hab
    · exact h1 (hsep B hB B' hB' hne a ha b hb)
    · exact h2 (hsep B' hB' B hB (Ne.symm hne) b hb a ha)
  rw [← subCode_univ]
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M univ) U
  have h2 := Submodule.finrank_mono (subCode_inf_zeroOn_le M univ U)
  have h3 := finrank_subCode_biUnion_le hpat P hdisj hsep'
  rw [hcover] at h3
  have h4 : ∑ B ∈ P, finrank F (subCode M B) ≤ ∑ B ∈ P, B.card / 2 :=
    sum_le_sum fun B hB => finrank_subCode_le_half_SHStar hyp B (hblock B hB)
  omega

/-- **Corollary SH*, matching form.** For any subset `D ⊆ heavyVerts M` that either has size at
most `2` or has no two distinct vertices sharing a common neighbour in `G`,
`dim ker M + |D| ≤ ν(G) + |H|`. -/
theorem finrank_ker_add_card_le_matching_SHStar {G : SimpleGraph V} (hyp : ThmSHyp M)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u) (h4 : ∀ v, Star4 M v) {D : Finset V}
    (hD : D ⊆ heavyVerts M)
    (hDc : D.card ≤ 2 ∨ ∀ u ∈ D, ∀ v ∈ D, u ≠ v → NoCommonNbhd G u v) :
    finrank F (LinearMap.ker M.mulVecLin) + D.card ≤ G.matchingNumber + (heavyVerts M).card := by
  set U := heavyVerts M \ D
  obtain ⟨U', hU'⟩ := G.exists_card_add_sum_card_div_two_eq_matchingNumber
  set P := (G.componentBlocks U').image fun B => B \ U
  have hcover : P.biUnion id = univ \ (U ∪ U') := by
    ext v
    rw [mem_biUnion, mem_sdiff, mem_union]
    constructor
    · rintro ⟨B', hB', hvB'⟩
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hB'
      obtain ⟨hvB, hvU⟩ := mem_sdiff.mp hvB'
      have : v ∈ (G.componentBlocks U').biUnion id := mem_biUnion.mpr ⟨B, hB, hvB⟩
      rw [G.biUnion_componentBlocks U'] at this
      exact ⟨mem_univ v, fun h => h.elim hvU (mem_sdiff.mp this).2⟩
    · rintro ⟨-, hv⟩
      have hvU : v ∉ U := fun h => hv (Or.inl h)
      have hvU' : v ∉ U' := fun h => hv (Or.inr h)
      have : v ∈ (G.componentBlocks U').biUnion id := by
        rw [G.biUnion_componentBlocks U']
        exact mem_sdiff.mpr ⟨mem_univ v, hvU'⟩
      obtain ⟨B, hB, hvB⟩ := mem_biUnion.mp this
      exact ⟨B \ U, mem_image.mpr ⟨B, hB, rfl⟩, mem_sdiff.mpr ⟨hvB, hvU⟩⟩
  have hblocks : ∀ B' ∈ P, ∀ B'' ∈ P, B' ≠ B'' → ∃ B₁ ∈ G.componentBlocks U',
      ∃ B₂ ∈ G.componentBlocks U', B₁ ≠ B₂ ∧ B' = B₁ \ U ∧ B'' = B₂ \ U := by
    intro B' hB' B'' hB'' hne
    obtain ⟨B₁, hB₁, rfl⟩ := mem_image.mp hB'
    obtain ⟨B₂, hB₂, rfl⟩ := mem_image.mp hB''
    exact ⟨B₁, hB₁, B₂, hB₂, fun e => hne (by rw [e]), rfl, rfl⟩
  have hdisj : (P : Set (Finset V)).PairwiseDisjoint id := by
    intro B' hB' B'' hB'' hne
    obtain ⟨B₁, hB₁, B₂, hB₂, hne', rfl, rfl⟩ := hblocks B' hB' B'' hB'' hne
    exact (G.pairwiseDisjoint_componentBlocks U' hB₁ hB₂ hne').mono sdiff_subset sdiff_subset
  have hsep : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → ∀ u ∈ B, ∀ v ∈ B', M u v = 0 := by
    intro B' hB' B'' hB'' hne u hu v hv
    obtain ⟨B₁, hB₁, B₂, hB₂, hne', rfl, rfl⟩ := hblocks B' hB' B'' hB'' hne
    have hadj := G.not_adj_of_mem_componentBlocks U' B₁ hB₁ B₂ hB₂ hne' u (mem_sdiff.mp hu).1 v
      (mem_sdiff.mp hv).1
    by_contra hM
    have huv : u ≠ v := fun e => disjoint_left.mp (G.pairwiseDisjoint_componentBlocks U' hB₁ hB₂ hne')
      (mem_sdiff.mp hu).1 (e ▸ (mem_sdiff.mp hv).1)
    exact hadj (hpat u v (mem_recSet.mpr ⟨Ne.symm huv, hM⟩))
  have hblock : ∀ B ∈ P, SHStarOn M B := by
    intro B' hB'
    obtain ⟨B, -, rfl⟩ := mem_image.mp hB'
    have hHD : heavySet M (B \ U) ⊆ D := by
      intro g hg
      have hgH : g ∈ heavyVerts M := by
        rw [← heavySet_univ]
        exact heavySet_mono (subset_univ _) hg
      by_contra hgD
      exact (mem_sdiff.mp (mem_filter.mp hg).1).2 (mem_sdiff.mpr ⟨hgH, hgD⟩)
    refine ⟨fun v _ => ((star4On_univ_iff v).mpr (h4 v)).mono (subset_univ _), ?_⟩
    rcases hDc with hc | hnocom
    · exact Or.inl ((card_le_card hHD).trans hc)
    · refine Or.inr fun v _ p hp q hq hpq hph hqh => ?_
      exact hnocom p (hHD hph) q (hHD hqh) hpq v
        ⟨(hpat v p (mem_inter.mp hp).1).symm, hpat v q (mem_inter.mp hq).1⟩
  have hbar := finrank_ker_le_barrier_SHStar hyp (U ∪ U') P hcover hdisj hsep hblock
  have hsum : ∑ B ∈ P, B.card / 2 ≤ ∑ B ∈ G.componentBlocks U', B.card / 2 :=
    (sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans
      (sum_le_sum fun B _ => Nat.div_le_div_right (card_le_card sdiff_subset))
  have hUU := card_union_le U U'
  have hUc : U.card + D.card = (heavyVerts M).card := by
    rw [card_sdiff_of_subset hD]
    have := card_le_card hD
    omega
  omega

open Classical in
/-- `ρ_match(G, H)`: the largest size of a subset `D ⊆ H` whose elements share no common
neighbour in `G` (on a triangle-free graph, an induced matching plus isolated vertices with no
pair at distance `2` in `G`). -/
noncomputable def rhoMatch (G : SimpleGraph V) (H : Finset V) : ℕ :=
  (H.powerset.filter fun D => ∀ u ∈ D, ∀ v ∈ D, u ≠ v → NoCommonNbhd G u v).sup card

omit [DecidableEq F] in
theorem exists_rhoMatch (G : SimpleGraph V) (H : Finset V) :
    ∃ D ⊆ H, (∀ u ∈ D, ∀ v ∈ D, u ≠ v → NoCommonNbhd G u v) ∧ D.card = rhoMatch G H := by
  classical
  obtain ⟨D, hD, he⟩ := exists_mem_eq_sup
    (H.powerset.filter fun D => ∀ u ∈ D, ∀ v ∈ D, u ≠ v → NoCommonNbhd G u v)
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset H, by simp⟩⟩ card
  obtain ⟨hDH, hnocom⟩ := mem_filter.mp hD
  refine ⟨D, mem_powerset.mp hDH, hnocom, ?_⟩
  unfold rhoMatch
  convert he.symm

omit [DecidableEq F] in
theorem rho3_le_rhoMatch (G : SimpleGraph V) (H : Finset V) :
    rho3 G H ≤ rhoMatch G H := by
  obtain ⟨D, hDH, hfar, hcard⟩ := exists_rho3 G H
  rw [← hcard]
  classical
  refine le_sup (mem_filter.mpr ⟨mem_powerset.mpr hDH, fun u hu v hv huv => (hfar u hu v hv huv).2⟩)

/-- **Corollary SH*, matching-packing form.** On a triangle-free graph of maximum degree at most
`4` containing the support of `M`,
`dim ker M + max(ρ_match(G, H), min(|H|, 2)) ≤ ν(G) + |H|`. -/
theorem finrank_ker_le_matching_rhoMatch {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 4) :
    finrank F (LinearMap.ker M.mulVecLin) +
        max (rhoMatch G (heavyVerts M)) (min (heavyVerts M).card 2) ≤
      G.matchingNumber + (heavyVerts M).card := by
  have hyp := thmSHyp_of_cliqueFree hdiag hpat htri
  have hpat' : ∀ v u, u ∈ recSet M v → G.Adj v u := fun _ _ hu => adj_of_mem_recSet hpat hu
  have h4 := star4_of_degree_le_four hpat hdeg
  rcases le_total (rhoMatch G (heavyVerts M)) (min (heavyVerts M).card 2) with hle | hle
  · rw [max_eq_right hle]
    obtain ⟨D, hD, hc⟩ := exists_subset_card_eq (show min (heavyVerts M).card 2 ≤ (heavyVerts M).card
      from min_le_left _ _)
    rw [← hc]
    exact finrank_ker_add_card_le_matching_SHStar hyp hpat' h4 hD
      (Or.inl (by rw [hc]; exact min_le_right _ _))
  · rw [max_eq_left hle]
    obtain ⟨D, hD, hnocom, hc⟩ := exists_rhoMatch G (heavyVerts M)
    rw [← hc]
    exact finrank_ker_add_card_le_matching_SHStar hyp hpat' h4 hD (Or.inr hnocom)

/-- **Corollary SH*, matching-packing form, transpose.** -/
theorem finrank_ker_le_matching_rhoMatch_transpose {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 4) :
    finrank F (LinearMap.ker M.mulVecLin) +
        max (rhoMatch G (heavyVerts M.transpose)) (min (heavyVerts M.transpose).card 2) ≤
      G.matchingNumber + (heavyVerts M.transpose).card := by
  rw [← finrank_ker_transpose]
  refine finrank_ker_le_matching_rhoMatch (M := M.transpose)
    (fun v => by rw [Matrix.transpose_apply, hdiag v]) (fun v u hvu hadj => ?_) htri hdeg
  rw [Matrix.transpose_apply]
  exact hpat u v (Ne.symm hvu) fun h => hadj h.symm

end GlobalStar

end DirectedReciprocity
