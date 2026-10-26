import BoundedNesting.SHPhase
import MotionDepthCodes.MatchingForm

/-!
# Theorem SH: separated heavy vertices

Let `M` have unit diagonal and no recovery triangle (`ThmSHyp`, paper 4), let every vertex satisfy
(★4) (`Star4`), and let the heavy vertices, those violating (★★) (`heavyVerts`), number at most two
or satisfy (S1) and (S2) (`SepS1`, `SepS2`).

* `MinCE.false_SH`: a minimal counterexample is impossible: the three starting cases of the paper,
  with the odd-state lemma and Phase E (`SHPhase.lean`).
* `finrank_subCode_le_half_SH`: the half bound on every vertex set on which the hypotheses hold
  (`SHOn`), by strong induction over vertex sets.
* `theoremSH`: **Theorem SH**, `dim ker M ≤ ⌊N/2⌋`; `theoremSH_transpose`: the same under the
  hypotheses for `Mᵀ`; `theoremSH_graph`: the graph form, `rank M ≥ ⌈N/2⌉` on a triangle-free graph
  of maximum degree at most `4` whose vertices violating (★★) number at most two or are pairwise at
  distance at least `3` (`Far3`).
* `finrank_ker_le_barrier_SH`, `finrank_ker_add_card_le_matching`, `finrank_ker_add_card_le_matching_graph`
  and `finrank_ker_add_card_le_matching_transpose`: **Corollary SH**, the barrier and matching forms,
  with the matching number of lean-machine's Tutte–Berge formula.
-/

namespace BoundedNesting

open Finset Module MotionDepthCodes

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

/-! ### The start -/

section Start

variable {M : Matrix V V F} {W : Finset V}

/-- **The start.** A minimal counterexample to the half bound on which the hypotheses of Theorem SH
hold is impossible. -/
theorem MinCE.false_SH (hW : MinCE M W) (hyp : ThmSHyp M) (hSH : SHOn M W) : False := by
  obtain ⟨h4, hmode⟩ := hSH
  obtain ⟨k, hk⟩ := hW.odd
  have hOS : ∀ v₀ t, OSAt M W v₀ t := fun v₀ => odd_state hW hyp h4 hmode
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
    refine F3 hW hyp (hOS h (NC M W ({h} ∪ pend M W {h} h)).card) ?_ (singleton_subset_iff.mpr hhW)
      (by simp) (mem_singleton_self h) (by rw [hpend, hc]) (by rw [hins]; exact hX₀)
      (by rw [hpend, ← insert_eq]; exact hdrop) (by rw [hpend]; exact not_mem_rs h) le_rfl ?_
    · rcases hmode with hfew | ⟨hS1, -⟩
      · exact F2Mode.of_le_one (by rw [hins]; omega)
      · exact F2Mode.of_S1 hS1
    · rcases hmode with hfew | ⟨-, hS2⟩
      · exact Or.inr (by rw [hins]; omega)
      · left
        intro t ht
        by_contra hl
        exact hS2 h (mem_filter.mpr ⟨hhW, hheavy⟩) t (pend_subset_rs {h} h ht)
          (mem_filter.mpr ⟨pend_subset {h} h ht, hl⟩)
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
  -- the number of heavy vertices is odd
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
        · rintro ⟨b, hb, rfl⟩
          exact hb
        · intro hu
          exact ⟨⟨u, rs_subset _ hu⟩, hu, rfl⟩
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
        · rw [h4'] at hb
          exact absurd hb (by decide)
      · rintro ⟨huW, hl⟩
        refine ⟨⟨u, huW⟩, ?_, rfl⟩
        rw [hdegG]
        rcases hdeg u huW with ⟨-, h3⟩ | ⟨hl', -⟩
        · rw [h3]
          decide
        · exact absurd hl hl'
    rw [← card_map, hmapF] at heven
    have hsplit := card_filter_add_card_filter_not (s := W) (fun v => StarOn M W v)
    obtain ⟨e, he⟩ := heven
    exact ⟨k - e, by unfold heavySet; omega⟩
  -- (S1) and (S2) on `W`
  have hS : S1On M W ∧ S2On M W := by
    rcases hmode with hfew | hS
    · have h1 : (heavySet M W).card = 1 := by
        obtain ⟨j, hj⟩ := hHodd
        omega
      obtain ⟨g, hg⟩ := card_eq_one.mp h1
      refine ⟨fun v _ p _ q _ hpq hp hq => ?_, fun g' hg' u hu hu' => ?_⟩
      · rw [hg] at hp hq
        exact hpq ((mem_singleton.mp hp).trans (mem_singleton.mp hq).symm)
      · rw [hg] at hg' hu'
        rw [mem_singleton.mp hg', ← mem_singleton.mp hu'] at hu
        exact not_mem_rs u hu
    · exact hS
  obtain ⟨hS1, hS2⟩ := hS
  -- a heavy vertex `h` and a light neighbour `v₀`
  obtain ⟨h, hhH⟩ : (heavySet M W).Nonempty := by
    rw [← card_pos]
    obtain ⟨j, hj⟩ := hHodd
    omega
  obtain ⟨hhW, hheavy⟩ := mem_filter.mp hhH
  have hh4 : (rs M W h).card = 4 := by
    rcases hdeg h hhW with ⟨hl, -⟩ | ⟨-, h4'⟩
    · exact absurd hl hheavy
    · exact h4'
  obtain ⟨v₀, hv₀⟩ : (rs M W h).Nonempty := by rw [← card_pos]; omega
  have hv₀W : v₀ ∈ W := rs_subset h hv₀
  have hv₀l : StarOn M W v₀ := by
    by_contra hl
    exact hS2 h hhH v₀ hv₀ (mem_filter.mpr ⟨hv₀W, hl⟩)
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
  have hrsv₀ : rs M W v₀ = {h, s₁, s₂} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact hhv₀
      · exact hs₁
      · exact hs₂
    · rw [hv₀3, card_insert_of_notMem (by simp [hs₁h.symm, hs₂h.symm]), card_pair hs12]
  have hlight : ∀ s ∈ rs M W v₀, s ≠ h → StarOn M W s := by
    intro s hs hsh
    by_contra hl
    exact hS1 v₀ hv₀W h hhv₀ s hs (Ne.symm hsh) hhH (mem_filter.mpr ⟨rs_subset v₀ hs, hl⟩)
  have hrec : ∀ a ∈ W, ∀ b ∈ W, a ∈ rs M W b → (b : V) ∈ rs M W a := fun a ha b hb hab =>
    hrecip a ha b hb hab
  -- triangle-freeness around `v₀`
  have htri : ∀ p ∈ rs M W v₀, ∀ q ∈ rs M W v₀, q ∉ rs M W p := fun p hp q hq hqp =>
    hyp.triangleFree v₀ p q (mem_inter.mp hp).1 (mem_inter.mp hq).1 (mem_inter.mp hqp).1
  -- `|W| ≥ 9`
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
    have hW7' : W.card = 7 := by omega
    have heqW : insert h (rs M W h) ∪ {s₁, s₂} = W := eq_of_subset_of_card_le hsub7 (by omega)
    -- every neighbour of `h` recovers from exactly `h`, `s₁`, `s₂`
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
          right
          exact hv2
      have h3 : 3 ≤ (rs M W n).card := by
        rcases hdeg n hnW with ⟨-, h3⟩ | ⟨-, h4'⟩ <;> omega
      have heq : rs M W n = {h, s₁, s₂} := eq_of_subset_of_card_le hsub (by
        rw [card_insert_of_notMem (by simp [hs₁h.symm, hs₂h.symm]), card_pair hs12]
        exact h3)
      rw [heq]
      simp
    have hsub : rs M W h ⊆ rs M W s₁ := fun n hn' =>
      hrec s₁ (rs_subset v₀ hs₁) n (rs_subset h hn') (hn n hn')
    have := card_le_card hsub
    have h3 : (rs M W s₁).card = 3 := by
      rcases hdeg s₁ (rs_subset v₀ hs₁) with ⟨-, h3⟩ | ⟨hl, -⟩
      · exact h3
      · exact absurd (hlight s₁ hs₁ hs₁h) hl
    omega
  -- the run from `v₀`
  obtain ⟨hX₀, hpend₀, hdrop₀⟩ := St.first hW hyp hv₀W (Or.inr hv₀3)
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
      · rintro ⟨hv, hne, -⟩
        exact ⟨hne, hv⟩
      · rintro ⟨hne, hv⟩
        exact ⟨hv, hne, fun hm => htri s hs v hm hv⟩
    rw [heq, card_erase_of_mem (hrec s hsW v₀ hv₀W hs)]
    rcases hdeg s hsW with ⟨-, h3⟩ | ⟨hl, -⟩
    · omega
    · exact absurd (hlight s hs hsh) hl
  have hF2 := F2 hW hyp (hOS v₀ _) (F2Mode.of_S1 hS1) _ _ hX₀ hX₀even rfl hY₀ hNC₀ s₁
    (mem_insert_of_mem hs₁) s₂ (mem_insert_of_mem hs₂) (hpend2 s₁ hs₁ hs₁h) (hpend2 s₂ hs₂ hs₂h)
  -- the move of `s₁` and a light member `a` of its pending pair
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
      · rintro rfl
        exact hv2 (mem_union_left _ (mem_insert_of_mem hs₂))
      · rintro rfl
        exact hv2 (mem_union_left _ (mem_insert_of_mem hs₁))
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_erase.mpr ⟨hs12.symm, hs₂c⟩), card_erase_of_mem hs₁c, hc3] at this
    omega
  have hpos := card_pos.mpr (imm_closure hyp hX₀.sub (mem_insert_of_mem hs₁) hdrop₁
    (by rw [hpend2 s₁ hs₁ hs₁h]) hc)
  exact F1 hW hyp (hOS v₀ _) hX₁ (by rw [hX₁card]; decide) (by rw [hX₁card]; omega)
    ((card_le_card (NC_anti subset_union_left)).trans hNC₀) (mem_union_right _ hc) (by omega)

/-- **The half bound under the hypotheses of Theorem SH**, on every vertex set on which they hold. -/
theorem finrank_subCode_le_half_SH (hyp : ThmSHyp M) :
    ∀ W : Finset V, SHOn M W → finrank F (subCode M W) ≤ W.card / 2 := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
    intro hSH
    by_contra hlt
    push Not at hlt
    exact MinCE.false_SH ⟨fun t ht => ih t ht (hSH.mono ht.subset), hlt⟩ hyp hSH

end Start

/-! ### The global statement -/

section Global

variable {M : Matrix V V F}

instance (M : Matrix V V F) (v : V) : Decidable (MotionDepthCodes.Star M v) := by
  unfold MotionDepthCodes.Star; infer_instance

/-- (★4) at `v`: at most three recovery neighbours, or exactly four that include every vertex
recovering from `v`. -/
def Star4 (M : Matrix V V F) (v : V) : Prop :=
  (recSet M v).card ≤ 3 ∨ ((recSet M v).card = 4 ∧ ∀ r, v ∈ recSet M r → r ∈ recSet M v)

/-- The heavy vertices: those violating (★★). -/
def heavyVerts (M : Matrix V V F) : Finset V := univ.filter fun v => ¬ MotionDepthCodes.Star M v

/-- (S1): no vertex has two heavy vertices in its recovery set. -/
def SepS1 (M : Matrix V V F) : Prop :=
  ∀ v p q, p ∈ recSet M v → q ∈ recSet M v → p ≠ q → p ∈ heavyVerts M → q ∉ heavyVerts M

/-- (S2): no heavy vertex has a heavy vertex in its recovery set. -/
def SepS2 (M : Matrix V V F) : Prop := ∀ g ∈ heavyVerts M, ∀ u ∈ recSet M g, u ∉ heavyVerts M

theorem rs_univ (v : V) : rs M univ v = recSet M v := inter_univ _

theorem starOn_univ_iff (v : V) : StarOn M univ v ↔ MotionDepthCodes.Star M v := by
  unfold StarOn MotionDepthCodes.Star
  simp only [rs_univ, mem_univ, true_implies]

theorem star4On_univ_iff (v : V) : Star4On M univ v ↔ Star4 M v := by
  unfold Star4On Star4
  simp only [rs_univ, mem_univ, true_implies]

theorem heavySet_univ : heavySet M univ = heavyVerts M := by
  ext v
  simp [heavySet, heavyVerts, starOn_univ_iff]

theorem shOn_univ (h4 : ∀ v, Star4 M v) (hH : (heavyVerts M).card ≤ 2 ∨ (SepS1 M ∧ SepS2 M)) :
    SHOn M univ := by
  refine ⟨fun v _ => (star4On_univ_iff v).mpr (h4 v), ?_⟩
  rw [heavySet_univ]
  rcases hH with hc | ⟨h1, h2⟩
  · exact Or.inl hc
  · refine Or.inr ⟨fun v _ p hp q hq hpq hph => ?_, fun g hg u hu => ?_⟩
    · rw [heavySet_univ] at hph ⊢
      rw [rs_univ] at hp hq
      exact h1 v p q hp hq hpq hph
    · rw [heavySet_univ] at hg ⊢
      rw [rs_univ] at hu
      exact h2 g hg u hu

/-- **Theorem SH.** If `M` has unit diagonal and no recovery triangle, every vertex satisfies (★4),
and the heavy vertices number at most two or satisfy (S1) and (S2), then `dim ker M ≤ ⌊N/2⌋`, over
every field. -/
theorem theoremSH (hyp : ThmSHyp M) (h4 : ∀ v, Star4 M v)
    (hH : (heavyVerts M).card ≤ 2 ∨ (SepS1 M ∧ SepS2 M)) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ Fintype.card V / 2 := by
  have h := finrank_subCode_le_half_SH hyp univ (shOn_univ h4 hH)
  rwa [subCode_univ, card_univ] at h

/-- The absence of recovery triangles is invariant under transposition. -/
theorem recTriangleFree_transpose (h : RecTriangleFree M) : RecTriangleFree M.transpose := by
  intro r p q hp hq hqp
  rw [mem_recSet, Matrix.transpose_apply] at hp hq hqp
  exact h q p r (mem_recSet.mpr ⟨Ne.symm hqp.1, hqp.2⟩) (mem_recSet.mpr ⟨Ne.symm hq.1, hq.2⟩)
    (mem_recSet.mpr ⟨Ne.symm hp.1, hp.2⟩)

theorem thmSHyp_transpose (hyp : ThmSHyp M) : ThmSHyp M.transpose :=
  ⟨fun v => by rw [Matrix.transpose_apply, hyp.diag v], recTriangleFree_transpose hyp.triangleFree⟩

omit [DecidableEq V] [DecidableEq F] in
theorem finrank_ker_transpose (M : Matrix V V F) :
    finrank F (LinearMap.ker M.transpose.mulVecLin) = finrank F (LinearMap.ker M.mulVecLin) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
  have h3 : M.transpose.rank = M.rank := Matrix.rank_transpose M
  unfold Matrix.rank at h3
  omega

/-- **Theorem SH for the transpose**: the same bound when `Mᵀ` satisfies (★4) and its heavy
vertices satisfy the hypothesis. -/
theorem theoremSH_transpose (hyp : ThmSHyp M) (h4 : ∀ v, Star4 M.transpose v)
    (hH : (heavyVerts M.transpose).card ≤ 2 ∨ (SepS1 M.transpose ∧ SepS2 M.transpose)) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ Fintype.card V / 2 := by
  rw [← finrank_ker_transpose]
  exact theoremSH (thmSHyp_transpose hyp) h4 hH

end Global

/-! ### The graph form -/

section Graph

variable {M : Matrix V V F}

/-- `u` and `v` lie at distance at least `3` in `G`: not adjacent, without a common neighbour. -/
def Far3 (G : SimpleGraph V) (u v : V) : Prop := ¬ G.Adj u v ∧ ∀ w, ¬ (G.Adj u w ∧ G.Adj w v)

theorem adj_of_mem_recSet {G : SimpleGraph V} (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    {v u : V} (hu : u ∈ recSet M v) : G.Adj v u := by
  obtain ⟨hne, hM⟩ := mem_recSet.mp hu
  by_contra h
  exact hM (hpat v u (Ne.symm hne) h)

/-- On a graph of maximum degree at most `4`, every pattern matrix satisfies (★4). -/
theorem star4_of_degree_le_four {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) (hdeg : ∀ v, G.degree v ≤ 4) (v : V) :
    Star4 M v := by
  have hsub : recSet M v ⊆ G.neighborFinset v := fun u hu => by
    rw [SimpleGraph.mem_neighborFinset]
    exact adj_of_mem_recSet hpat hu
  have hcard := card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  by_cases h3 : (recSet M v).card ≤ 3
  · exact Or.inl h3
  · right
    have hdv := hdeg v
    have heq : recSet M v = G.neighborFinset v :=
      eq_of_subset_of_card_le hsub (by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega)
    refine ⟨by omega, fun r hr => ?_⟩
    rw [heq, SimpleGraph.mem_neighborFinset]
    exact (adj_of_mem_recSet hpat hr).symm

/-- Heavy vertices pairwise at distance at least `3` satisfy (S1) and (S2). -/
theorem sep_of_far3 {G : SimpleGraph V} (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (hfar : ∀ u ∈ heavyVerts M, ∀ v ∈ heavyVerts M, u ≠ v → Far3 G u v) : SepS1 M ∧ SepS2 M := by
  refine ⟨fun v p q hp hq hpq hph hqh => ?_, fun g hg u hu huh => ?_⟩
  · exact (hfar p hph q hqh hpq).2 v ⟨(adj_of_mem_recSet hpat hp).symm, adj_of_mem_recSet hpat hq⟩
  · exact (hfar g hg u huh (fun e => (mem_recSet.mp hu).1 e.symm)).1 (adj_of_mem_recSet hpat hu)

/-- **Theorem SH, graph form.** If `G` is triangle-free of maximum degree at most `4`, the
off-diagonal support of `M` lies in the edges of `G`, and the vertices violating (★★) number at most
two or lie pairwise at distance at least `3` in `G`, then `rank M ≥ ⌈N/2⌉`. -/
theorem theoremSH_graph {G : SimpleGraph V} [DecidableRel G.Adj] (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 4)
    (hH : (heavyVerts M).card ≤ 2 ∨ ∀ u ∈ heavyVerts M, ∀ v ∈ heavyVerts M, u ≠ v → Far3 G u v) :
    (Fintype.card V + 1) / 2 ≤ M.rank := by
  have h1 := theoremSH (thmSHyp_of_cliqueFree hdiag hpat htri) (star4_of_degree_le_four hpat hdeg)
    (hH.imp id (sep_of_far3 hpat))
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have h3 : M.rank = finrank F (LinearMap.range M.mulVecLin) := rfl
  omega

end Graph

/-! ### Corollary SH: barrier and matching forms -/

section Corollary

variable {M : Matrix V V F}

/-- **Corollary SH, barrier form.** Let `V \ U` be partitioned into blocks with `M_uv = 0` for `u`,
`v` in different blocks, and let the hypotheses of Theorem SH hold on every block. Then
`dim ker M ≤ |U| + ∑_B ⌊|B|/2⌋`. -/
theorem finrank_ker_le_barrier_SH (hyp : ThmSHyp M) (U : Finset V) (P : Finset (Finset V))
    (hcover : P.biUnion id = univ \ U) (hdisj : (P : Set (Finset V)).PairwiseDisjoint id)
    (hsep : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → ∀ u ∈ B, ∀ v ∈ B', M u v = 0)
    (hblock : ∀ B ∈ P, SHOn M B) :
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
    sum_le_sum fun B hB => finrank_subCode_le_half_SH hyp B (hblock B hB)
  omega

/-- **Corollary SH, matching form.** If the support of `M` lies in `G`, every vertex satisfies
(★4), and `D` is a set of heavy vertices that has at most two elements or is pairwise at distance at
least `3` in `G`, then `dim ker M ≤ ν(G) + |H| - |D|`. Taking for `D` a largest such set gives
`dim ker M ≤ ν(G) + |H| - max(ρ₃(H), min(|H|, 2))`. -/
theorem finrank_ker_add_card_le_matching {G : SimpleGraph V} (hyp : ThmSHyp M)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u) (h4 : ∀ v, Star4 M v) {D : Finset V}
    (hD : D ⊆ heavyVerts M) (hDc : D.card ≤ 2 ∨ ∀ u ∈ D, ∀ v ∈ D, u ≠ v → Far3 G u v) :
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
  have hblock : ∀ B ∈ P, SHOn M B := by
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
    rcases hDc with hc | hfar
    · exact Or.inl ((card_le_card hHD).trans hc)
    · refine Or.inr ⟨fun v _ p hp q hq hpq hph hqh => ?_, fun g hg u hu huh => ?_⟩
      · exact (hfar p (hHD hph) q (hHD hqh) hpq).2 v
          ⟨(hpat v p (mem_inter.mp hp).1).symm, hpat v q (mem_inter.mp hq).1⟩
      · have hug : u ≠ g := by
          rintro rfl
          exact not_mem_rs u hu
        exact (hfar g (hHD hg) u (hHD huh) (Ne.symm hug)).1 (hpat g u (mem_inter.mp hu).1)
  have hbar := finrank_ker_le_barrier_SH hyp (U ∪ U') P hcover hdisj hsep hblock
  have hsum : ∑ B ∈ P, B.card / 2 ≤ ∑ B ∈ G.componentBlocks U', B.card / 2 :=
    (sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans
      (sum_le_sum fun B _ => Nat.div_le_div_right (card_le_card sdiff_subset))
  have hUU := card_union_le U U'
  have hUc : U.card + D.card = (heavyVerts M).card := by
    rw [card_sdiff_of_subset hD]
    have := card_le_card hD
    omega
  omega

/-- **Corollary SH, matching form on a graph.** On a triangle-free graph of maximum degree at most `4`
containing the support of `M`: `dim ker M + |D| ≤ ν(G) + |H|` for every set `D` of heavy vertices
with at most two elements or pairwise at distance at least `3`. -/
theorem finrank_ker_add_card_le_matching_graph {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 4) {D : Finset V} (hD : D ⊆ heavyVerts M)
    (hDc : D.card ≤ 2 ∨ ∀ u ∈ D, ∀ v ∈ D, u ≠ v → Far3 G u v) :
    finrank F (LinearMap.ker M.mulVecLin) + D.card ≤ G.matchingNumber + (heavyVerts M).card :=
  finrank_ker_add_card_le_matching (thmSHyp_of_cliqueFree hdiag hpat htri)
    (fun _ _ hu => adj_of_mem_recSet hpat hu) (star4_of_degree_le_four hpat hdeg) hD hDc

/-- **Corollary SH, matching form, transpose**: the same with the heavy set of `Mᵀ`. -/
theorem finrank_ker_add_card_le_matching_transpose {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 4) {D : Finset V}
    (hD : D ⊆ heavyVerts M.transpose)
    (hDc : D.card ≤ 2 ∨ ∀ u ∈ D, ∀ v ∈ D, u ≠ v → Far3 G u v) :
    finrank F (LinearMap.ker M.mulVecLin) + D.card ≤
      G.matchingNumber + (heavyVerts M.transpose).card := by
  rw [← finrank_ker_transpose]
  refine finrank_ker_add_card_le_matching_graph (M := M.transpose)
    (fun v => by rw [Matrix.transpose_apply, hdiag v]) (fun v u hvu hadj => ?_) htri hdeg hD hDc
  rw [Matrix.transpose_apply]
  exact hpat u v (Ne.symm hvu) fun h => hadj h.symm

open Classical in
/-- `ρ₃(H)`: the largest size of a subset of `H` whose elements lie pairwise at distance at least `3`
in `G`. -/
noncomputable def rho3 (G : SimpleGraph V) (H : Finset V) : ℕ :=
  (H.powerset.filter fun D => ∀ u ∈ D, ∀ v ∈ D, u ≠ v → Far3 G u v).sup card

omit [DecidableEq F] in
theorem exists_rho3 (G : SimpleGraph V) (H : Finset V) :
    ∃ D ⊆ H, (∀ u ∈ D, ∀ v ∈ D, u ≠ v → Far3 G u v) ∧ D.card = rho3 G H := by
  classical
  obtain ⟨D, hD, he⟩ := exists_mem_eq_sup
    (H.powerset.filter fun D => ∀ u ∈ D, ∀ v ∈ D, u ≠ v → Far3 G u v)
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset H, by simp⟩⟩ card
  obtain ⟨hDH, hfar⟩ := mem_filter.mp hD
  refine ⟨D, mem_powerset.mp hDH, hfar, ?_⟩
  unfold rho3
  convert he.symm

/-- **Corollary SH, matching form, as stated.** On a triangle-free graph of maximum degree at most
`4` containing the support of `M`,
`dim ker M ≤ ν(G) + |H| - max(ρ₃(H), min(|H|, 2))`. -/
theorem finrank_ker_le_matching_rho3 {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 4) :
    finrank F (LinearMap.ker M.mulVecLin) + max (rho3 G (heavyVerts M)) (min (heavyVerts M).card 2) ≤
      G.matchingNumber + (heavyVerts M).card := by
  rcases le_total (rho3 G (heavyVerts M)) (min (heavyVerts M).card 2) with hle | hle
  · rw [max_eq_right hle]
    obtain ⟨D, hD, hc⟩ := exists_subset_card_eq (show min (heavyVerts M).card 2 ≤ (heavyVerts M).card
      from min_le_left _ _)
    rw [← hc]
    exact finrank_ker_add_card_le_matching_graph hdiag hpat htri hdeg hD
      (Or.inl (by rw [hc]; exact min_le_right _ _))
  · rw [max_eq_left hle]
    obtain ⟨D, hD, hfar, hc⟩ := exists_rho3 G (heavyVerts M)
    rw [← hc]
    exact finrank_ker_add_card_le_matching_graph hdiag hpat htri hdeg hD (Or.inr hfar)

/-- **Corollary SH, matching form as stated, transpose**: the same with the heavy set of `Mᵀ`. -/
theorem finrank_ker_le_matching_rho3_transpose {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 4) :
    finrank F (LinearMap.ker M.mulVecLin) +
        max (rho3 G (heavyVerts M.transpose)) (min (heavyVerts M.transpose).card 2) ≤
      G.matchingNumber + (heavyVerts M.transpose).card := by
  rw [← finrank_ker_transpose]
  refine finrank_ker_le_matching_rho3 (M := M.transpose)
    (fun v => by rw [Matrix.transpose_apply, hdiag v]) (fun v u hvu hadj => ?_) htri hdeg
  rw [Matrix.transpose_apply]
  exact hpat u v (Ne.symm hvu) fun h => hadj h.symm

end Corollary

end BoundedNesting
