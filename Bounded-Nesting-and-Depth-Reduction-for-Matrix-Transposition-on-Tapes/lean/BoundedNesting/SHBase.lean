import MotionDepthCodes.Subcubic

/-!
# Theorem SH: the minimal counterexample

The setting of Theorem SH (`sec:crux-deg4`), with the codes on vertex subsets of paper 4
(`MotionDepthCodes.subCode`, `zeroOn`, `recSet`). For a vertex set `W`, the recovery set of `v` on
`W` is `rs M W v = S_v ∩ W`; (★★) and (★4) on `W` are `StarOn` and `Star4On`; the heavy vertices on
`W` are `heavySet M W`; (S1) and (S2) on `W` are `S1On`, `S2On`; and `SHOn M W` collects the
hypotheses of Theorem SH on `W`. They are hereditary (`SHOn.mono`).

For a minimal counterexample `W` (`MinCE`), with code `C = subCode M W`, the paper's explorations are
replaced by codes: `cdim M W X` is the dimension of the codewords vanishing on `X`, at most
`⌊(|W| - |X|)/2⌋` (`MinCE.ub`), and `X` is a *good state* if equality holds (`Good`); this is the
paper's `Φ = 0`. A move `(r, P_X(r))` lowers `cdim` by at most `|P_X(r)| - 1` (`cdim_move`), which
gives the table of neutral moves (`MinCE.good_move`, `MinCE.single_odd_false`). At a neutral move
the code vanishing on `X` restricts onto the whole hyperplane of the mover's row, which gives test
vectors (`test_vec`) and immediate closure (`imm_closure`). Lemma "axioms": `MinCE.two_le_rs` (c),
`MinCE.out_card` (d), and (b) in the code form `MinCE.ub`; Lemma "tools": the pending bounds
`St.pend_light`, `St.pend_le_three` (a), immediate closure (b), and the Hall count
`MinCE.hall_count` (c). States of runs from `v₀` are `St`.
-/

namespace BoundedNesting

open Finset Module MotionDepthCodes

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

/-! ### Relative notions -/

section Relative

variable (M : Matrix V V F) (W : Finset V)

/-- The recovery set of `v` on `W`. -/
def rs (v : V) : Finset V := recSet M v ∩ W

/-- The pending set of `u` at `X`: its recovery set on `W` outside `X`. -/
def pend (X : Finset V) (u : V) : Finset V := rs M W u \ X

/-- (★★) on `W`. -/
def StarOn (v : V) : Prop :=
  (rs M W v).card ≤ 2 ∨ ((rs M W v).card = 3 ∧ ∀ r ∈ W, v ∈ rs M W r → r ∈ rs M W v)

instance (v : V) : Decidable (StarOn M W v) := by unfold StarOn; infer_instance

/-- (★4) on `W`. -/
def Star4On (v : V) : Prop :=
  (rs M W v).card ≤ 3 ∨ ((rs M W v).card = 4 ∧ ∀ r ∈ W, v ∈ rs M W r → r ∈ rs M W v)

/-- The heavy vertices on `W`: the vertices of `W` violating (★★) on `W`. -/
def heavySet : Finset V := W.filter fun v => ¬ StarOn M W v

/-- (S1) on `W`: no vertex has two heavy vertices in its recovery set. -/
def S1On : Prop :=
  ∀ v ∈ W, ∀ p ∈ rs M W v, ∀ q ∈ rs M W v, p ≠ q → p ∈ heavySet M W → q ∉ heavySet M W

/-- (S2) on `W`: no heavy vertex has a heavy vertex in its recovery set. -/
def S2On : Prop := ∀ g ∈ heavySet M W, ∀ u ∈ rs M W g, u ∉ heavySet M W

/-- The hypotheses of Theorem SH on `W`: (★4) everywhere, and at most two heavy vertices or
(S1) and (S2). -/
def SHOn : Prop :=
  (∀ v ∈ W, Star4On M W v) ∧ ((heavySet M W).card ≤ 2 ∨ (S1On M W ∧ S2On M W))

end Relative

section Heredity

variable {M : Matrix V V F} {W W' : Finset V}

theorem rs_mono (h : W' ⊆ W) (v : V) : rs M W' v ⊆ rs M W v := inter_subset_inter_left h

theorem rs_subset (v : V) : rs M W v ⊆ W := inter_subset_right

theorem not_mem_rs (v : V) : v ∉ rs M W v := fun h => (mem_recSet.mp (mem_inter.mp h).1).1 rfl

theorem StarOn.mono (h : W' ⊆ W) {v : V} (hs : StarOn M W v) : StarOn M W' v := by
  have hc := card_le_card (rs_mono (M := M) h v)
  rcases hs with h2 | ⟨h3, hrec⟩
  · exact Or.inl (by omega)
  · by_cases h2 : (rs M W' v).card ≤ 2
    · exact Or.inl h2
    · refine Or.inr ⟨by omega, fun r hr hv => ?_⟩
      exact mem_inter.mpr ⟨(mem_inter.mp (hrec r (h hr) (rs_mono h r hv))).1, hr⟩

theorem Star4On.mono (h : W' ⊆ W) {v : V} (hs : Star4On M W v) : Star4On M W' v := by
  have hc := card_le_card (rs_mono (M := M) h v)
  rcases hs with h3 | ⟨h4, hrec⟩
  · exact Or.inl (by omega)
  · by_cases h3 : (rs M W' v).card ≤ 3
    · exact Or.inl h3
    · refine Or.inr ⟨by omega, fun r hr hv => ?_⟩
      exact mem_inter.mpr ⟨(mem_inter.mp (hrec r (h hr) (rs_mono h r hv))).1, hr⟩

theorem heavySet_mono (h : W' ⊆ W) : heavySet M W' ⊆ heavySet M W := by
  intro v hv
  obtain ⟨hvW', hns⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨h hvW', fun hs => hns (hs.mono h)⟩

theorem SHOn.mono (h : W' ⊆ W) (hs : SHOn M W) : SHOn M W' := by
  refine ⟨fun v hv => (hs.1 v (h hv)).mono h, ?_⟩
  rcases hs.2 with hc | ⟨h1, h2⟩
  · exact Or.inl ((card_le_card (heavySet_mono h)).trans hc)
  · refine Or.inr ⟨fun v hv p hp q hq hpq hph hqh => ?_, fun g hg u hu huh => ?_⟩
    · exact h1 v (h hv) p (rs_mono h v hp) q (rs_mono h v hq) hpq (heavySet_mono h hph)
        (heavySet_mono h hqh)
    · exact h2 g (heavySet_mono h hg) u (rs_mono h g hu) (heavySet_mono h huh)

theorem pend_subset_rs (X : Finset V) (u : V) : pend M W X u ⊆ rs M W u := sdiff_subset

theorem pend_subset (X : Finset V) (u : V) : pend M W X u ⊆ W := sdiff_subset.trans inter_subset_right

theorem disjoint_pend (X : Finset V) (u : V) : Disjoint X (pend M W X u) := disjoint_sdiff

theorem pend_anti {X X' : Finset V} (h : X ⊆ X') (u : V) : pend M W X' u ⊆ pend M W X u :=
  sdiff_subset_sdiff le_rfl h

end Heredity

/-! ### Rows -/

section Rows

variable {M : Matrix V V F} {W : Finset V}

/-- The row of `v ∈ W` on a codeword of `W`, over the recovery set on `W`. -/
theorem row_rs (hyp : ThmSHyp M) {x : V → F} (hx : x ∈ subCode M W) {v : V} (hv : v ∈ W) :
    x v + ∑ u ∈ rs M W v, M v u * x u = 0 := by
  have h := row_sum_eq_zero hx hv (insert v (rs M W v)) (by
    intro u hMu hxu
    by_cases huv : u = v
    · rw [huv]
      exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_inter.mpr ⟨mem_recSet.mpr ⟨huv, hMu⟩, ?_⟩)
      by_contra hu
      exact hxu (hx.1 u hu))
  rw [sum_insert (not_mem_rs v), hyp.diag, one_mul] at h
  exact h

/-- A codeword vanishing on the recovery set of `v` vanishes at `v`. -/
theorem zero_of_rs (hyp : ThmSHyp M) {x : V → F} (hx : x ∈ subCode M W) {v : V} (hv : v ∈ W)
    (h : ∀ u ∈ rs M W v, x u = 0) : x v = 0 := by
  have := row_rs hyp hx hv
  rwa [sum_eq_zero (fun u hu => by rw [h u hu, mul_zero]), add_zero] at this

/-- A codeword vanishing at `v` and on its recovery set except at `u` vanishes at `u`. -/
theorem zero_of_rs_but (hyp : ThmSHyp M) {x : V → F} (hx : x ∈ subCode M W) {v : V} (hv : v ∈ W)
    {u : V} (hu : u ∈ rs M W v) (hxv : x v = 0) (h : ∀ u' ∈ rs M W v, u' ≠ u → x u' = 0) :
    x u = 0 := by
  have := row_rs hyp hx hv
  rw [hxv, zero_add, ← sum_erase_add _ _ hu,
    sum_eq_zero (fun u' hu' => by rw [h u' (mem_of_mem_erase hu') (ne_of_mem_erase hu'), mul_zero]),
    zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left (mem_recSet.mp (mem_inter.mp hu).1).2

end Rows

/-! ### The code dimension of a state -/

/-- The dimension of the codewords of `W` vanishing on `X`. -/
noncomputable def cdim (M : Matrix V V F) (W X : Finset V) : ℕ :=
  finrank F (subCode M W ⊓ zeroOn X : Submodule F (V → F))

/-- A good state: the codewords vanishing on `X` have the largest dimension that the minimality of
`W` allows. -/
def Good (M : Matrix V V F) (W X : Finset V) : Prop := cdim M W X = (W.card - X.card) / 2

section Moves

variable {M : Matrix V V F} {W X : Finset V}

omit [DecidableEq F] in
/-- The restriction to `U` lowers the code dimension by at most `|U|`. -/
theorem cdim_le_card_add (X U : Finset V) : cdim M W X ≤ U.card + cdim M W (X ∪ U) := by
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W ⊓ zeroOn X) U
  have hle : subCode M W ⊓ zeroOn X ⊓ zeroOn U ≤ subCode M W ⊓ zeroOn (X ∪ U) := by
    rintro x ⟨⟨hx, hxX⟩, hxU⟩
    refine ⟨hx, fun u hu => ?_⟩
    rcases mem_union.mp hu with hu | hu
    · exact hxX u hu
    · exact hxU u hu
  have h2 := Submodule.finrank_mono hle
  unfold cdim
  omega

/-- **A move.** The row of the mover makes one pending coordinate determined by the others. -/
theorem cdim_move (hyp : ThmSHyp M) (hXW : X ⊆ W) {r : V} (hr : r ∈ X) {u₀ : V}
    (hu₀ : u₀ ∈ pend M W X r) :
    cdim M W X ≤ ((pend M W X r).card - 1) + cdim M W (X ∪ pend M W X r) := by
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W ⊓ zeroOn X)
    ((pend M W X r).erase u₀)
  have hle : subCode M W ⊓ zeroOn X ⊓ zeroOn ((pend M W X r).erase u₀) ≤
      subCode M W ⊓ zeroOn (X ∪ pend M W X r) := by
    rintro x ⟨⟨hx, hxX⟩, hxP⟩
    refine ⟨hx, fun u hu => ?_⟩
    rcases mem_union.mp hu with hu | hu
    · exact hxX u hu
    · by_cases hu' : u = u₀
      · subst hu'
        refine zero_of_rs_but hyp hx (hXW hr) (mem_sdiff.mp hu).1 (hxX r hr) (fun u' hu' hne => ?_)
        by_cases hu'X : u' ∈ X
        · exact hxX u' hu'X
        · exact hxP u' (mem_erase.mpr ⟨hne, mem_sdiff.mpr ⟨hu', hu'X⟩⟩)
      · exact hxP u (mem_erase.mpr ⟨hu', hu⟩)
  have h2 := Submodule.finrank_mono hle
  rw [card_erase_of_mem hu₀] at h1
  unfold cdim
  omega

end Moves

omit [Fintype V] [DecidableEq F] in
/-- The restriction to `I`, as a linear map. -/
theorem exists_restrict (I : Finset V) : ∃ φ : (V → F) →ₗ[F] (V → F),
    ∀ x u, φ x u = if u ∈ I then x u else 0 :=
  ⟨{ toFun := fun x u => if u ∈ I then x u else 0
     map_add' := fun x y => by
       funext u
       by_cases hu : u ∈ I <;> simp [hu]
     map_smul' := fun c x => by
       funext u
       by_cases hu : u ∈ I <;> simp [hu] }, fun _ _ => rfl⟩

/-! ### A minimal counterexample -/

/-- `W` is a minimal counterexample to the half bound. -/
structure MinCE (M : Matrix V V F) (W : Finset V) : Prop where
  ih : ∀ t ⊂ W, finrank F (subCode M t) ≤ t.card / 2
  lt : W.card / 2 < finrank F (subCode M W)

section MinCE

variable {M : Matrix V V F} {W : Finset V} (hW : MinCE M W)
include hW

omit [DecidableEq F] in
theorem MinCE.odd : Odd W.card := (start_facts hW.ih hW.lt).1

omit [DecidableEq F] in
theorem MinCE.dim : finrank F (subCode M W) = W.card / 2 + 1 := (start_facts hW.ih hW.lt).2.1

omit [DecidableEq F] in
/-- Singletons are good states. -/
theorem MinCE.single {v : V} (hv : v ∈ W) : Good M W {v} := by
  obtain ⟨-, -, h⟩ := start_facts hW.ih hW.lt
  unfold Good cdim
  rw [← (h v hv).1, (h v hv).2, card_singleton]
  obtain ⟨k, hk⟩ := hW.odd
  omega

omit [DecidableEq F] in
/-- **Lemma "axioms" (b), code form.** The codewords vanishing on a nonempty `X ⊆ W` have dimension
at most `⌊(|W| - |X|)/2⌋`. -/
theorem MinCE.ub {X : Finset V} (hXW : X ⊆ W) (hX : X.Nonempty) :
    cdim M W X ≤ (W.card - X.card) / 2 := by
  refine (Submodule.finrank_mono (subCode_inf_zeroOn_le M W X)).trans ?_
  have := hW.ih (W \ X) (sdiff_ssubset hXW hX)
  rwa [card_sdiff_of_subset hXW] at this

/-- **Neutral moves.** From a good state, a move with a pending pair, with a single pending vertex at
an even state, or with a pending triple at an odd state, reaches a good state, and the code
dimension drops by exactly `|P| - 1`. -/
theorem MinCE.good_move (hyp : ThmSHyp M) {X : Finset V} (hXW : X ⊆ W) (hg : Good M W X) {r : V}
    (hr : r ∈ X) (hneut : (pend M W X r).card = 2 ∨ ((pend M W X r).card = 1 ∧ Even X.card) ∨
      ((pend M W X r).card = 3 ∧ Odd X.card)) :
    Good M W (X ∪ pend M W X r) ∧
      cdim M W X = ((pend M W X r).card - 1) + cdim M W (X ∪ pend M W X r) := by
  have hne : (pend M W X r).Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨u₀, hu₀⟩ := hne
  have hm := cdim_move hyp hXW hr hu₀
  have hsub : X ∪ pend M W X r ⊆ W := union_subset hXW (pend_subset X r)
  have hub := hW.ub hsub ⟨r, mem_union_left _ hr⟩
  have hcard : (X ∪ pend M W X r).card = X.card + (pend M W X r).card :=
    card_union_of_disjoint (disjoint_pend X r)
  have hcW := card_le_card hsub
  obtain ⟨k, hk⟩ := hW.odd
  unfold Good at hg ⊢
  rw [hcard] at hub hcW ⊢
  rcases hneut with h2 | ⟨h1, ⟨a, ha⟩⟩ | ⟨h3, ⟨a, ha⟩⟩ <;> constructor <;> omega

/-- A single pending vertex at an odd good state is a contradiction. -/
theorem MinCE.single_odd_false (hyp : ThmSHyp M) {X : Finset V} (hXW : X ⊆ W) (hg : Good M W X)
    {r : V} (hr : r ∈ X) (h1 : (pend M W X r).card = 1) (hodd : Odd X.card) : False := by
  obtain ⟨u₀, hu₀⟩ : (pend M W X r).Nonempty := by
    rw [← card_pos]
    omega
  have hm := cdim_move hyp hXW hr hu₀
  have hsub : X ∪ pend M W X r ⊆ W := union_subset hXW (pend_subset X r)
  have hub := hW.ub hsub ⟨r, mem_union_left _ hr⟩
  have hcard : (X ∪ pend M W X r).card = X.card + (pend M W X r).card :=
    card_union_of_disjoint (disjoint_pend X r)
  have hcW := card_le_card hsub
  obtain ⟨k, hk⟩ := hW.odd
  obtain ⟨a, ha⟩ := hodd
  unfold Good at hg
  rw [hcard] at hub hcW
  omega

/-- **Lemma "axioms" (c).** Every vertex of a minimal counterexample has at least two recovery
neighbours on `W`. -/
theorem MinCE.two_le_rs (hyp : ThmSHyp M) {v : V} (hv : v ∈ W) : 2 ≤ (rs M W v).card := by
  by_contra hlt
  push Not at hlt
  have hpend : pend M W {v} v = rs M W v := by
    ext u
    simp only [pend, mem_sdiff, mem_singleton, and_iff_left_iff_imp]
    rintro hu rfl
    exact not_mem_rs u hu
  rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
  · have hempty : rs M W v = ∅ := card_eq_zero.mp (by omega)
    have hle : subCode M W ≤ subCode M W ⊓ zeroOn {v} := by
      intro x hx
      refine ⟨hx, fun u hu => ?_⟩
      rw [mem_singleton.mp hu]
      exact zero_of_rs hyp hx hv (by simp [hempty])
    have h1 := Submodule.finrank_mono hle
    have h2 := hW.single hv
    have h3 := hW.dim
    unfold Good cdim at h2
    rw [card_singleton] at h2
    obtain ⟨k, hk⟩ := hW.odd
    omega
  · exact hW.single_odd_false hyp (singleton_subset_iff.mpr hv) (hW.single hv) (mem_singleton_self v)
      (by rw [hpend, h1]) (by simp)

/-- **Lemma "tools" (c), the Hall count.** If no vertex of a nonempty `I ⊆ W` points to another,
then `|I ∪ ⋃_{v ∈ I} S_v| ≥ 2|I| + 1`. -/
theorem MinCE.hall_count (hyp : ThmSHyp M) {I : Finset V} (hIW : I ⊆ W) (hI : I.Nonempty)
    (hind : ∀ v ∈ I, ∀ v' ∈ I, v' ∉ recSet M v) :
    2 * I.card + 1 ≤ (I ∪ I.biUnion (rs M W)).card := by
  set U := I ∪ I.biUnion (rs M W)
  have hUW : U ⊆ W := union_subset hIW (biUnion_subset.mpr fun v _ => rs_subset v)
  have hIU : I ⊆ U := subset_union_left
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W) (U \ I)
  have hle : subCode M W ⊓ zeroOn (U \ I) ≤ subCode M W ⊓ zeroOn U := by
    rintro x ⟨hx, hxU⟩
    refine ⟨hx, fun v hv => ?_⟩
    by_cases hvI : v ∈ I
    · refine zero_of_rs hyp hx (hIW hvI) (fun u hu => hxU u (mem_sdiff.mpr ⟨?_, ?_⟩))
      · exact mem_union_right _ (mem_biUnion.mpr ⟨v, hvI, hu⟩)
      · intro huI
        exact hind v hvI u huI (mem_inter.mp hu).1
    · exact hxU v (mem_sdiff.mpr ⟨hv, hvI⟩)
  have h2 := Submodule.finrank_mono hle
  have h3 := hW.ub hUW (hI.mono hIU)
  have h4 := hW.dim
  have h5 := card_sdiff_of_subset hIU
  have h6 := card_le_card hUW
  have h7 := card_le_card hIU
  unfold cdim at h3
  obtain ⟨k, hk⟩ := hW.odd
  omega

/-- **Lemma "axioms" (d).** For a nonempty `X ⊊ W`, the vertices of `X` with a recovery neighbour
outside `X` number at least two if `|X|` is even and at least one if `|X|` is odd. -/
theorem MinCE.out_card {X : Finset V} (hXW : X ⊆ W) (hX : X.Nonempty)
    (hXne : X ≠ W) :
    (Even X.card → 2 ≤ (X.filter fun v => ¬ rs M W v ⊆ X).card) ∧
      (Odd X.card → 1 ≤ (X.filter fun v => ¬ rs M W v ⊆ X).card) := by
  set O := X.filter fun v => ¬ rs M W v ⊆ X
  set I := X.filter fun v => rs M W v ⊆ X
  have hIO : I.card + O.card = X.card := card_filter_add_card_filter_not _
  have hIW : I ⊂ W := (filter_subset _ _).trans_ssubset (ssubset_of_subset_of_ne hXW hXne)
  have hIX : I ⊆ X := filter_subset _ _
  have hOX : O ⊆ X := filter_subset _ _
  obtain ⟨φ, hφ⟩ := exists_restrict (F := F) I
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W) O
  set Q := subCode M W ⊓ zeroOn O
  -- `φ` maps `Q` into the code of `I`, with kernel the codewords vanishing on `X`
  have hmap : Q.map φ ≤ subCode M I := by
    rintro _ ⟨x, ⟨hx, hxO⟩, rfl⟩
    refine ⟨fun u hu => by rw [hφ]; simp [hu], fun v hv => ?_⟩
    have hvW : v ∈ W := hIW.subset hv
    have hvX : rs M W v ⊆ X := (mem_filter.mp hv).2
    have hterm : ∀ u, M v u * φ x u = M v u * x u := by
      intro u
      rw [hφ]
      by_cases huI : u ∈ I
      · simp [huI]
      · simp only [huI, ↓reduceIte, mul_zero]
        by_cases hM : M v u = 0
        · rw [hM, zero_mul]
        · by_cases huW : u ∈ W
          · have huv : u ≠ v := fun e => huI (e ▸ hv)
            have hurs : u ∈ rs M W v := mem_inter.mpr ⟨mem_recSet.mpr ⟨huv, hM⟩, huW⟩
            have huO : u ∈ O := mem_filter.mpr ⟨hvX hurs, fun h => huI (mem_filter.mpr ⟨hvX hurs, h⟩)⟩
            rw [hxO u huO, mul_zero]
          · rw [hx.1 u huW, mul_zero]
    simp only [hterm]
    exact hx.2 v hvW
  have hker : ∀ x ∈ Q, φ x = 0 → x ∈ subCode M W ⊓ zeroOn X := by
    rintro x ⟨hx, hxO⟩ h0
    refine ⟨hx, fun u hu => ?_⟩
    by_cases huI : u ∈ I
    · have := congrFun h0 u
      rw [hφ] at this
      simpa [huI] using this
    · exact hxO u (mem_filter.mpr ⟨hu, fun h => huI (mem_filter.mpr ⟨hu, h⟩)⟩)
  have hrk := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict Q)
  rw [LinearMap.range_domRestrict] at hrk
  have hk1 := Submodule.finrank_mono hmap
  have hk2 : finrank F (LinearMap.ker (φ.domRestrict Q)) ≤ cdim M W X := by
    rw [← Submodule.finrank_map_subtype_eq Q (LinearMap.ker (φ.domRestrict Q))]
    refine Submodule.finrank_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hker y.1 y.2 hy
  have h2 := hW.ih I hIW
  have h3 := hW.ub hXW hX
  have h4 := hW.dim
  have h5 := card_le_card hXW
  obtain ⟨k, hk⟩ := hW.odd
  refine ⟨fun ⟨a, ha⟩ => ?_, fun ⟨a, ha⟩ => ?_⟩ <;> omega

end MinCE

/-! ### Test vectors and immediate closure -/

section Closure

variable {M : Matrix V V F} {W X : Finset V}

/-- **Test vectors.** At a move whose code dimension drops by exactly `|P| - 1`, for two pending
vertices `u ≠ u'` some codeword vanishes on `X` and on the other pending vertices but not at `u`. -/
theorem test_vec (hyp : ThmSHyp M) (hXW : X ⊆ W) {r : V} (hr : r ∈ X)
    (hdrop : cdim M W X = ((pend M W X r).card - 1) + cdim M W (X ∪ pend M W X r)) {u u' : V}
    (hu : u ∈ pend M W X r) (hu' : u' ∈ pend M W X r) (huu : u ≠ u') :
    ∃ x ∈ subCode M W, (∀ v ∈ X, x v = 0) ∧ (∀ v ∈ pend M W X r, v ≠ u → v ≠ u' → x v = 0) ∧
      x u ≠ 0 := by
  set E := ((pend M W X r).erase u).erase u'
  have hE : E.card = (pend M W X r).card - 2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm huu, hu'⟩), card_erase_of_mem hu]
    omega
  have h2 : 2 ≤ (pend M W X r).card := by
    have : ({u, u'} : Finset V) ⊆ pend M W X r := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hu
      · exact hu'
    have := card_le_card this
    rwa [card_pair huu] at this
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W ⊓ zeroOn X) E
  by_contra hno
  push Not at hno
  have hle : subCode M W ⊓ zeroOn X ⊓ zeroOn E ≤ subCode M W ⊓ zeroOn (X ∪ pend M W X r) := by
    rintro x ⟨⟨hx, hxX⟩, hxE⟩
    have hxu : x u = 0 := hno x hx hxX (fun v hv hvu hvu' =>
      hxE v (mem_erase.mpr ⟨hvu', mem_erase.mpr ⟨hvu, hv⟩⟩))
    refine ⟨hx, fun v hv => ?_⟩
    rcases mem_union.mp hv with hv | hv
    · exact hxX v hv
    · by_cases hvu : v = u
      · rw [hvu]
        exact hxu
      by_cases hvu' : v = u'
      · rw [hvu']
        refine zero_of_rs_but hyp hx (hXW hr) (mem_sdiff.mp hu').1 (hxX r hr) (fun w hw hne => ?_)
        by_cases hwX : w ∈ X
        · exact hxX w hwX
        · by_cases hwu : w = u
          · rw [hwu]
            exact hxu
          · exact hxE w (mem_erase.mpr ⟨hne, mem_erase.mpr ⟨hwu, mem_sdiff.mpr ⟨hw, hwX⟩⟩⟩)
      · exact hxE v (mem_erase.mpr ⟨hvu', mem_erase.mpr ⟨hvu, hv⟩⟩)
  have h3 := Submodule.finrank_mono hle
  unfold cdim at hdrop
  omega

/-- **Immediate closure.** After a move with at least two pending vertices whose code dimension
drops by exactly `|P| - 1`, every member of the block has a pending vertex. -/
theorem imm_closure (hyp : ThmSHyp M) (hXW : X ⊆ W) {r : V} (hr : r ∈ X)
    (hdrop : cdim M W X = ((pend M W X r).card - 1) + cdim M W (X ∪ pend M W X r))
    (h2 : 2 ≤ (pend M W X r).card) {w : V} (hw : w ∈ pend M W X r) :
    (pend M W (X ∪ pend M W X r) w).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty, pend, sdiff_eq_empty_iff_subset] at hne
  obtain ⟨u', hu', hne'⟩ := exists_mem_ne (show 1 < (pend M W X r).card by omega) w
  have hwr : w ∈ recSet M r := (mem_inter.mp (pend_subset_rs X r hw)).1
  have hu'r : u' ∈ recSet M r := (mem_inter.mp (pend_subset_rs X r hu')).1
  have hu'w : u' ∉ recSet M w := hyp.triangleFree r w u' hwr hu'r
  obtain ⟨x, hx, hxX, hxP, hxw⟩ := test_vec hyp hXW hr hdrop hw hu' (Ne.symm hne')
  refine hxw (zero_of_rs hyp hx (pend_subset X r hw) fun v hv => ?_)
  rcases mem_union.mp (hne hv) with hv' | hv'
  · exact hxX v hv'
  · refine hxP v hv' (fun e => not_mem_rs w (e ▸ hv)) (fun e => hu'w ?_)
    rw [← e]
    exact (mem_inter.mp hv).1

end Closure

/-! ### States of runs -/

/-- A state of a neutral run from `v₀` on `W`: a good state containing `v₀` and its recovery set
(at least one move has been made), in which every other vertex has a parent pointing to it. -/
structure St (M : Matrix V V F) (W : Finset V) (v₀ : V) (X : Finset V) : Prop where
  sub : X ⊆ W
  good : Good M W X
  mem : v₀ ∈ X
  closed : rs M W v₀ ⊆ X
  parent : ∀ u ∈ X, u ≠ v₀ → ∃ r ∈ X, u ∈ rs M W r

section States

variable {M : Matrix V V F} {W X : Finset V} {v₀ : V}

theorem St.nonempty (h : St M W v₀ X) : X.Nonempty := ⟨v₀, h.mem⟩

/-- A neutral move from a state reaches a state. -/
theorem St.move (hW : MinCE M W) (hyp : ThmSHyp M) (h : St M W v₀ X) {r : V} (hr : r ∈ X)
    (hneut : (pend M W X r).card = 2 ∨ ((pend M W X r).card = 1 ∧ Even X.card) ∨
      ((pend M W X r).card = 3 ∧ Odd X.card)) :
    St M W v₀ (X ∪ pend M W X r) ∧
      cdim M W X = ((pend M W X r).card - 1) + cdim M W (X ∪ pend M W X r) := by
  obtain ⟨hg, hdrop⟩ := hW.good_move hyp h.sub h.good hr hneut
  refine ⟨⟨union_subset h.sub (pend_subset X r), hg, mem_union_left _ h.mem,
    h.closed.trans subset_union_left, fun u hu huv => ?_⟩, hdrop⟩
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨r', hr', hur'⟩ := h.parent u hu huv
    exact ⟨r', mem_union_left _ hr', hur'⟩
  · exact ⟨r, mem_union_left _ hr, pend_subset_rs X r hu⟩

/-- The first move, from `{v₀}` with two or three recovery neighbours. -/
theorem St.first (hW : MinCE M W) (hyp : ThmSHyp M) (hv₀ : v₀ ∈ W)
    (h23 : (rs M W v₀).card = 2 ∨ (rs M W v₀).card = 3) :
    St M W v₀ (insert v₀ (rs M W v₀)) ∧ pend M W {v₀} v₀ = rs M W v₀ ∧
      cdim M W {v₀} = ((rs M W v₀).card - 1) + cdim M W (insert v₀ (rs M W v₀)) := by
  have hpend : pend M W {v₀} v₀ = rs M W v₀ := by
    ext u
    simp only [pend, mem_sdiff, mem_singleton, and_iff_left_iff_imp]
    rintro hu rfl
    exact not_mem_rs u hu
  have hins : ({v₀} : Finset V) ∪ rs M W v₀ = insert v₀ (rs M W v₀) := by
    rw [insert_eq]
  obtain ⟨hg, hdrop⟩ := hW.good_move hyp (singleton_subset_iff.mpr hv₀) (hW.single hv₀)
    (mem_singleton_self v₀) (by
      rw [hpend]
      rcases h23 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨h, by simp⟩))
  rw [hpend, hins] at hg hdrop
  refine ⟨⟨insert_subset hv₀ (rs_subset v₀), hg, mem_insert_self _ _, subset_insert _ _,
    fun u hu huv => ⟨v₀, mem_insert_self _ _, ?_⟩⟩, hpend, hdrop⟩
  rcases mem_insert.mp hu with rfl | hu
  · exact absurd rfl huv
  · exact hu

theorem St.pend_start (h : St M W v₀ X) : pend M W X v₀ = ∅ :=
  sdiff_eq_empty_iff_subset.mpr h.closed

/-- **Lemma "tools" (a), light vertices.** A light vertex other than `v₀` has at most two pending
vertices. -/
theorem St.pend_light (h : St M W v₀ X) {u : V} (hu : u ∈ X) (huv : u ≠ v₀) (hl : StarOn M W u) :
    (pend M W X u).card ≤ 2 := by
  rcases hl with h2 | ⟨h3, hrec⟩
  · exact (card_le_card (pend_subset_rs X u)).trans h2
  · obtain ⟨r, hr, hur⟩ := h.parent u hu huv
    have hrS : r ∈ rs M W u := hrec r (h.sub hr) hur
    calc (pend M W X u).card ≤ ((rs M W u).erase r).card := by
          refine card_le_card fun w hw => mem_erase.mpr ⟨?_, pend_subset_rs X u hw⟩
          rintro rfl
          exact (mem_sdiff.mp hw).2 hr
      _ = 2 := by rw [card_erase_of_mem hrS, h3]

/-- **Lemma "tools" (a), all vertices.** Under (★4), a vertex other than `v₀` has at most three
pending vertices. -/
theorem St.pend_le_three (h : St M W v₀ X) {u : V} (hu : u ∈ X) (huv : u ≠ v₀)
    (h4 : Star4On M W u) : (pend M W X u).card ≤ 3 := by
  rcases h4 with h3 | ⟨h4, hrec⟩
  · exact (card_le_card (pend_subset_rs X u)).trans h3
  · obtain ⟨r, hr, hur⟩ := h.parent u hu huv
    have hrS : r ∈ rs M W u := hrec r (h.sub hr) hur
    calc (pend M W X u).card ≤ ((rs M W u).erase r).card := by
          refine card_le_card fun w hw => mem_erase.mpr ⟨?_, pend_subset_rs X u hw⟩
          rintro rfl
          exact (mem_sdiff.mp hw).2 hr
      _ = 3 := by rw [card_erase_of_mem hrS, h4]

end States

/-! ### Non-closed heavy vertices -/

/-- The heavy vertices on `W` that are not closed at `X`: outside `X` or with a pending vertex. -/
def NC (M : Matrix V V F) (W X : Finset V) : Finset V :=
  (heavySet M W).filter fun g => g ∉ X ∨ (pend M W X g).Nonempty

theorem NC_anti {M : Matrix V V F} {W X X' : Finset V} (h : X ⊆ X') : NC M W X' ⊆ NC M W X := by
  intro g hg
  obtain ⟨hgH, hg'⟩ := mem_filter.mp hg
  refine mem_filter.mpr ⟨hgH, ?_⟩
  rcases hg' with hg' | ⟨u, hu⟩
  · exact Or.inl fun hgX => hg' (h hgX)
  · by_cases hgX : g ∈ X
    · exact Or.inr ⟨u, pend_anti h g hu⟩
    · exact Or.inl hgX

theorem NC_subset {M : Matrix V V F} {W X : Finset V} : NC M W X ⊆ heavySet M W := filter_subset _ _

end BoundedNesting
