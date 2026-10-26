import BoundedNesting.MCost

/-!
# The cost of the label of Theorem M

For a residue `ρ` and offsets `ω = (ω₀, ωd, ωe)` (`offsets`), the cut consists of the edges at the
level-`0` line times `Zt` (all of them), the violated hop edges (`cutHM`), and the state edges at
descents (`cutSM`). Its hop edges are those of the chords of `x0` and of the hops of the bounded
walks (`Eall`).

* `card_cut_le`: the cut is covered by the edges at line times, the descents between non-line times,
  the violated chords at non-line cells and the violated hops of the bounded walks.
* `desc_subset`, `chord_subset`, `ahop_subset`: each of these needs a wrap of a digit (or, for a hop of
  window `j`, a visit of head `0` to a level-`(j+1)` line).
* `card_offsets_wrap0`, `card_offsets_wrapD`, `card_offsets_wrapE`: the offsets at which a digit whose count rises by `Δ`
  wraps number at most `Δ` times the other offsets.
-/

namespace BoundedNesting

open Finset

section Sets

variable {ι : Type*} [Fintype ι] {N : ℕ}
variable (x0 : ℕ → ℤ) (W : ℕ → ℕ) (ρ : ℕ) (A : Fam ι N) (T : ℕ)

/-- The level-`0` line times. -/
def Zt : Finset ℕ := (range T).filter fun t => LineAt W ρ 0 (x0 t)

/-- The level-`i` line times. -/
def lineT (i : ℕ) : Finset ℕ := (range T).filter fun t => LineAt W ρ i (x0 t)

/-- The hop edges of `G`: the chords of `x0` and the hops of the bounded walks. -/
def Eall : Finset (ℕ × ℕ) := hops x0 T ∪ A.H.image fun η => η.2

/-- The offsets `(ω₀, ωd, ωe)`. -/
def offsets (K₀ K q : ℕ) : Finset (ℕ × (Fin q → ℕ) × (Fin q → ℕ)) :=
  range K₀ ×ˢ (Fintype.piFinset (fun _ : Fin q => range K) ×ˢ
    Fintype.piFinset (fun _ : Fin q => range K))

variable {q : ℕ} (β : Fin q → ℕ) (K₀ K : ℕ)

open Classical in
/-- The cut state edges `t → t - 1`: at a line time, or at a descent. -/
noncomputable def cutSM (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) : Finset ℕ :=
  (Ico 1 T).filter fun t => t ∈ Zt x0 W ρ T ∨ t - 1 ∈ Zt x0 W ρ T ∨
    mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (t - 1)

open Classical in
/-- The cut hop edges `u → p`: at a line time, or violated. -/
noncomputable def cutHM (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) : Finset (ℕ × ℕ) :=
  (Eall x0 A T).filter fun e => e.1 ∈ Zt x0 W ρ T ∨ e.2 ∈ Zt x0 W ρ T ∨
    mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.1

end Sets

/-! ### Counting offsets -/

section Offsets

theorem card_offsets (K₀ K q : ℕ) : (offsets K₀ K q).card = K₀ * (K ^ q * K ^ q) := by
  simp [offsets, card_product, Fintype.card_piFinset]

theorem card_offsets_wrap0 {K₀ K q : ℕ} (hK₀ : 0 < K₀) {n n' : ℕ} (h : n ≤ n') :
    ((offsets K₀ K q).filter fun ω => (n + ω.1) / K₀ ≠ (n' + ω.1) / K₀).card ≤
      (n' - n) * (K ^ q * K ^ q) := by
  have e : (offsets K₀ K q).filter (fun ω => (n + ω.1) / K₀ ≠ (n' + ω.1) / K₀) =
      ((range K₀).filter fun c => (n + c) / K₀ ≠ (n' + c) / K₀) ×ˢ
        (Fintype.piFinset (fun _ : Fin q => range K) ×ˢ Fintype.piFinset (fun _ : Fin q => range K)) := by
    ext ⟨a, b, c⟩
    simp only [offsets, mem_filter, mem_product]
    tauto
  rw [e, card_product, card_product, Fintype.card_piFinset]
  simp only [card_range, prod_const, card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ (Fam.card_wrap_le hK₀ h)

theorem card_offsets_wrapD {K₀ K q : ℕ} (hK : 0 < K) (j : Fin q) {n n' : ℕ} (h : n ≤ n') :
    ((offsets K₀ K q).filter fun ω => (n + ω.2.1 j) / K ≠ (n' + ω.2.1 j) / K).card ≤
      K₀ * ((n' - n) * K ^ (q - 1) * K ^ q) := by
  have e : (offsets K₀ K q).filter (fun ω => (n + ω.2.1 j) / K ≠ (n' + ω.2.1 j) / K) =
      range K₀ ×ˢ (((Fintype.piFinset (fun _ : Fin q => range K)).filter
        fun c => (n + c j) / K ≠ (n' + c j) / K) ×ˢ Fintype.piFinset (fun _ : Fin q => range K)) := by
    ext ⟨a, b, c⟩
    simp only [offsets, mem_filter, mem_product]
    tauto
  rw [e, card_product, card_product, card_range,
    Fam.card_piFinset_coord j (fun c => (n + c) / K ≠ (n' + c) / K), Fintype.card_piFinset]
  simp only [card_range, prod_const, card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Fam.card_wrap_le hK h)))

theorem card_offsets_wrapE {K₀ K q : ℕ} (hK : 0 < K) (j : Fin q) {n n' : ℕ} (h : n ≤ n') :
    ((offsets K₀ K q).filter fun ω => (n + ω.2.2 j) / K ≠ (n' + ω.2.2 j) / K).card ≤
      K₀ * (K ^ q * ((n' - n) * K ^ (q - 1))) := by
  have e : (offsets K₀ K q).filter (fun ω => (n + ω.2.2 j) / K ≠ (n' + ω.2.2 j) / K) =
      range K₀ ×ˢ (Fintype.piFinset (fun _ : Fin q => range K) ×ˢ
        ((Fintype.piFinset (fun _ : Fin q => range K)).filter
          fun c => (n + c j) / K ≠ (n' + c j) / K)) := by
    ext ⟨a, b, c⟩
    simp only [offsets, mem_filter, mem_product]
    tauto
  rw [e, card_product, card_product, card_range,
    Fam.card_piFinset_coord j (fun c => (n + c) / K ≠ (n' + c) / K), Fintype.card_piFinset]
  simp only [card_range, prod_const, card_univ, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
    (Fam.card_wrap_le hK h)))

end Offsets

/-! ### The cut decomposed -/

section Decomp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {ρ : ℕ} {A : Fam ι N} {T q : ℕ} {β : Fin q → ℕ} {K₀ K : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- The state edges at a line time. -/
theorem card_ZS_le :
    ((Ico 1 T).filter fun t => t ∈ Zt x0 W ρ T ∨ t - 1 ∈ Zt x0 W ρ T).card ≤
      2 * (Zt x0 W ρ T).card := by
  calc ((Ico 1 T).filter fun t => t ∈ Zt x0 W ρ T ∨ t - 1 ∈ Zt x0 W ρ T).card
      ≤ (Zt x0 W ρ T ∪ (Zt x0 W ρ T).image (· + 1)).card := by
        refine card_le_card fun t ht => ?_
        obtain ⟨ht1, h⟩ := mem_filter.mp ht
        rcases h with h | h
        · exact mem_union_left _ h
        · exact mem_union_right _ (mem_image.mpr ⟨t - 1, h, by have := (mem_Ico.mp ht1).1; omega⟩)
    _ ≤ (Zt x0 W ρ T).card + ((Zt x0 W ρ T).image (· + 1)).card := card_union_le _ _
    _ ≤ 2 * (Zt x0 W ρ T).card := by have := card_image_le (s := Zt x0 W ρ T) (f := (· + 1)); omega

omit [Fintype ι] [DecidableEq ι] in
/-- The hop edges at a line time: at most `2` chords and `2k` hops of the bounded walks at each time. -/
theorem card_ZH_le {k : ℕ}
    (hdegA : ∀ t, ((A.H.image fun η => η.2).filter fun e => e.1 = t ∨ e.2 = t).card ≤ 2 * k) :
    ((Eall x0 A T).filter fun e => e.1 ∈ Zt x0 W ρ T ∨ e.2 ∈ Zt x0 W ρ T).card ≤
      (2 + 2 * k) * (Zt x0 W ρ T).card := by
  have hchord : ∀ t, ((hops x0 T).filter fun e => e.1 = t ∨ e.2 = t).card ≤ 2 := by
    intro t
    have h1 : ((hops x0 T).filter fun e => e.1 = t).card ≤ 1 :=
      card_le_one.mpr fun e he e' he' => by
        obtain ⟨h1, h2⟩ := mem_filter.mp he
        obtain ⟨h1', h2'⟩ := mem_filter.mp he'
        have hh := mem_hops.mp h1
        have hh' := mem_hops.mp h1'
        rw [h2, ← h2'] at hh
        exact Prod.ext (h2.trans h2'.symm) (hop_start_unique hh hh')
    have h2 : ((hops x0 T).filter fun e => e.2 = t).card ≤ 1 :=
      card_le_one.mpr fun e he e' he' => by
        obtain ⟨h1, h2⟩ := mem_filter.mp he
        obtain ⟨h1', h2'⟩ := mem_filter.mp he'
        have hh := mem_hops.mp h1
        have hh' := mem_hops.mp h1'
        rw [h2, ← h2'] at hh
        exact Prod.ext (hop_end_unique hh hh') (h2.trans h2'.symm)
    rw [filter_or]
    exact (card_union_le _ _).trans (by omega)
  calc ((Eall x0 A T).filter fun e => e.1 ∈ Zt x0 W ρ T ∨ e.2 ∈ Zt x0 W ρ T).card
      ≤ ((Zt x0 W ρ T).biUnion fun t => (Eall x0 A T).filter fun e => e.1 = t ∨ e.2 = t).card := by
        refine card_le_card fun e he => ?_
        obtain ⟨he1, h⟩ := mem_filter.mp he
        rcases h with h | h
        · exact mem_biUnion.mpr ⟨e.1, h, mem_filter.mpr ⟨he1, Or.inl rfl⟩⟩
        · exact mem_biUnion.mpr ⟨e.2, h, mem_filter.mpr ⟨he1, Or.inr rfl⟩⟩
    _ ≤ ∑ t ∈ Zt x0 W ρ T, ((Eall x0 A T).filter fun e => e.1 = t ∨ e.2 = t).card := card_biUnion_le
    _ ≤ ∑ _t ∈ Zt x0 W ρ T, (2 + 2 * k) := by
        refine sum_le_sum fun t _ => ?_
        unfold Eall
        rw [filter_union]
        exact (card_union_le _ _).trans (Nat.add_le_add (hchord t) (hdegA t))
    _ = (2 + 2 * k) * (Zt x0 W ρ T).card := by rw [sum_const, smul_eq_mul, mul_comm]

open Classical in
omit [DecidableEq ι] in
/-- **The cut decomposed.** -/
theorem card_cut_le (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) :
    (cutSM x0 W ρ A T β K₀ K ω).card + (cutHM x0 W ρ A T β K₀ K ω).card ≤
      ((Ico 1 T).filter fun t => t ∈ Zt x0 W ρ T ∨ t - 1 ∈ Zt x0 W ρ T).card +
      ((Eall x0 A T).filter fun e => e.1 ∈ Zt x0 W ρ T ∨ e.2 ∈ Zt x0 W ρ T).card +
      ((Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (t - 1)).card +
      ((hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.1).card +
      (A.H.filter fun η => η.2.1 ∉ Zt x0 W ρ T ∧ η.2.2 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.2 ≤
          mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.1).card := by
  set m := mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2
  set Z := Zt x0 W ρ T
  have hS : cutSM x0 W ρ A T β K₀ K ω ⊆ ((Ico 1 T).filter fun t => t ∈ Z ∨ t - 1 ∈ Z) ∪
      ((Ico 1 T).filter fun t => t ∉ Z ∧ t - 1 ∉ Z ∧ m t < m (t - 1)) := by
    intro t ht
    obtain ⟨ht1, h⟩ := mem_filter.mp ht
    by_cases hz : t ∈ Z ∨ t - 1 ∈ Z
    · exact mem_union_left _ (mem_filter.mpr ⟨ht1, hz⟩)
    · push Not at hz
      have := h.resolve_left (by tauto)
      exact mem_union_right _ (mem_filter.mpr ⟨ht1, hz.1, hz.2, this.resolve_left (by tauto)⟩)
  have hH : cutHM x0 W ρ A T β K₀ K ω ⊆ ((Eall x0 A T).filter fun e => e.1 ∈ Z ∨ e.2 ∈ Z) ∪
      (((hops x0 T).filter fun e => e.1 ∉ Z ∧ m e.2 ≤ m e.1) ∪
        (A.H.filter fun η => η.2.1 ∉ Z ∧ η.2.2 ∉ Z ∧ m η.2.2 ≤ m η.2.1).image fun η => η.2) := by
    intro e he
    obtain ⟨he1, h⟩ := mem_filter.mp he
    by_cases hz : e.1 ∈ Z ∨ e.2 ∈ Z
    · exact mem_union_left _ (mem_filter.mpr ⟨he1, hz⟩)
    · push Not at hz
      have hv : m e.2 ≤ m e.1 := (h.resolve_left hz.1).resolve_left hz.2
      refine mem_union_right _ ?_
      rcases mem_union.mp he1 with hc | ha
      · exact mem_union_left _ (mem_filter.mpr ⟨hc, hz.1, hv⟩)
      · obtain ⟨η, hη, rfl⟩ := mem_image.mp ha
        exact mem_union_right _ (mem_image.mpr ⟨η, mem_filter.mpr ⟨hη, hz.1, hz.2, hv⟩, rfl⟩)
  have h1 := (card_le_card hS).trans (card_union_le _ _)
  have h2 := (card_le_card hH).trans (card_union_le _ _)
  have h3 := card_union_le ((hops x0 T).filter fun e => e.1 ∉ Z ∧ m e.2 ≤ m e.1)
    ((A.H.filter fun η => η.2.1 ∉ Z ∧ η.2.2 ∉ Z ∧ m η.2.2 ≤ m η.2.1).image fun η => η.2)
  have h4 := card_image_le (s := A.H.filter fun η => η.2.1 ∉ Z ∧ η.2.2 ∉ Z ∧ m η.2.2 ≤ m η.2.1)
    (f := fun η => η.2)
  omega

end Decomp

/-! ### Violations need wraps -/

section Wraps

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {ρ : ℕ} {A : Fam ι N} {T q : ℕ} {β : Fin q → ℕ} {K₀ K : ℕ}
variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

omit [Fintype ι] [DecidableEq ι] in
theorem not_line_of_not_Zt {t : ℕ} (ht : t < T) (h : t ∉ Zt x0 W ρ T) : ¬ LineAt W ρ 0 (x0 t) :=
  fun hl => h (mem_filter.mpr ⟨mem_range.mpr ht, hl⟩)

open Classical in
omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- (b) A descent between non-line times needs a wrap of `d_0` or of some `e_j`. -/
theorem desc_subset (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) :
    ((Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (t - 1)) ⊆
      ((Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T ∧
          (lcnt x0 W ρ 0 (t - 1) + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 t + ω.1) / K₀) ∪
        univ.biUnion fun j : Fin q => (Ico 1 T).filter fun t =>
          (nev A β j (t - 1) + ω.2.2 j) / K ≠ (nev A β j t + ω.2.2 j) / K := by
  intro t ht
  obtain ⟨ht1, h1, h2, hlt⟩ := mem_filter.mp ht
  obtain ⟨ht1a, ht1b⟩ := mem_Ico.mp ht1
  by_contra hno
  simp only [mem_union, mem_filter, mem_biUnion, mem_univ, true_and, not_or, not_exists,
    ht1, h1, h2, not_not, not_false_eq_true] at hno
  have hle := state_le (A := A) (β := β) (K₀ := K₀) (K := K) (ω₀ := ω.1) (ωd := ω.2.1)
    (ωe := ω.2.2) hx0 hW hdiv ht1a (not_line_of_not_Zt ht1b h1)
    (not_line_of_not_Zt (by omega) h2) hno.1 (fun j => hno.2 j)
  exact absurd hlt (not_lt.mpr hle)

open Classical in
omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- (c) A violated chord at a non-line cell needs a wrap of the counter of its deciding level, or of
some `e_j` above it. -/
theorem chord_subset (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) :
    ((hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.1) ⊆
      ((hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧ chordLevel x0 W ρ q e.1 e.2 = 0 ∧
          (lcnt x0 W ρ 0 e.1 + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 e.2 + ω.1) / K₀) ∪
        (univ.biUnion fun j : Fin q => (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
          chordLevel x0 W ρ q e.1 e.2 = j.val + 1 ∧
          (lcnt x0 W ρ (j.val + 1) e.1 + ω.2.1 j) / K ≠ (lcnt x0 W ρ (j.val + 1) e.2 + ω.2.1 j) / K) ∪
        (univ.biUnion fun j : Fin q => (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
          chordLevel x0 W ρ q e.1 e.2 < j.val + 1 ∧
          (nev A β j e.1 + ω.2.2 j) / K ≠ (nev A β j e.2 + ω.2.2 j) / K) := by
  intro e he
  obtain ⟨hh, hz, hv⟩ := mem_filter.mp he
  have hγ := mem_hops.mp hh
  have hc := not_line_of_not_Zt (by have := hγ.1; have := hγ.2.1; omega) hz
  by_contra hno
  simp only [mem_union, mem_filter, mem_biUnion, mem_univ, true_and, not_or, not_exists,
    not_and, hh, hz, true_and, not_not, not_false_eq_true] at hno
  obtain ⟨⟨h0, hd⟩, he'⟩ := hno
  have hlt := chord_lt (A := A) (β := β) (K₀ := K₀) (K := K) (ω₀ := ω.1) (ωd := ω.2.1)
    (ωe := ω.2.2) hx0 hW hdiv hγ hc h0 hd he'
  exact absurd hv (not_le.mpr hlt)

open Classical in
include hx0 hW hdiv in
/-- (d) A violated hop of a bounded walk, not at a line time, needs a visit of head `0` to a line of
its window's level, or a wrap of some `e_j` at or above its window. -/
theorem ahop_subset (hA : A.Valid T) (win : ι → Fin q) (hwin : ∀ F, β (win F) ≤ lam (A.d F))
    (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) :
    (A.H.filter fun η => η.2.1 ∉ Zt x0 W ρ T ∧ η.2.2 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.1) ⊆
      (A.H.filter fun η => ∃ t ∈ Ioo η.2.1 η.2.2, LineAt W ρ ((win η.1).val + 1) (x0 t)) ∪
        univ.biUnion fun j : Fin q => A.H.filter fun η => win η.1 ≤ j ∧
          (nev A β j η.2.1 + ω.2.2 j) / K ≠ (nev A β j η.2.2 + ω.2.2 j) / K := by
  intro η hη
  obtain ⟨hηH, hzp, hzu, hv⟩ := mem_filter.mp hη
  obtain ⟨h1, h2, h3, h4⟩ := hA.hop_in η hηH
  have hUT := hA.lt_T η.1
  by_contra hno
  simp only [mem_union, mem_filter, mem_biUnion, mem_univ, true_and, not_or, not_exists,
    not_and, hηH, true_and, not_not] at hno
  obtain ⟨hnl, he⟩ := hno
  have hlt := ahop_lt (x0 := x0) (W := W) (ρ := ρ) (A := A) (β := β) (K₀ := K₀) (K := K)
    (ω₀ := ω.1) (ωd := ω.2.1) (ωe := ω.2.2) hx0 hW hdiv (win η.1) h2 h3 (hwin η.1)
    (not_line_of_not_Zt (by omega) hzp) (not_line_of_not_Zt (by omega) hzu)
    (fun t ht hl => hnl t ht hl) (fun j' hj' => he j' hj')
  exact absurd hv (not_le.mpr hlt)

end Wraps

/-! ### Summing over the offsets -/

section OmegaSums

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {ρ : ℕ} {A : Fam ι N} {T q : ℕ} {β : Fin q → ℕ} {K₀ K : ℕ}
variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

omit [DecidableEq ι] in
/-- The event count rises by at most the number of events in between. -/
theorem nev_sub_le (j : Fin q) {t t' : ℕ} :
    nev A β j t' - nev A β j t ≤
      (univ.filter fun F => t < A.o F ∧ A.o F ≤ t' ∧ β j ≤ lam (A.d F)).card := by
  classical
  unfold nev
  have : univ.filter (fun F => A.o F ≤ t' ∧ β j ≤ lam (A.d F)) ⊆
      univ.filter (fun F => A.o F ≤ t ∧ β j ≤ lam (A.d F)) ∪
        univ.filter (fun F => t < A.o F ∧ A.o F ≤ t' ∧ β j ≤ lam (A.d F)) := by
    intro F hF
    obtain ⟨-, h1, h2⟩ := mem_filter.mp hF
    rcases le_or_gt (A.o F) t with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h, h2⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h, h1, h2⟩)
  have := (card_le_card this).trans (card_union_le _ _)
  omega

omit [DecidableEq ι] in
/-- Over the state edges, the event count of a window rises by at most the number of its events. -/
theorem sum_nev_steps_le (j : Fin q) :
    ∑ t ∈ Ico 1 T, (nev A β j t - nev A β j (t - 1)) ≤
      (univ.filter fun F => β j ≤ lam (A.d F)).card := by
  classical
  calc ∑ t ∈ Ico 1 T, (nev A β j t - nev A β j (t - 1))
      ≤ ∑ t ∈ Ico 1 T, (univ.filter fun F => A.o F = t ∧ β j ≤ lam (A.d F)).card := by
        refine sum_le_sum fun t ht => (nev_sub_le j).trans (card_le_card fun F hF => ?_)
        obtain ⟨-, h1, h2, h3⟩ := mem_filter.mp hF
        exact mem_filter.mpr ⟨mem_univ _, by have := (mem_Ico.mp ht).1; omega, h3⟩
    _ = ∑ F, ((Ico 1 T).filter fun t => A.o F = t ∧ β j ≤ lam (A.d F)).card :=
        sum_card_filter_comm _ _ (fun t F => A.o F = t ∧ β j ≤ lam (A.d F))
    _ ≤ ∑ F ∈ univ.filter (fun F => β j ≤ lam (A.d F)), 1 := by
        rw [sum_filter]
        refine sum_le_sum fun F _ => ?_
        split_ifs with hF
        · exact card_le_one.mpr fun x hx y hy =>
            (mem_filter.mp hx).2.1.symm.trans (mem_filter.mp hy).2.1
        · exact Nat.le_zero.mpr (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun t _ h => hF h.2))
    _ = (univ.filter fun F => β j ≤ lam (A.d F)).card := by rw [card_eq_sum_ones]

/-- Along a chord the counters read one strip, and do not decrease. -/
theorem lcnt_mono_hop {p u : ℕ} (hpu : p ≤ u) (hcu : x0 u = x0 p) (i : ℕ) :
    lcnt x0 W ρ i p ≤ lcnt x0 W ρ i u := by
  unfold lcnt
  rw [hcu]
  split_ifs
  · exact visits_mono _ hpu
  · exact entries'_mono _ _ hpu

open Classical in
omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- (b) summed over the offsets. -/
theorem sum_desc_le (hK₀ : 0 < K₀) (hK : 0 < K) :
    ∑ ω ∈ offsets K₀ K q, ((Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (t - 1)).card ≤
      T * (K ^ q * K ^ q) +
        ∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card * (K₀ * (K ^ q * K ^ (q - 1))) := by
  set X := (Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T
  have h1 : ∀ ω ∈ offsets K₀ K q, ((Ico 1 T).filter fun t => t ∉ Zt x0 W ρ T ∧ t - 1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 t < mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 (t - 1)).card ≤
      (X.filter fun t => (lcnt x0 W ρ 0 (t - 1) + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 t + ω.1) / K₀).card +
        ∑ j : Fin q, ((Ico 1 T).filter fun t =>
          (nev A β j (t - 1) + ω.2.2 j) / K ≠ (nev A β j t + ω.2.2 j) / K).card := by
    intro ω _
    refine (card_le_card (desc_subset hx0 hW hdiv ω)).trans ((card_union_le _ _).trans ?_)
    refine Nat.add_le_add (le_of_eq ?_) card_biUnion_le
    congr 1
    ext t
    simp only [X, mem_filter, and_assoc]
  calc _ ≤ ∑ ω ∈ offsets K₀ K q, ((X.filter fun t =>
          (lcnt x0 W ρ 0 (t - 1) + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 t + ω.1) / K₀).card +
        ∑ j : Fin q, ((Ico 1 T).filter fun t =>
          (nev A β j (t - 1) + ω.2.2 j) / K ≠ (nev A β j t + ω.2.2 j) / K).card) := sum_le_sum h1
    _ = ∑ t ∈ X, ((offsets K₀ K q).filter fun ω =>
          (lcnt x0 W ρ 0 (t - 1) + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 t + ω.1) / K₀).card +
        ∑ j : Fin q, ∑ t ∈ Ico 1 T, ((offsets K₀ K q).filter fun ω =>
          (nev A β j (t - 1) + ω.2.2 j) / K ≠ (nev A β j t + ω.2.2 j) / K).card := by
        rw [sum_add_distrib, sum_comm]
        congr 1
        · exact sum_card_filter_comm _ _ (fun (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) (t : ℕ) =>
            (lcnt x0 W ρ 0 (t - 1) + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 t + ω.1) / K₀)
        · exact sum_congr rfl fun j _ => sum_card_filter_comm _ _
            (fun (ω : ℕ × (Fin q → ℕ) × (Fin q → ℕ)) (t : ℕ) =>
              (nev A β j (t - 1) + ω.2.2 j) / K ≠ (nev A β j t + ω.2.2 j) / K)
    _ ≤ ∑ _t ∈ X, 1 * (K ^ q * K ^ q) +
        ∑ j : Fin q, ∑ t ∈ Ico 1 T, K₀ * (K ^ q * ((nev A β j t - nev A β j (t - 1)) * K ^ (q - 1))) := by
        refine Nat.add_le_add (sum_le_sum fun t ht => ?_) (sum_le_sum fun j _ => sum_le_sum fun t _ =>
          card_offsets_wrapE hK j (nev_mono j (by omega)))
        obtain ⟨ht1, hz1, hz2⟩ := mem_filter.mp ht
        obtain ⟨ht1a, ht1b⟩ := mem_Ico.mp ht1
        have hstep := lcnt_state_zero (W := W) (ρ := ρ) hx0 hW ht1a
          (not_line_of_not_Zt ht1b hz1) (not_line_of_not_Zt (by omega) hz2)
        have := card_offsets_wrap0 (K := K) (q := q) hK₀ (show lcnt x0 W ρ 0 (t - 1) ≤ lcnt x0 W ρ 0 t by omega)
        rw [hstep, Nat.add_sub_cancel_left] at this
        rwa [hstep]
    _ ≤ T * (K ^ q * K ^ q) +
        ∑ j : Fin q, (univ.filter fun F => β j ≤ lam (A.d F)).card * (K₀ * (K ^ q * K ^ (q - 1))) := by
        refine Nat.add_le_add ?_ (sum_le_sum fun j _ => ?_)
        · rw [sum_const, smul_eq_mul, one_mul]
          exact Nat.mul_le_mul_right _ ((card_le_card (filter_subset _ _)).trans (by simp))
        · calc ∑ t ∈ Ico 1 T, K₀ * (K ^ q * ((nev A β j t - nev A β j (t - 1)) * K ^ (q - 1)))
              = (∑ t ∈ Ico 1 T, (nev A β j t - nev A β j (t - 1))) * (K₀ * (K ^ q * K ^ (q - 1))) := by
                rw [sum_mul]; exact sum_congr rfl fun t _ => by ring
            _ ≤ _ := Nat.mul_le_mul_right _ (sum_nev_steps_le j)

/-- Summing a count over the offsets: exchange of summation. -/
theorem sum_offsets_filter_eq {α : Type*} (X : Finset α) (K₀ K q : ℕ)
    (P : ℕ × (Fin q → ℕ) × (Fin q → ℕ) → α → Prop) [∀ ω x, Decidable (P ω x)] :
    ∑ ω ∈ offsets K₀ K q, (X.filter fun x => P ω x).card =
      ∑ x ∈ X, ((offsets K₀ K q).filter fun ω => P ω x).card :=
  sum_card_filter_comm _ _ P

open Classical in
omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- (c) summed over the offsets. -/
theorem sum_chord_le (hK₀ : 0 < K₀) (hK : 0 < K) :
    ∑ ω ∈ offsets K₀ K q, ((hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.1).card ≤
      (K ^ q * K ^ q) * ∑ e ∈ (hops x0 T).filter (fun e => e.1 ∉ Zt x0 W ρ T ∧
          chordLevel x0 W ρ q e.1 e.2 = 0), (lcnt x0 W ρ 0 e.2 - lcnt x0 W ρ 0 e.1) +
      ∑ j : Fin q, (K₀ * (K ^ (q - 1) * K ^ q)) * ∑ e ∈ (hops x0 T).filter (fun e =>
          e.1 ∉ Zt x0 W ρ T ∧ chordLevel x0 W ρ q e.1 e.2 = j.val + 1),
          (lcnt x0 W ρ (j.val + 1) e.2 - lcnt x0 W ρ (j.val + 1) e.1) +
      ∑ j : Fin q, (K₀ * (K ^ q * K ^ (q - 1))) * ∑ e ∈ (hops x0 T).filter (fun e =>
          e.1 ∉ Zt x0 W ρ T ∧ chordLevel x0 W ρ q e.1 e.2 < j.val + 1),
          (nev A β j e.2 - nev A β j e.1) := by
  set X0 := (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧ chordLevel x0 W ρ q e.1 e.2 = 0
  set Xd : Fin q → Finset (ℕ × ℕ) := fun j => (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
    chordLevel x0 W ρ q e.1 e.2 = j.val + 1
  set Xe : Fin q → Finset (ℕ × ℕ) := fun j => (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
    chordLevel x0 W ρ q e.1 e.2 < j.val + 1
  have hmono : ∀ e ∈ hops x0 T, ∀ i, lcnt x0 W ρ i e.1 ≤ lcnt x0 W ρ i e.2 := fun e he i =>
    lcnt_mono_hop (by have := (mem_hops.mp he).1; omega) (mem_hops.mp he).2.2.1 i
  have hle : ∀ e ∈ hops x0 T, e.1 ≤ e.2 := fun e he => by have := (mem_hops.mp he).1; omega
  have h1 : ∀ ω ∈ offsets K₀ K q, ((hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 e.1).card ≤
      (X0.filter fun e => (lcnt x0 W ρ 0 e.1 + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 e.2 + ω.1) / K₀).card +
      ∑ j : Fin q, ((Xd j).filter fun e => (lcnt x0 W ρ (j.val + 1) e.1 + ω.2.1 j) / K ≠
          (lcnt x0 W ρ (j.val + 1) e.2 + ω.2.1 j) / K).card +
      ∑ j : Fin q, ((Xe j).filter fun e =>
          (nev A β j e.1 + ω.2.2 j) / K ≠ (nev A β j e.2 + ω.2.2 j) / K).card := by
    intro ω _
    refine (card_le_card (chord_subset hx0 hW hdiv ω)).trans ?_
    refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
      (Nat.add_le_add (le_of_eq ?_) (card_biUnion_le.trans (le_of_eq ?_)))) (card_biUnion_le.trans
        (le_of_eq ?_)))
    · congr 1; ext e; simp only [X0, mem_filter, and_assoc]
    · refine sum_congr rfl fun j _ => ?_
      congr 1; ext e; simp only [Xd, mem_filter, and_assoc]
    · refine sum_congr rfl fun j _ => ?_
      congr 1; ext e; simp only [Xe, mem_filter, and_assoc]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_add_distrib]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · rw [sum_offsets_filter_eq X0 K₀ K q (fun ω e =>
      (lcnt x0 W ρ 0 e.1 + ω.1) / K₀ ≠ (lcnt x0 W ρ 0 e.2 + ω.1) / K₀), mul_sum]
    refine sum_le_sum fun e he => ?_
    rw [mul_comm]
    exact card_offsets_wrap0 hK₀ (hmono e (mem_filter.mp he).1 0)
  · rw [sum_comm]
    refine sum_le_sum fun j _ => ?_
    rw [sum_offsets_filter_eq (Xd j) K₀ K q (fun ω e => (lcnt x0 W ρ (j.val + 1) e.1 + ω.2.1 j) / K ≠
      (lcnt x0 W ρ (j.val + 1) e.2 + ω.2.1 j) / K), mul_sum]
    refine sum_le_sum fun e he => ?_
    refine (card_offsets_wrapD hK j (hmono e (mem_filter.mp he).1 _)).trans (le_of_eq ?_)
    ring
  · rw [sum_comm]
    refine sum_le_sum fun j _ => ?_
    rw [sum_offsets_filter_eq (Xe j) K₀ K q (fun ω e =>
      (nev A β j e.1 + ω.2.2 j) / K ≠ (nev A β j e.2 + ω.2.2 j) / K), mul_sum]
    refine sum_le_sum fun e he => ?_
    refine (card_offsets_wrapE hK j (nev_mono j (hle e (mem_filter.mp he).1))).trans (le_of_eq ?_)
    ring

open Classical in
include hx0 hW hdiv in
/-- (d) summed over the offsets. -/
theorem sum_ahop_le (hK : 0 < K) (hA : A.Valid T) (win : ι → Fin q)
    (hwin : ∀ F, β (win F) ≤ lam (A.d F)) :
    ∑ ω ∈ offsets K₀ K q, (A.H.filter fun η => η.2.1 ∉ Zt x0 W ρ T ∧ η.2.2 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.1).card ≤
      (offsets K₀ K q).card * (A.H.filter fun η =>
          ∃ t ∈ Ioo η.2.1 η.2.2, LineAt W ρ ((win η.1).val + 1) (x0 t)).card +
      ∑ j : Fin q, (K₀ * (K ^ q * K ^ (q - 1))) * ∑ η ∈ A.H.filter (fun η => win η.1 ≤ j),
          (nev A β j η.2.2 - nev A β j η.2.1) := by
  have hle : ∀ η ∈ A.H, η.2.1 ≤ η.2.2 := fun η hη => by
    have := hA.hop_in η hη; omega
  have h1 : ∀ ω ∈ offsets K₀ K q, (A.H.filter fun η => η.2.1 ∉ Zt x0 W ρ T ∧ η.2.2 ∉ Zt x0 W ρ T ∧
        mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.2 ≤ mlab x0 W ρ A β K₀ K ω.1 ω.2.1 ω.2.2 η.2.1).card ≤
      (A.H.filter fun η => ∃ t ∈ Ioo η.2.1 η.2.2, LineAt W ρ ((win η.1).val + 1) (x0 t)).card +
      ∑ j : Fin q, ((A.H.filter fun η => win η.1 ≤ j).filter fun η =>
          (nev A β j η.2.1 + ω.2.2 j) / K ≠ (nev A β j η.2.2 + ω.2.2 j) / K).card := by
    intro ω _
    refine (card_le_card (ahop_subset hx0 hW hdiv hA win hwin ω)).trans ?_
    refine (card_union_le _ _).trans (Nat.add_le_add le_rfl (card_biUnion_le.trans (le_of_eq ?_)))
    refine sum_congr rfl fun j _ => ?_
    congr 1; ext η; simp only [mem_filter, and_assoc]
  refine (sum_le_sum h1).trans ?_
  rw [sum_add_distrib, sum_const, smul_eq_mul]
  refine Nat.add_le_add le_rfl ?_
  rw [sum_comm]
  refine sum_le_sum fun j _ => ?_
  rw [sum_offsets_filter_eq (A.H.filter fun η => win η.1 ≤ j) K₀ K q (fun ω η =>
    (nev A β j η.2.1 + ω.2.2 j) / K ≠ (nev A β j η.2.2 + ω.2.2 j) / K), mul_sum]
  refine sum_le_sum fun η hη => ?_
  refine (card_offsets_wrapE hK j (nev_mono j (hle η (mem_filter.mp hη).1))).trans (le_of_eq ?_)
  ring

end OmegaSums

/-! ### Exchange of summation -/

section Exchange

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
variable {x0 : ℕ → ℤ} {W : ℕ → ℕ} {ρ : ℕ} {A : Fam ι N} {T q : ℕ} {β : Fin q → ℕ}
variable (hx0 : IsWalk x0) (hW : ∀ i, 2 ≤ W i) (hdiv : ∀ i j, i ≤ j → W i ∣ W j)

variable (x0 W ρ T) in
/-- The increment times of level `i`: all times at level `0`, and the times just after a visit to a
level-`i` line at positive levels. -/
def incT (i : ℕ) : Finset ℕ :=
  if i = 0 then range T else (range T).filter fun s => 1 ≤ s ∧ LineAt W ρ i (x0 (s - 1))

variable (x0 W ρ) in
/-- The increments of the level-`i` counter of the strip `S` at time `s`. -/
def incr (i s : ℕ) (S : ℤ) : Prop :=
  if i = 0 then ¬ LineAt W ρ 0 (x0 s) ∧ stripAt W ρ 0 (x0 s) = S
  else 1 ≤ s ∧ ¬ LineAt W ρ i (x0 s) ∧ stripAt W ρ i (x0 s) = S ∧ LineAt W ρ i (x0 (s - 1))

instance (i s : ℕ) (S : ℤ) : Decidable (incr x0 W ρ i s S) := by unfold incr; infer_instance

theorem lcnt_eq_incr (i t : ℕ) :
    lcnt x0 W ρ i t = ((range (t + 1)).filter fun s => incr x0 W ρ i s (stripAt W ρ i (x0 t))).card := by
  unfold lcnt incr visits entries'
  split_ifs with h
  · subst h; rfl
  · rfl

theorem incr_line (i s : ℕ) (S : ℤ) (h : incr x0 W ρ i s S) :
    ¬ LineAt W ρ i (x0 s) ∧ stripAt W ρ i (x0 s) = S := by
  unfold incr at h
  split_ifs at h with hi
  · subst hi; exact h
  · exact ⟨h.2.1, h.2.2.1⟩

/-- The growth of a counter along a chord is the number of increments in between. -/
theorem lcnt_chord_sub_le {p u : ℕ} (hcu : x0 u = x0 p) (i : ℕ) :
    lcnt x0 W ρ i u - lcnt x0 W ρ i p ≤
      ((Ioc p u).filter fun s => incr x0 W ρ i s (stripAt W ρ i (x0 p))).card := by
  rw [lcnt_eq_incr, lcnt_eq_incr, hcu]
  have : (range (u + 1)).filter (fun s => incr x0 W ρ i s (stripAt W ρ i (x0 p))) ⊆
      (range (p + 1)).filter (fun s => incr x0 W ρ i s (stripAt W ρ i (x0 p))) ∪
        (Ioc p u).filter (fun s => incr x0 W ρ i s (stripAt W ρ i (x0 p))) := by
    intro s hs
    obtain ⟨h1, h2⟩ := mem_filter.mp hs
    rcases le_or_gt s p with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr (by omega), h2⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h, by have := mem_range.mp h1; omega⟩, h2⟩)
  have := (card_le_card this).trans (card_union_le _ _)
  omega

include hW hdiv in
/-- **(X1, X2)** Over the chords at non-line cells, the counters of level `i` grow in all by at most
`W i - 1` per increment time: by (P1) at most `W i - 1` chords at cells of one strip span a time. -/
theorem sum_chord_growth_le (i : ℕ) :
    ∑ e ∈ (hops x0 T).filter (fun e => e.1 ∉ Zt x0 W ρ T), (lcnt x0 W ρ i e.2 - lcnt x0 W ρ i e.1) ≤
      (W i - 1) * (incT x0 W ρ T i).card := by
  classical
  set X := (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T
  calc ∑ e ∈ X, (lcnt x0 W ρ i e.2 - lcnt x0 W ρ i e.1)
      ≤ ∑ e ∈ X, ((range T).filter fun s => e.1 < s ∧ s ≤ e.2 ∧
          incr x0 W ρ i s (stripAt W ρ i (x0 e.1))).card := by
        refine sum_le_sum fun e he => (lcnt_chord_sub_le (mem_hops.mp (mem_filter.mp he).1).2.2.1 i).trans
          (card_le_card fun s hs => ?_)
        obtain ⟨h1, h2⟩ := mem_filter.mp hs
        obtain ⟨h1a, h1b⟩ := mem_Ioc.mp h1
        have := (mem_hops.mp (mem_filter.mp he).1).2.1
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), h1a, h1b, h2⟩
    _ = ∑ s ∈ range T, (X.filter fun e => e.1 < s ∧ s ≤ e.2 ∧
          incr x0 W ρ i s (stripAt W ρ i (x0 e.1))).card :=
        sum_card_filter_comm _ _ (fun (e : ℕ × ℕ) (s : ℕ) => e.1 < s ∧ s ≤ e.2 ∧
          incr x0 W ρ i s (stripAt W ρ i (x0 e.1)))
    _ ≤ ∑ s ∈ incT x0 W ρ T i, (W i - 1) := by
        rw [← sum_filter_add_sum_filter_not (range T) (fun s => s ∈ incT x0 W ρ T i)]
        have hzero : ∑ s ∈ (range T).filter (fun s => s ∉ incT x0 W ρ T i),
            (X.filter fun e => e.1 < s ∧ s ≤ e.2 ∧ incr x0 W ρ i s (stripAt W ρ i (x0 e.1))).card = 0 := by
          refine sum_eq_zero fun s hs => card_eq_zero.mpr (filter_eq_empty_iff.mpr fun e _ h => ?_)
          obtain ⟨hsT, hsn⟩ := mem_filter.mp hs
          apply hsn
          have hinc := h.2.2
          unfold incT
          unfold incr at hinc
          split_ifs at hinc ⊢ with hi
          · exact hsT
          · exact mem_filter.mpr ⟨hsT, hinc.1, hinc.2.2.2⟩
        rw [hzero, add_zero]
        have hsub : (range T).filter (fun s => s ∈ incT x0 W ρ T i) = incT x0 W ρ T i := by
          ext s
          simp only [mem_filter, mem_range, and_iff_right_iff_imp]
          intro hs
          unfold incT at hs
          split_ifs at hs
          · exact mem_range.mp hs
          · exact mem_range.mp (mem_filter.mp hs).1
        rw [hsub]
        refine sum_le_sum fun s _ => ?_
        refine (card_le_card fun e he => ?_).trans
          (card_hops_span_strip_le x0 T (hW i) (res_bounds (ρ := ρ) hW i) s (stripAt W ρ i (x0 s)))
        obtain ⟨he1, h1, h2, hinc⟩ := mem_filter.mp he
        obtain ⟨hh, hz⟩ := mem_filter.mp he1
        have hnl := not_lineAt_of_not_line0 (i := i) hdiv
          (not_line_of_not_Zt (by have := (mem_hops.mp hh).1; have := (mem_hops.mp hh).2.1; omega) hz)
        obtain ⟨-, hS⟩ := incr_line i s _ hinc
        exact mem_filter.mpr ⟨hh, hnl, hS.symm, h1, h2⟩
    _ = (W i - 1) * (incT x0 W ρ T i).card := by rw [sum_const, smul_eq_mul, mul_comm]

include hx0 hW hdiv in
/-- **Confinement.** Inside a chord of deciding level below `i`, head `0` stays in the level-`i` strip
of the chord's cell, off the level-`i` lines. -/
theorem chord_confined {p u q i τ : ℕ} {T' : ℕ} (hγ : IsHop x0 T' p u) (hc : ¬ LineAt W ρ 0 (x0 p))
    (hlev : chordLevel x0 W ρ q p u < i) (hiq : i ≤ q) (h1 : p < τ) (h2 : τ ≤ u) :
    ¬ LineAt W ρ i (x0 τ) ∧ stripAt W ρ i (x0 τ) = stripAt W ρ i (x0 p) := by
  have hnl : ∀ t, p ≤ t → t ≤ u → ¬ LineAt W ρ i (x0 t) := by
    intro t ht1 ht2
    rcases Nat.eq_or_lt_of_le ht1 with he | hlt
    · rw [← he]; exact not_lineAt_of_not_line0 hdiv hc
    rcases Nat.eq_or_lt_of_le ht2 with he' | hlt'
    · rw [he', hγ.2.2.1]; exact not_lineAt_of_not_line0 hdiv hc
    exact not_line_of_gt_chordLevel hlev hiq (mem_Ioo.mpr ⟨hlt, hlt'⟩)
  exact ⟨hnl τ (by omega) h2, stripAt_const hx0 hW hnl τ (by omega) h2⟩

omit [DecidableEq ι] in
include hx0 hW hdiv in
/-- **(X3)** Over the chords at non-line cells, the event counts of the windows above their level grow
in all by at most `W (j+1) - 1` per event of window `j`: the chords of level `≤ j` that span an event
are confined to one level-`(j+1)` strip. -/
theorem sum_chord_events_le (j : Fin q) :
    ∑ e ∈ (hops x0 T).filter (fun e => e.1 ∉ Zt x0 W ρ T ∧ chordLevel x0 W ρ q e.1 e.2 < j.val + 1),
      (nev A β j e.2 - nev A β j e.1) ≤
      (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card := by
  classical
  set X := (hops x0 T).filter fun e => e.1 ∉ Zt x0 W ρ T ∧ chordLevel x0 W ρ q e.1 e.2 < j.val + 1
  calc ∑ e ∈ X, (nev A β j e.2 - nev A β j e.1)
      ≤ ∑ e ∈ X, (univ.filter fun F => e.1 < A.o F ∧ A.o F ≤ e.2 ∧ β j ≤ lam (A.d F)).card :=
        sum_le_sum fun e _ => nev_sub_le j
    _ = ∑ F, (X.filter fun e => e.1 < A.o F ∧ A.o F ≤ e.2 ∧ β j ≤ lam (A.d F)).card :=
        sum_card_filter_comm _ _ (fun (e : ℕ × ℕ) (F : ι) => e.1 < A.o F ∧ A.o F ≤ e.2 ∧ β j ≤ lam (A.d F))
    _ ≤ ∑ F ∈ univ.filter (fun F => β j ≤ lam (A.d F)), (W (j.val + 1) - 1) := by
        rw [sum_filter]
        refine sum_le_sum fun F _ => ?_
        split_ifs with hF
        · refine (card_le_card fun e he => ?_).trans (card_hops_span_strip_le x0 T (hW _)
            (res_bounds (ρ := ρ) hW _) (A.o F) (stripAt W ρ (j.val + 1) (x0 (A.o F))))
          obtain ⟨he1, h1, h2, -⟩ := mem_filter.mp he
          obtain ⟨hh, hz, hlev⟩ := mem_filter.mp he1
          have hγ := mem_hops.mp hh
          have hc := not_line_of_not_Zt (by have := hγ.1; have := hγ.2.1; omega) hz
          obtain ⟨-, hS⟩ := chord_confined hx0 hW hdiv hγ hc hlev (by omega) h1 h2
          exact mem_filter.mpr ⟨hh, not_lineAt_of_not_line0 hdiv hc, hS.symm, h1, h2⟩
        · exact Nat.le_zero.mpr (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun e _ h => hF h.2.2))
    _ = (W (j.val + 1) - 1) * (univ.filter fun F => β j ≤ lam (A.d F)).card := by
        rw [sum_const, smul_eq_mul, mul_comm]

omit [Fintype ι] in
/-- **(X4)** The hops of the bounded walks along which head `0` visits a line of their window's
level number at most `N 2^(β_j + h + 1)` per visit to a level-`(j+1)` line, by the overlap bound. -/
theorem card_lineVisit_le (hA : A.Valid T) {h : ℕ} (win : ι → Fin q)
    (hwin : ∀ F, lam (A.d F) ≤ β (win F) + h) :
    (A.H.filter fun η => ∃ t ∈ Ioo η.2.1 η.2.2, LineAt W ρ ((win η.1).val + 1) (x0 t)).card ≤
      ∑ j : Fin q, (lineT x0 W ρ T (j.val + 1)).card * (N * (2 ^ (β j + h + 1) - 1)) := by
  classical
  calc (A.H.filter fun η => ∃ t ∈ Ioo η.2.1 η.2.2, LineAt W ρ ((win η.1).val + 1) (x0 t)).card
      ≤ (univ.biUnion fun j : Fin q => (lineT x0 W ρ T (j.val + 1)).biUnion fun t =>
          A.H.filter fun η => η.2.1 < t ∧ t ≤ η.2.2 ∧ lam (A.d η.1) < β j + h + 1).card := by
        refine card_le_card fun η hη => ?_
        obtain ⟨hηH, t, ht, hl⟩ := mem_filter.mp hη
        obtain ⟨h1, h2⟩ := mem_Ioo.mp ht
        have hUT := hA.lt_T η.1
        have hin := hA.hop_in η hηH
        refine mem_biUnion.mpr ⟨win η.1, mem_univ _, mem_biUnion.mpr ⟨t,
          mem_filter.mpr ⟨mem_range.mpr (by omega), hl⟩, mem_filter.mpr ⟨hηH, h1, h2.le, ?_⟩⟩⟩
        have := hwin η.1
        omega
    _ ≤ ∑ j : Fin q, ((lineT x0 W ρ T (j.val + 1)).biUnion fun t =>
          A.H.filter fun η => η.2.1 < t ∧ t ≤ η.2.2 ∧ lam (A.d η.1) < β j + h + 1).card :=
        card_biUnion_le
    _ ≤ ∑ j : Fin q, ∑ t ∈ lineT x0 W ρ T (j.val + 1),
          (A.H.filter fun η => η.2.1 < t ∧ t ≤ η.2.2 ∧ lam (A.d η.1) < β j + h + 1).card :=
        sum_le_sum fun j _ => card_biUnion_le
    _ ≤ ∑ j : Fin q, ∑ _t ∈ lineT x0 W ρ T (j.val + 1), N * (2 ^ (β j + h + 1) - 1) :=
        sum_le_sum fun j _ => sum_le_sum fun t _ => hA.overlap t _
    _ = ∑ j : Fin q, (lineT x0 W ρ T (j.val + 1)).card * (N * (2 ^ (β j + h + 1) - 1)) := by
        simp only [sum_const, smul_eq_mul]

/-- Distinct thresholds below `s` have `∑ 2^β < 2^(s+1)`. -/
theorem sum_pow_beta_lt (hβ : StrictMono β) (s : ℕ) :
    ∑ j ∈ univ.filter (fun j : Fin q => β j ≤ s), 2 ^ β j < 2 ^ (s + 1) := by
  classical
  calc ∑ j ∈ univ.filter (fun j : Fin q => β j ≤ s), 2 ^ β j
      = ∑ v ∈ (univ.filter fun j : Fin q => β j ≤ s).image β, 2 ^ v :=
        (sum_image fun x _ y _ h => hβ.injective h).symm
    _ ≤ ∑ v ∈ range (s + 1), 2 ^ v := by
        refine sum_le_sum_of_subset fun v hv => ?_
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hv
        exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hj).2)
    _ < 2 ^ (s + 1) := Fam.sum_pow_two_lt _

/-- **(X5)** Over the hops of the bounded walks, the event counts of the windows at or above theirs
grow in all by at most `N 2^(h+2) ∑ d`: an event of scale `s` is counted by the hops that span it,
of windows `≤ j` with `β_j ≤ s`, of bands at most `β_j + h`. -/
theorem sum_ahop_events_le (hA : A.Valid T) (hβ : StrictMono β) {h : ℕ} (win : ι → Fin q)
    (hwin : ∀ F, lam (A.d F) ≤ β (win F) + h) :
    ∑ j : Fin q, ∑ η ∈ A.H.filter (fun η => win η.1 ≤ j), (nev A β j η.2.2 - nev A β j η.2.1) ≤
      N * 2 ^ (h + 2) * ∑ F, A.d F := by
  classical
  calc ∑ j : Fin q, ∑ η ∈ A.H.filter (fun η => win η.1 ≤ j), (nev A β j η.2.2 - nev A β j η.2.1)
      ≤ ∑ j : Fin q, ∑ η ∈ A.H.filter (fun η => win η.1 ≤ j),
          (univ.filter fun F => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ β j ≤ lam (A.d F)).card :=
        sum_le_sum fun j _ => sum_le_sum fun η _ => nev_sub_le j
    _ = ∑ j : Fin q, ∑ F, ((A.H.filter fun η => win η.1 ≤ j).filter
          fun η => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ β j ≤ lam (A.d F)).card :=
        sum_congr rfl fun j _ => sum_card_filter_comm _ _
          (fun (η : ι × ℕ × ℕ) (F : ι) => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ β j ≤ lam (A.d F))
    _ ≤ ∑ j : Fin q, ∑ F, (if β j ≤ lam (A.d F) then N * 2 ^ (h + 1) * 2 ^ β j else 0) := by
        refine sum_le_sum fun j _ => sum_le_sum fun F _ => ?_
        split_ifs with hF
        · calc ((A.H.filter fun η => win η.1 ≤ j).filter
                fun η => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧ β j ≤ lam (A.d F)).card
              ≤ (A.H.filter fun η => η.2.1 < A.o F ∧ A.o F ≤ η.2.2 ∧
                  lam (A.d η.1) < β j + h + 1).card := by
                refine card_le_card fun η hη => ?_
                obtain ⟨hη1, h1, h2, -⟩ := mem_filter.mp hη
                obtain ⟨hηH, hw⟩ := mem_filter.mp hη1
                have := hwin η.1
                have := hβ.monotone hw
                exact mem_filter.mpr ⟨hηH, h1, h2, by omega⟩
            _ ≤ N * (2 ^ (β j + h + 1) - 1) := hA.overlap _ _
            _ ≤ N * 2 ^ (h + 1) * 2 ^ β j := by
                rw [mul_assoc, ← pow_add, show h + 1 + β j = β j + h + 1 by ring]
                exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        · exact Nat.le_zero.mpr (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun η _ h' => hF h'.2.2))
    _ = ∑ F, N * 2 ^ (h + 1) * ∑ j ∈ univ.filter (fun j : Fin q => β j ≤ lam (A.d F)), 2 ^ β j := by
        rw [sum_comm]
        refine sum_congr rfl fun F _ => ?_
        rw [sum_filter, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ F, N * 2 ^ (h + 2) * A.d F := by
        refine sum_le_sum fun F _ => ?_
        have h1 := sum_pow_beta_lt hβ (lam (A.d F))
        have h2 : 2 ^ lam (A.d F) ≤ A.d F := Nat.pow_log_le_self 2 (by have := hA.d_pos F; omega)
        calc N * 2 ^ (h + 1) * ∑ j ∈ univ.filter (fun j : Fin q => β j ≤ lam (A.d F)), 2 ^ β j
            ≤ N * 2 ^ (h + 1) * 2 ^ (lam (A.d F) + 1) := Nat.mul_le_mul_left _ h1.le
          _ = N * 2 ^ (h + 2) * 2 ^ lam (A.d F) := by ring
          _ ≤ N * 2 ^ (h + 2) * A.d F := Nat.mul_le_mul_left _ h2
    _ = N * 2 ^ (h + 2) * ∑ F, A.d F := by rw [mul_sum]

end Exchange

end BoundedNesting
