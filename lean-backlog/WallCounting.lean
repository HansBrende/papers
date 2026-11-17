import WallSubgroups

/-!
# The counting form of the label bound

A labelling `f u : X → β` of a finite set `X` is a partition of `X`. The permutations of `X`
preserving the labels at all vertices of a set `S` are those preserving the joint label
`x ↦ (f u x)_{u ∈ S}`; their number is the product, over the classes of the common refinement,
of the factorial of the class size (`classFactorial`). This file restates the label form of the
subgroup hypothesis as a statement about these counts.

* The dictionary: the order of the intersection of label stabilisers (`card_meet_labelStabilizer`),
  the relative index (`relIndex_mul_classFactorial`), the index of the total intersection
  (`index_mul_classFactorial`), and inclusion of stabilisers as refinement of partitions
  (`meet_le_labelStabilizer_iff`).
* The label form and the counting form are equivalent at every size
  (`labelBoundAt_iff_countingBoundAt`).
* The restricted counting form, for labels that separate points and `Q = q ^ |X|`, follows
  from the counting form (`separatedCountingBoundAt_of_countingBoundAt`) and still bounds every
  code (`card_le_of_separatedCountingBoundAt`); one common deficit for it implies the
  conjecture (`conjecture_of_separatedCountingCommonDeficit`).

Nothing here asserts any of these hypotheses.
-/

namespace LeanBacklog.WallCounting

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells
open LeanBacklog.WallBipartite LeanBacklog.WallBundle LeanBacklog.WallSubgroups

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- The joint label of `x` on the vertex set `S`: its labels at the vertices of `S`, nothing
elsewhere. -/
def joint {X β : Type} {n m : ℕ} (f : Fin m ⊕ Fin n → X → β) (S : Finset (Fin m ⊕ Fin n))
    (x : X) : Fin m ⊕ Fin n → Option β :=
  fun u => if u ∈ S then some (f u x) else none

/-- The product, over the classes of the common refinement of the partitions `f u`, `u ∈ S`, of
the factorial of the class size. -/
def classFactorial {X β : Type} [Fintype X] [DecidableEq β] {n m : ℕ}
    (f : Fin m ⊕ Fin n → X → β) (S : Finset (Fin m ⊕ Fin n)) : ℕ :=
  ∏ c ∈ univ.image (joint f S), ((univ.filter fun x => joint f S x = c).card).factorial

/-- The counting form at one size. -/
def CountingBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (X : Type) [Fintype X] [DecidableEq X] (β : Type) [DecidableEq β]
      (f : Fin m ⊕ Fin n → X → β) (Q : ℕ), 2 ≤ Q →
      (∀ u x y, (∀ u' ∈ nbrs H_col H_row u, f u' x = f u' y) → f u x = f u y) →
      (∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
        classFactorial f K ≤ Q ^ newCells K u * classFactorial f (insert u K)) →
      ((Fintype.card X).factorial : ℝ) ≤ (Q : ℝ) ^ v * (classFactorial f univ : ℝ)

/-- The restricted counting form: the labels together separate the points of `X`, and
`Q = q ^ |X|`. -/
def SeparatedCountingBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (X : Type) [Fintype X] [DecidableEq X] (β : Type) [DecidableEq β]
      (f : Fin m ⊕ Fin n → X → β) (q : ℕ), 2 ≤ q →
      (∀ x y, (∀ u, f u x = f u y) → x = y) →
      (∀ u x y, (∀ u' ∈ nbrs H_col H_row u, f u' x = f u' y) → f u x = f u y) →
      (∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
        classFactorial f K ≤ (q ^ Fintype.card X) ^ newCells K u * classFactorial f (insert u K)) →
      ((Fintype.card X).factorial : ℝ) ≤ (q : ℝ) ^ ((Fintype.card X : ℝ) * v)

/-- The counting hypothesis: one deficit for every degree bound and all large sizes. -/
def CountingCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, CountingBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-- The restricted counting hypothesis. -/
def SeparatedCountingCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    SeparatedCountingBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-- The uniform statement of the label (symmetric-group) form. -/
def LabelCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, LabelBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-! ## The dictionary -/

section Dictionary

variable {X β : Type} {n m : ℕ}

theorem mem_labelStabilizer_iff {g : X → β} {σ : Equiv.Perm X} :
    σ ∈ labelStabilizer g ↔ ∀ x, g (σ x) = g x :=
  Iff.rfl

theorem mem_meet_labelStabilizer_iff (f : Fin m ⊕ Fin n → X → β) {S : Finset (Fin m ⊕ Fin n)}
    {σ : Equiv.Perm X} :
    σ ∈ meet (fun u => labelStabilizer (f u)) S ↔ ∀ u ∈ S, ∀ x, f u (σ x) = f u x := by
  rw [mem_meet]
  exact Iff.rfl

theorem joint_comp_eq_iff (f : Fin m ⊕ Fin n → X → β) (S : Finset (Fin m ⊕ Fin n))
    (σ : Equiv.Perm X) :
    joint f S ∘ σ = joint f S ↔ ∀ u ∈ S, ∀ x, f u (σ x) = f u x := by
  constructor
  · intro h u hu x
    have := congrFun (congrFun h x) u
    simpa [joint, hu] using this
  · intro h
    funext x u
    simp only [Function.comp_apply, joint]
    split_ifs with hu
    · rw [h u hu x]
    · rfl

/-- A transposition of two points with the same label preserves the label. -/
theorem label_swap [DecidableEq X] {g : X → β} {x y : X} (h : g x = g y) (z : X) :
    g (Equiv.swap x y z) = g z := by
  rcases eq_or_ne z x with rfl | hx
  · rw [Equiv.swap_apply_left]
    exact h.symm
  rcases eq_or_ne z y with rfl | hy
  · rw [Equiv.swap_apply_right]
    exact h
  rw [Equiv.swap_apply_of_ne_of_ne hx hy]

theorem swap_mem_labelStabilizer [DecidableEq X] {g : X → β} {x y : X} (h : g x = g y) :
    Equiv.swap x y ∈ labelStabilizer g :=
  fun z => label_swap h z

variable [Fintype X] [DecidableEq X] [DecidableEq β]

/-- **The order of an intersection of label stabilisers** is the product of the factorials of
the class sizes of the common refinement. -/
theorem card_meet_labelStabilizer (f : Fin m ⊕ Fin n → X → β) (S : Finset (Fin m ⊕ Fin n)) :
    Nat.card ↥(meet (fun u => labelStabilizer (f u)) S) = classFactorial f S := by
  have e : ↥(meet (fun u => labelStabilizer (f u)) S) ≃
      {g : Equiv.Perm X // joint f S ∘ g = joint f S} :=
    Equiv.subtypeEquivRight (fun σ => by
      rw [mem_meet_labelStabilizer_iff, joint_comp_eq_iff])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, DomMulAct.stabilizer_card']
  unfold classFactorial
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Fintype.card_subtype]

omit [DecidableEq X] in
theorem classFactorial_pos (f : Fin m ⊕ Fin n → X → β) (S : Finset (Fin m ⊕ Fin n)) :
    0 < classFactorial f S :=
  Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

/-- The index of an intersection of label stabilisers times the count is `|X| !`. -/
theorem index_mul_classFactorial (f : Fin m ⊕ Fin n → X → β) (S : Finset (Fin m ⊕ Fin n)) :
    (meet (fun u => labelStabilizer (f u)) S).index * classFactorial f S =
      (Fintype.card X).factorial := by
  rw [← card_meet_labelStabilizer, Subgroup.index_mul_card, Nat.card_eq_fintype_card,
    Fintype.card_perm]

theorem index_mul_classFactorial_univ (f : Fin m ⊕ Fin n → X → β) :
    (meet (fun u => labelStabilizer (f u)) univ).index * classFactorial f univ =
      (Fintype.card X).factorial :=
  index_mul_classFactorial f univ

/-- **The relative index** in terms of the counts. -/
theorem relIndex_mul_classFactorial (f : Fin m ⊕ Fin n → X → β) (K : Finset (Fin m ⊕ Fin n))
    (u : Fin m ⊕ Fin n) :
    (labelStabilizer (f u)).relIndex (meet (fun u => labelStabilizer (f u)) K) *
        classFactorial f (insert u K) = classFactorial f K := by
  set Hs : Fin m ⊕ Fin n → Subgroup (Equiv.Perm X) := fun u => labelStabilizer (f u) with hHs
  have h1 : (meet Hs (insert u K)).index = (Hs u).relIndex (meet Hs K) * (meet Hs K).index := by
    rw [meet_insert, ← Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_mul_index inf_le_right).symm
  have h2 := index_mul_classFactorial f (insert u K)
  have h3 := index_mul_classFactorial f K
  apply Nat.eq_of_mul_eq_mul_left (index_pos' (meet Hs K))
  rw [h3, ← h2, h1]
  ring

omit [Fintype X] in
/-- **Inclusion of stabilisers is refinement of partitions.** -/
theorem meet_le_labelStabilizer_iff (f : Fin m ⊕ Fin n → X → β) (N : Finset (Fin m ⊕ Fin n))
    (u : Fin m ⊕ Fin n) :
    meet (fun u => labelStabilizer (f u)) N ≤ labelStabilizer (f u) ↔
      ∀ x y, (∀ u' ∈ N, f u' x = f u' y) → f u x = f u y := by
  constructor
  · intro h x y hxy
    by_contra hne
    have hs : Equiv.swap x y ∈ meet (fun u => labelStabilizer (f u)) N := by
      rw [mem_meet_labelStabilizer_iff]
      intro u' hu' z
      exact label_swap (hxy u' hu') z
    have := (mem_labelStabilizer_iff.mp (h hs)) x
    rw [Equiv.swap_apply_left] at this
    exact hne this.symm
  · intro h σ hσ
    rw [mem_meet_labelStabilizer_iff] at hσ
    rw [mem_labelStabilizer_iff]
    intro x
    exact h (σ x) x (fun u' hu' => hσ u' hu' x)

omit [DecidableEq X] in
/-- Labels that separate points have trivial common refinement. -/
theorem classFactorial_univ_eq_one (f : Fin m ⊕ Fin n → X → β)
    (hsep : ∀ x y, (∀ u, f u x = f u y) → x = y) : classFactorial f univ = 1 := by
  unfold classFactorial
  apply Finset.prod_eq_one
  intro c _
  rw [Nat.factorial_eq_one]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [mem_filter] at ha hb
  apply hsep
  intro u
  have := congrFun (ha.2.trans hb.2.symm) u
  simpa [joint] using this

end Dictionary

/-! ## The label form and the counting form -/

/-- **The label form and the counting form are equivalent at every size.** -/
theorem labelBoundAt_iff_countingBoundAt {n m w : ℕ} {v : ℝ} :
    LabelBoundAt n m w v ↔ CountingBoundAt n m w v := by
  constructor
  · intro h H_col H_row hcol hrow hsym X _ _ β _ f Q hQ hrec hcap
    have hcap' : ∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
        (labelStabilizer (f u)).relIndex (meet (fun u => labelStabilizer (f u)) K) ≤
          Q ^ newCells K u := by
      intro K u hu
      apply Nat.le_of_mul_le_mul_right _ (classFactorial_pos f (insert u K))
      rw [relIndex_mul_classFactorial]
      exact hcap K u hu
    have hb := h H_col H_row hcol hrow hsym X β f Q hQ
      (fun u => (meet_le_labelStabilizer_iff f _ u).mpr (hrec u)) hcap'
    rw [← index_mul_classFactorial_univ f, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg _)
  · intro h H_col H_row hcol hrow hsym X _ _ β f Q hQ hrec hcap
    classical
    have hb := h H_col H_row hcol hrow hsym X β f Q hQ
      (fun u => (meet_le_labelStabilizer_iff f _ u).mp (hrec u))
      (fun K u hu => by
        rw [← relIndex_mul_classFactorial f K u]
        exact Nat.mul_le_mul_right _ (hcap K u hu))
    rw [← index_mul_classFactorial_univ f, Nat.cast_mul] at hb
    exact le_of_mul_le_mul_right hb (by exact_mod_cast classFactorial_pos f univ)

/-- **The counting form implies its restriction** to separating labels with `Q = q ^ |X|`. -/
theorem separatedCountingBoundAt_of_countingBoundAt {n m w : ℕ} {v : ℝ}
    (h : CountingBoundAt n m w v) : SeparatedCountingBoundAt n m w v := by
  intro H_col H_row hcol hrow hsym X _ _ β _ f q hq hsep hrec hcap
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h0 | hpos
  · rw [h0]
    simp
  have hQ : 2 ≤ q ^ Fintype.card X := le_trans hq (Nat.le_self_pow hpos.ne' _)
  have hb := h H_col H_row hcol hrow hsym X β f (q ^ Fintype.card X) hQ hrec hcap
  rw [classFactorial_univ_eq_one f hsep, Nat.cast_one, mul_one, Nat.cast_pow] at hb
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [Real.rpow_mul hq0, Real.rpow_natCast]
  exact hb

/-! ## The bridge from codes -/

section Bridge

variable {n m : ℕ} {α : Type}

/-- **The restricted counting bound bounds every code**, up to the factor `e`. -/
theorem card_le_of_separatedCountingBoundAt {w : ℕ} {v : ℝ} [Fintype α] [Nonempty α]
    (h : SeparatedCountingBoundAt n m w v)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ Real.exp 1 * (Fintype.card α : ℝ) ^ v := by
  classical
  have hα0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rcases D.eq_empty_or_nonempty with hDe | _
  · rw [hDe, card_empty, Nat.cast_zero]
    exact mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg hα0.le v)
  have hq1 : 1 ≤ Fintype.card α := Fintype.card_pos
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hq | hq
  · have hq' : Fintype.card α = 1 := by omega
    have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hq'.le
    have hle : D.card ≤ 1 := by
      apply card_le_one.mpr
      intro x _ y _
      funext p
      exact Subsingleton.elim _ _
    rw [hq', Nat.cast_one, Real.one_rpow, mul_one]
    have : (D.card : ℝ) ≤ 1 := by exact_mod_cast hle
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hsep : ∀ x y : D, (∀ u, bundleLabel D u x = bundleLabel D u y) → x = y := by
    intro x y hxy
    have hs : Equiv.swap x y ∈ meet (fun u => labelStabilizer (bundleLabel D u)) univ := by
      rw [mem_meet]
      intro u _
      exact swap_mem_labelStabilizer (hxy u)
    rw [meet_univ_eq_bot, Subgroup.mem_bot] at hs
    have := congrArg (fun σ : Equiv.Perm D => σ x) hs
    simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at this
    exact this.symm
  have hb := h H_col H_row hcol hrow hsym D (Fin n × Fin m → Option α) (bundleLabel D)
    (Fintype.card α) hq hsep
    (fun u => (meet_le_labelStabilizer_iff (bundleLabel D) _ u).mp (meet_nbrs_le H_col H_row hD u))
    (fun K u _ => by
      rw [← relIndex_mul_classFactorial (bundleLabel D) K u, Fintype.card_coe]
      exact Nat.mul_le_mul_right _ (relIndex_bundleLabel_le D K u))
  rw [Fintype.card_coe, mul_comm, Real.rpow_mul hα0.le, Real.rpow_natCast] at hb
  exact le_exp_mul_of_factorial_le (Real.rpow_nonneg hα0.le v) hb

end Bridge

/-! ## The implications -/

/-- **The restricted counting hypothesis implies the bipartite common deficit.** -/
theorem bipartiteCommonDeficit_of_separatedCounting (h : SeparatedCountingCommonDeficit) :
    BipartiteCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w η hη => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨max n₀ (⌈2 / η⌉₊ + 1), fun d hd => ?_⟩
  intro H_col H_row D hcol hrow hsym hD
  have h1 := card_le_of_separatedCountingBoundAt (hn₀ d ((le_max_left _ _).trans hd)) H_col
    H_row hcol hrow hsym D hD
  have h2 := exp_one_mul_rpow_le (t := (1 - δ) * (d : ℝ) ^ 2) (two_card_bits d)
    (two_le_mul_sq hη ((le_max_right _ _).trans hd))
  have h3 : (1 - δ) * (d : ℝ) ^ 2 + η * (d : ℝ) ^ 2 = (1 - δ + η) * (d : ℝ) ^ 2 := by ring
  rw [h3] at h2
  exact h1.trans h2

theorem commonDeficit_of_separatedCounting (h : SeparatedCountingCommonDeficit) :
    LeanBacklog.Wall.CommonDeficit :=
  bipartiteCommonDeficit_iff_commonDeficit.mp (bipartiteCommonDeficit_of_separatedCounting h)

/-- **The restricted counting hypothesis implies the conjecture.** -/
theorem conjecture_of_separatedCountingCommonDeficit (h : SeparatedCountingCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCommonDeficit (bipartiteCommonDeficit_of_separatedCounting h)

theorem separatedCountingCommonDeficit_of_counting (h : CountingCommonDeficit) :
    SeparatedCountingCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  exact ⟨n₀, fun n hn => separatedCountingBoundAt_of_countingBoundAt (hn₀ n hn)⟩

theorem countingCommonDeficit_iff_label : CountingCommonDeficit ↔ LabelCommonDeficit := by
  constructor
  · rintro ⟨δ, hδ, hb⟩
    refine ⟨δ, hδ, fun w => ?_⟩
    obtain ⟨n₀, hn₀⟩ := hb w
    exact ⟨n₀, fun n hn => labelBoundAt_iff_countingBoundAt.mpr (hn₀ n hn)⟩
  · rintro ⟨δ, hδ, hb⟩
    refine ⟨δ, hδ, fun w => ?_⟩
    obtain ⟨n₀, hn₀⟩ := hb w
    exact ⟨n₀, fun n hn => labelBoundAt_iff_countingBoundAt.mp (hn₀ n hn)⟩

theorem labelCommonDeficit_of_group (h : GroupCommonDeficit) : LabelCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  exact ⟨n₀, fun n hn => labelBoundAt_of_groupBoundAt (hn₀ n hn)⟩

/-- The counting hypothesis implies the conjecture. -/
theorem conjecture_of_countingCommonDeficit (h : CountingCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_separatedCountingCommonDeficit (separatedCountingCommonDeficit_of_counting h)

/-- The uniform label hypothesis implies the conjecture. -/
theorem conjecture_of_labelCommonDeficit (h : LabelCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_countingCommonDeficit (countingCommonDeficit_iff_label.mpr h)

#print axioms card_meet_labelStabilizer
#print axioms relIndex_mul_classFactorial
#print axioms index_mul_classFactorial_univ
#print axioms meet_le_labelStabilizer_iff
#print axioms classFactorial_pos
#print axioms classFactorial_univ_eq_one
#print axioms labelBoundAt_iff_countingBoundAt
#print axioms separatedCountingBoundAt_of_countingBoundAt
#print axioms card_le_of_separatedCountingBoundAt
#print axioms bipartiteCommonDeficit_of_separatedCounting
#print axioms commonDeficit_of_separatedCounting
#print axioms conjecture_of_separatedCountingCommonDeficit
#print axioms separatedCountingCommonDeficit_of_counting
#print axioms countingCommonDeficit_iff_label
#print axioms labelCommonDeficit_of_group
#print axioms conjecture_of_countingCommonDeficit
#print axioms conjecture_of_labelCommonDeficit

end LeanBacklog.WallCounting
