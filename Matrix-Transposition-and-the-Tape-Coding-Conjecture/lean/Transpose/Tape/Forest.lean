import Transpose.Tape.Passes
import Transpose.Tape.Counting

/-!
# The dependency forest: addresses, invariants, Forest and Disjointness Lemmas, information count

* Convex step sets (`IsConvex`, `convex_eq_Icc`), addresses, roots and children, the node
  invariant (`forestNode_inv`), closure under children (`forestNode_append`).
* `exists_append_step_mem_forest`: the step appending an output position of a segment lies in the
  segment's forest.
* The Forest Lemma: `forest_entryPoints_subset`, `forest_entryCells_subset` and their counts.
* The information count is proved on a set `W` of co-entropy `≤ m` (`forest_info_on`, from the Cut
  Lemma on a set, `cut_bound_on_coentropy`); `forest_info` is its case `W` = all matrix inputs,
  `m = 0`.
* The Disjointness Lemma: time separation (`forestNode_timeSep`) and disjointness
  (`forestNode_disjoint`).
-/

namespace Transpose.Tape.Impl

open Transpose

/-! ### Convex step sets and first steps -/

/-- A step set is convex (an interval of steps). -/
def IsConvex (J : Finset ℕ) : Prop := ∀ x ∈ J, ∀ y ∈ J, ∀ z, x ≤ z → z ≤ y → z ∈ J

/-- A nonempty convex set is the interval between its least and its greatest element. -/
theorem convex_eq_Icc {J : Finset ℕ} (hc : IsConvex J) (hJ : J.Nonempty) :
    J = Finset.Icc (J.min' hJ) (J.max' hJ) := by
  ext τ
  simp only [Finset.mem_Icc]
  constructor
  · intro h; exact ⟨J.min'_le τ h, J.le_max' τ h⟩
  · rintro ⟨h1, h2⟩; exact hc _ (J.min'_mem hJ) _ (J.max'_mem hJ) τ h1 h2

theorem firstStep_mem {J : Finset ℕ} (hJ : J.Nonempty) : firstStep J ∈ J := by
  simp only [firstStep, hJ, dite_true]; exact Finset.min'_mem J hJ

theorem firstStep_le {J : Finset ℕ} {τ : ℕ} (hτ : τ ∈ J) : firstStep J ≤ τ := by
  have hJ : J.Nonempty := ⟨τ, hτ⟩
  simp only [firstStep, hJ, dite_true]; exact Finset.min'_le J τ hτ

theorem mem_passSteps {p : ℕ → ℕ} {P τ : ℕ} : τ ∈ passSteps p P ↔ p P ≤ τ ∧ τ < p (P + 1) := by
  simp [passSteps]

/-! ### Addresses -/

theorem nil_mem_addrsBelow (k P : ℕ) : ([] : List (ℕ × Fin k)) ∈ addrsBelow k P := by
  induction P with
  | zero => simp [addrsBelow]
  | succ P ih => simp only [addrsBelow]; exact Finset.mem_union_left _ ih

theorem mem_addrsBelow {k P : ℕ} {l : List (ℕ × Fin k)} :
    l ∈ addrsBelow k P ↔ l = [] ∨ ∃ x l', l = x :: l' ∧ x.1 < P ∧ l' ∈ addrsBelow k x.1 := by
  induction P generalizing l with
  | zero => simp [addrsBelow]
  | succ P ih =>
    simp only [addrsBelow, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨t, l', hl', rfl⟩)
      · rcases ih.1 h with h | ⟨x, l', rfl, hx, hl'⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, l', rfl, by omega, hl'⟩
      · exact Or.inr ⟨(P, t), l', rfl, by simp, hl'⟩
    · rintro (rfl | ⟨x, l', rfl, hx, hl'⟩)
      · exact Or.inl (nil_mem_addrsBelow k P)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hlt | heq
        · exact Or.inl (ih.2 (Or.inr ⟨x, l', rfl, hlt, hl'⟩))
        · right
          refine ⟨x.2, l', ?_, ?_⟩
          · rw [← heq]; exact hl'
          · rw [← heq]

theorem card_addrsBelow_le (k P : ℕ) : (addrsBelow k P).card ≤ (k + 1) ^ P := by
  induction P with
  | zero => simp [addrsBelow]
  | succ P ih =>
    simp only [addrsBelow]
    calc (addrsBelow k P ∪ Finset.univ.biUnion (fun t : Fin k =>
            (addrsBelow k P).image (fun l => (P, t) :: l))).card
        ≤ (addrsBelow k P).card + (Finset.univ.biUnion (fun t : Fin k =>
            (addrsBelow k P).image (fun l => (P, t) :: l))).card := Finset.card_union_le _ _
      _ ≤ (addrsBelow k P).card + ∑ t : Fin k, ((addrsBelow k P).image (fun l => (P, t) :: l)).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ (addrsBelow k P).card + ∑ _t : Fin k, (addrsBelow k P).card :=
          Nat.add_le_add_left (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)) _
      _ = (k + 1) * (addrsBelow k P).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
      _ ≤ (k + 1) * (k + 1) ^ P := Nat.mul_le_mul_left _ ih
      _ = (k + 1) ^ (P + 1) := by ring

theorem card_addresses_le (k r : ℕ) : (addresses k r).card ≤ addrCount k r := by
  unfold addresses addrCount
  calc ((Finset.range r).biUnion (fun P₀ => (addrsBelow k P₀).image (fun l => (P₀, l)))).card
      ≤ ∑ P₀ ∈ Finset.range r, ((addrsBelow k P₀).image (fun l => (P₀, l))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ P₀ ∈ Finset.range r, (k + 1) ^ P₀ :=
        Finset.sum_le_sum (fun P₀ _ => le_trans Finset.card_image_le (card_addrsBelow_le k P₀))

theorem mem_addresses {k r : ℕ} {α : ℕ × List (ℕ × Fin k)} :
    α ∈ addresses k r ↔ α.1 < r ∧ α.2 ∈ addrsBelow k α.1 := by
  obtain ⟨P₀, l⟩ := α
  simp only [addresses, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨P, hP, l', hl', rfl, rfl⟩; exact ⟨hP, hl'⟩
  · rintro ⟨hP, hl⟩; exact ⟨P₀, hP, l, hl, rfl, rfl⟩

/-- The pass of the last entry of an address (the root pass if the list is empty). -/
def lastPass {k : ℕ} : List (ℕ × Fin k) → ℕ → ℕ
  | [], P => P
  | x :: l, _ => lastPass l x.1

theorem lastPass_le {k : ℕ} : ∀ {l : List (ℕ × Fin k)} {P : ℕ}, l ∈ addrsBelow k P →
    lastPass l P ≤ P
  | [], _, _ => le_rfl
  | x :: l, P, h => by
    rcases mem_addrsBelow.1 h with h | ⟨y, l', he, hy, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      show lastPass l x.1 ≤ P
      exact le_trans (lastPass_le hl') (le_of_lt hy)

theorem append_mem_addrsBelow {k : ℕ} (t : Fin k) : ∀ {l : List (ℕ × Fin k)} {P P' : ℕ},
    l ∈ addrsBelow k P → P' < lastPass l P → l ++ [(P', t)] ∈ addrsBelow k P
  | [], P, P', _, hP' => by
    rw [mem_addrsBelow]
    exact Or.inr ⟨(P', t), [], rfl, hP', nil_mem_addrsBelow k P'⟩
  | x :: l, P, P', h, hP' => by
    rcases mem_addrsBelow.1 h with h | ⟨y, l', he, hy, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rw [mem_addrsBelow]
      exact Or.inr ⟨x, l ++ [(P', t)], rfl, hy, append_mem_addrsBelow t hl' hP'⟩

/-! ### Roots and children -/

section Nodes

variable {M : TM} {w : List Bool} {T r : ℕ} {p : ℕ → ℕ}

theorem mem_sSet {h : ℕ → ℤ} {J : Finset ℕ} {P' : ℕ} {c : ℤ} :
    c ∈ sSet h p J P' ↔ (∃ τ ∈ J, h τ = c) ∧ c ≠ h (firstStep J) ∧
      ∃ σ ∈ passSteps p P', IsLastVisitTo h c (firstStep J) σ := by
  classical
  simp only [sSet, Finset.mem_filter, Finset.mem_image]

theorem childNode_subset (h : ℕ → ℤ) (J : Finset ℕ) (P' : ℕ) :
    childNode h p J P' ⊆ passSteps p P' := by
  unfold childNode
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem mem_childNode_iff {h : ℕ → ℤ} {J : Finset ℕ} {P' σ : ℕ} :
    σ ∈ childNode h p J P' ↔ ∃ hS : (sSet h p J P').Nonempty, σ ∈ passSteps p P' ∧
      (sSet h p J P').min' hS ≤ h σ ∧ h σ ≤ (sSet h p J P').max' hS := by
  unfold childNode
  split_ifs with hS
  · simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨hS, h1, h2, h3⟩
    · rintro ⟨_, h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · simp only [Finset.notMem_empty, false_iff, not_exists]
    intro hS'; exact absurd hS' hS

theorem mem_childNode {h : ℕ → ℤ} {J : Finset ℕ} {P' σ : ℕ} (hσ : σ ∈ passSteps p P')
    (hc : h σ ∈ sSet h p J P') : σ ∈ childNode h p J P' :=
  mem_childNode_iff.2 ⟨⟨_, hc⟩, hσ, Finset.min'_le _ _ hc, Finset.le_max' _ _ hc⟩

theorem childNode_convex {h : ℕ → ℤ} {J : Finset ℕ} {P' : ℕ}
    (hm : MonoOn h (p P') (p (P' + 1))) : IsConvex (childNode h p J P') := by
  intro x hx y hy z hxz hzy
  rw [mem_childNode_iff] at hx hy ⊢
  obtain ⟨hS, hxP, hx1, hx2⟩ := hx
  obtain ⟨_, hyP, hy1, hy2⟩ := hy
  rw [mem_passSteps] at hxP hyP
  refine ⟨hS, mem_passSteps.2 ⟨by omega, by omega⟩, ?_, ?_⟩ <;>
  · rcases monoOn_cases hm with up | dn
    · have := up x z (by omega) hxz (by omega)
      have := up z y (by omega) hzy (by omega)
      linarith
    · have := dn x z (by omega) hxz (by omega)
      have := dn z y (by omega) hzy (by omega)
      linarith

theorem rootNode_subset (len : ℕ → ℕ) (o₁ o₂ P : ℕ) : rootNode len p o₁ o₂ P ⊆ passSteps p P :=
  Finset.filter_subset _ _

theorem outLen_mono (M : TM) (w : List Bool) {τ τ' : ℕ} (h : τ ≤ τ') :
    outLen M w τ ≤ outLen M w τ' :=
  outRev_length_mono w h

theorem outLen_succ_le (M : TM) (w : List Bool) (τ : ℕ) : outLen M w (τ + 1) ≤ outLen M w τ + 1 := by
  have := outRev_length_succ (M := M) w τ
  simp only [outLen]
  split_ifs at this <;> omega

theorem rootNode_convex (M : TM) (w : List Bool) (o₁ o₂ P : ℕ) :
    IsConvex (rootNode (outLen M w) p o₁ o₂ P) := by
  classical
  intro x hx y hy z hxz hzy
  simp only [rootNode, Finset.mem_filter, mem_passSteps] at hx hy ⊢
  have h1 := outLen_mono M w hzy
  have h2 := outLen_mono M w (show x + 1 ≤ z + 1 by omega)
  exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-! ### The node invariant -/

/-- Folding children keeps a node convex and inside the pass of the last entry. -/
theorem foldl_inv (hp : PassPartition M w T r p) :
    ∀ (l : List (ℕ × Fin M.k)) (J : Finset ℕ) (P : ℕ), P < r → J ⊆ passSteps p P → IsConvex J →
      l ∈ addrsBelow M.k P →
      l.foldl (fun J x => childNode (fun τ => workTraj M w τ x.2) p J x.1) J ⊆
          passSteps p (lastPass l P) ∧
        IsConvex (l.foldl (fun J x => childNode (fun τ => workTraj M w τ x.2) p J x.1) J)
  | [], J, P, _, hJ, hc, _ => ⟨hJ, hc⟩
  | x :: l, J, P, hP, _, _, hl => by
    rcases mem_addrsBelow.1 hl with h | ⟨y, l', he, hy, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      simp only [List.foldl_cons, lastPass]
      exact foldl_inv hp l _ x.1 (by omega) (childNode_subset _ _ _)
        (childNode_convex ((hp.2.2.2 x.1 (by omega)).2 x.2)) hl'

theorem lastPass_lt {k : ℕ} {α : ℕ × List (ℕ × Fin k)} {r : ℕ} (hα : α ∈ addresses k r) :
    lastPass α.2 α.1 < r :=
  lt_of_le_of_lt (lastPass_le (mem_addresses.1 hα).2) (mem_addresses.1 hα).1

theorem forestNode_inv (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)}
    (hα : α ∈ addresses M.k r) (o₁ o₂ : ℕ) :
    forestNode M w p o₁ o₂ α.1 α.2 ⊆ passSteps p (lastPass α.2 α.1) ∧
      IsConvex (forestNode M w p o₁ o₂ α.1 α.2) :=
  foldl_inv hp α.2 _ α.1 (mem_addresses.1 hα).1 (rootNode_subset _ _ _ _)
    (rootNode_convex M w _ _ _) (mem_addresses.1 hα).2

/-- **Closure:** the child of a node at an earlier pass is the node at the extended address. -/
theorem forestNode_append (o₁ o₂ P₀ : ℕ) (l : List (ℕ × Fin M.k)) (P' : ℕ) (t : Fin M.k) :
    forestNode M w p o₁ o₂ P₀ (l ++ [(P', t)]) =
      childNode (fun τ => workTraj M w τ t) p (forestNode M w p o₁ o₂ P₀ l) P' := by
  simp [forestNode, List.foldl_append]

theorem forest_subset (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    ∀ τ ∈ forest M w p r o₁ o₂, τ < T := by
  intro τ hτ
  obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτ
  have h1 := (forestNode_inv hp hα o₁ o₂).1 hτα
  rw [mem_passSteps] at h1
  have := pp_le_T hp (show lastPass α.2 α.1 + 1 ≤ r from lastPass_lt hα)
  omega

/-- The step that appends output position `o ∈ [o₁, o₂)` (with `o` below the output length at `T`)
lies in the root of its pass, hence in the forest of `[o₁, o₂)`. -/
theorem exists_append_step_mem_forest (hp : PassPartition M w T r p) {o₁ o₂ o : ℕ}
    (ho₁ : o₁ ≤ o) (ho₂ : o < o₂) (ho : o < (run M w T).outRev.length) :
    ∃ τ < T, τ ∈ forest M w p r o₁ o₂ ∧ (outBit M w τ).isSome ∧ (run M w τ).outRev.length = o := by
  classical
  obtain ⟨τ, hτT, hsome, hlen⟩ := exists_append_step w ho
  obtain ⟨P, hPr, hP1, hP2⟩ := pp_exists_pass hp hτT
  refine ⟨τ, hτT, Finset.mem_biUnion.2 ⟨(P, []), mem_addresses.2 ⟨hPr, nil_mem_addrsBelow _ _⟩, ?_⟩,
    hsome, hlen⟩
  show τ ∈ rootNode (outLen M w) p o₁ o₂ P
  have := outRev_length_succ (M := M) w τ
  simp only [hsome, ite_true] at this
  simp only [rootNode, Finset.mem_filter, mem_passSteps]
  simp only [outLen]
  exact ⟨⟨hP1, hP2⟩, by omega, by omega⟩

/-! ### The Forest Lemma: entry data of the forest -/

theorem forest_entryPoints_subset (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    entryPoints (forest M w p r o₁ o₂) ⊆
      (addresses M.k r).image (fun α => firstStep (forestNode M w p o₁ o₂ α.1 α.2)) := by
  intro τ hτ
  rw [mem_entryPoints] at hτ
  obtain ⟨hτF, hτ0, hprev⟩ := hτ
  obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτF
  refine Finset.mem_image.2 ⟨α, hα, ?_⟩
  have hconv := (forestNode_inv hp hα o₁ o₂).2
  have hle := firstStep_le hτα
  by_contra hne
  have hlt : firstStep (forestNode M w p o₁ o₂ α.1 α.2) < τ := lt_of_le_of_ne hle hne
  apply hprev
  exact Finset.mem_biUnion.2 ⟨α, hα, hconv _ (firstStep_mem ⟨τ, hτα⟩) τ hτα (τ - 1)
    (by omega) (by omega)⟩

theorem forest_entryPoints_card_le (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    (entryPoints (forest M w p r o₁ o₂)).card ≤ (addresses M.k r).card :=
  le_trans (Finset.card_le_card (forest_entryPoints_subset hp o₁ o₂)) Finset.card_image_le

theorem forest_entryCells_subset (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    entryCells (workTraj M w) (forest M w p r o₁ o₂) ⊆
      (Finset.univ ×ˢ addresses M.k r).image
        (fun x => (x.1, firstStep (forestNode M w p o₁ o₂ x.2.1 x.2.2))) := by
  classical
  rintro ⟨t, τ⟩ hτ
  rw [mem_entryCells] at hτ
  obtain ⟨hτF, σ, hσF, hσ⟩ := hτ
  obtain ⟨α, hα, hτα⟩ := Finset.mem_biUnion.1 hτF
  refine Finset.mem_image.2 ⟨(t, α), by simp [hα], ?_⟩
  simp only [Prod.mk.injEq, true_and]
  set J := forestNode M w p o₁ o₂ α.1 α.2 with hJdef
  set h := fun s => workTraj M w s t with hdef
  obtain ⟨hJsub, hJconv⟩ := forestNode_inv hp hα o₁ o₂
  set P := lastPass α.2 α.1 with hPdef
  have hPr : P < r := lastPass_lt hα
  have ha : firstStep J ≤ τ := firstStep_le hτα
  have haJ : firstStep J ∈ J := firstStep_mem ⟨τ, hτα⟩
  by_contra hne
  have hlt : firstStep J < τ := lt_of_le_of_ne ha hne
  -- the last write is before the node
  have hσa : σ < firstStep J := by
    by_contra hc
    push Not at hc
    exact hσF (Finset.mem_biUnion.2 ⟨α, hα, hJconv _ haJ τ hτα σ hc (le_of_lt hσ.1)⟩)
  -- the cell differs from the cell at the node's first step
  have hne_a : h τ ≠ h (firstStep J) := fun heq => hσ.2.2 _ hσa hlt heq.symm
  -- the Fresh-Cell Lemma: the last write is before the pass
  have hmono : MonoOn h (p P) (p (P + 1)) := (hp.2.2.2 P hPr).2 t
  have haP := mem_passSteps.1 (hJsub haJ)
  have hτP := mem_passSteps.1 (hJsub hτα)
  have hσP : σ < p P := by
    by_contra hc
    push Not at hc
    exact pass_fresh hmono hc hσa ha hτP.2.le hne_a hσ.2.1
  -- the pass of the last write
  have hτT : τ < T := forest_subset hp o₁ o₂ τ hτF
  obtain ⟨P', hP'r, hP'1, hP'2⟩ := pp_exists_pass hp (show σ < T by have := hσ.1; omega)
  have hP'P : P' < P := by
    by_contra hc
    push Not at hc
    have := pp_mono hp hc (le_of_lt hP'r)
    omega
  -- the cell is in the S-set
  have hc : h τ ∈ sSet h p J P' := by
    rw [mem_sSet]
    refine ⟨⟨τ, hτα, rfl⟩, hne_a, σ, mem_passSteps.2 ⟨hP'1, hP'2⟩, hσa, hσ.2.1, ?_⟩
    intro ρ h1 h2
    exact hσ.2.2 ρ h1 (by omega)
  -- the child at the extended address contains the last write
  have hα' : (α.1, α.2 ++ [(P', t)]) ∈ addresses M.k r :=
    mem_addresses.2 ⟨(mem_addresses.1 hα).1, append_mem_addrsBelow t (mem_addresses.1 hα).2 hP'P⟩
  have hσ' : σ ∈ forestNode M w p o₁ o₂ α.1 (α.2 ++ [(P', t)]) := by
    rw [forestNode_append]
    exact mem_childNode (mem_passSteps.2 ⟨hP'1, hP'2⟩)
      (show h σ ∈ sSet h p J P' by rw [hσ.2.1]; exact hc)
  exact hσF (Finset.mem_biUnion.2 ⟨_, hα', hσ'⟩)

theorem forest_entryCells_card_le (hp : PassPartition M w T r p) (o₁ o₂ : ℕ) :
    (entryCells (workTraj M w) (forest M w p r o₁ o₂)).card ≤ M.k * (addresses M.k r).card := by
  calc _ ≤ ((Finset.univ ×ˢ addresses M.k r).image
        (fun x => (x.1, firstStep (forestNode M w p o₁ o₂ x.2.1 x.2.2)))).card :=
        Finset.card_le_card (forest_entryCells_subset hp o₁ o₂)
    _ ≤ (Finset.univ ×ˢ addresses M.k r).card := Finset.card_image_le
    _ = M.k * (addresses M.k r).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-! ### The information count -/

/-- The comb bits of a segment that its forest does not read lie in the forest's cut set (the
output of `w₀` has `n² b` bits). -/
theorem comb_diff_subset_cutSet_on {n b : ℕ} {w₀ : List Bool} (hlen : outLen M w₀ T = n * n * b)
    (hp : PassPartition M w₀ T r p) {o₁ o₂ : ℕ} :
    combSet n b o₁ o₂ \ readSet (inTraj M w₀) (n * n * b) (forest M w₀ p r o₁ o₂) ⊆
      cutSet M w₀ n b (forest M w₀ p r o₁ o₂) := by
  classical
  intro d hd
  simp only [Finset.mem_sdiff, combSet, readSet, Finset.mem_filter, Finset.mem_range, not_and,
    not_exists] at hd
  obtain ⟨⟨hdL, ho1, ho2⟩, hdr⟩ := hd
  obtain ⟨τ, -, hτF, hsome, hlen'⟩ := exists_append_step_mem_forest hp ho1 ho2 (by
    have := tpos_lt hdL; simp only [outLen] at hlen; omega)
  simp only [cutSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨hdL, fun τ hτ heq => hdr hdL τ hτ heq, τ, hτF, hsome, hlen'⟩

/-- **The information count on a set**: a group pays the co-entropy `m` on top of its side
information (the Cut Lemma on a set, `cut_bound_on_coentropy`, applied to the forest). -/
theorem forest_info_on {n b : ℕ} {W : Set (List Bool)} (hobl : ObliviousOn M W T)
    (hcorr : ∀ w ∈ W, ∃ A : Matrix, w = encode n b A ∧
      (run M w T).outRev.reverse = encode n b (transpose A))
    {w₀ : List Bool} (hw₀ : w₀ ∈ W) (hp : PassPartition M w₀ T r p) {m : ℕ}
    (hco : 2 ^ (n * n * b) ≤ 2 ^ m * W.ncard) {o₁ o₂ : ℕ} :
    2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M w₀) (n * n * b) (forest M w₀ p r o₁ o₂)).card ≤
      2 ^ m * ((M.q + 1) * (M.g + 1) ^ M.k) ^ (addresses M.k r).card := by
  have h2 := Finset.card_le_card
    (comb_diff_subset_cutSet_on (o₁ := o₁) (o₂ := o₂) (outLen_of_classCorrect hcorr hw₀) hp)
  calc _ ≤ 2 ^ (cutSet M w₀ n b (forest M w₀ p r o₁ o₂)).card :=
        Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ _ := cut_bound_on_coentropy hobl hcorr hw₀ (forest_subset hp o₁ o₂) hco
    _ ≤ _ := Nat.mul_le_mul_left _ (by
        rw [mul_pow, ← pow_mul]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (forest_entryPoints_card_le hp o₁ o₂))
          (Nat.pow_le_pow_right (by omega) (forest_entryCells_card_le hp o₁ o₂)))

/-- **The information count** (the Forest Lemma with the Cut Lemma): the case `W` = all matrix
inputs, `m = 0` of `forest_info_on`. -/
theorem forest_info {n b : ℕ} (hobl : ObliviousOn M (matrixInputs n b) T)
    (hcorr : Transposes M n b) {w₀ : List Bool} (hw₀ : w₀ ∈ matrixInputs n b)
    (hp : PassPartition M w₀ T r p) {o₁ o₂ : ℕ} :
    2 ^ (combSet n b o₁ o₂ \ readSet (inTraj M w₀) (n * n * b) (forest M w₀ p r o₁ o₂)).card ≤
      ((M.q + 1) * (M.g + 1) ^ M.k) ^ (addresses M.k r).card := by
  have h := forest_info_on (m := 0) (o₁ := o₁) (o₂ := o₂) hobl
    (fun w hw => correct_of_transposes hcorr hw (hobl.1 w hw)) hw₀ hp
    (by rw [ncard_matrixInputs, pow_zero, one_mul])
  rwa [pow_zero, one_mul] at h

/-! ### The Disjointness Lemma: time separation and disjointness -/

/-- Two step sets are time-separated: one lies entirely before the other. -/
def TimeSep (J₁ J₂ : Finset ℕ) : Prop :=
  (∀ x ∈ J₁, ∀ y ∈ J₂, x < y) ∨ (∀ x ∈ J₁, ∀ y ∈ J₂, y < x)

theorem timeSep_symm {J₁ J₂ : Finset ℕ} (h : TimeSep J₁ J₂) : TimeSep J₂ J₁ := by
  rcases h with h | h
  · exact Or.inr (fun x hx y hy => h y hy x hx)
  · exact Or.inl (fun x hx y hy => h y hy x hx)

theorem disjoint_of_timeSep {J₁ J₂ : Finset ℕ} (h : TimeSep J₁ J₂) : Disjoint J₁ J₂ := by
  rw [Finset.disjoint_left]
  intro x hx hx2
  rcases h with h | h
  · exact lt_irrefl _ (h x hx x hx2)
  · exact lt_irrefl _ (h x hx x hx2)

/-- If `J₁` lies before `J₂` in a pass where `h` is monotone, the S-sets of `J₁` lie strictly on
one side of the S-sets of `J₂`: all cells of `J₁` are on one side of the cell `h a₂` at the first
step of `J₂`, and all cells of the S-set of `J₂` strictly on the other. -/
theorem sSet_sep {h : ℕ → ℤ} {J₁ J₂ : Finset ℕ} {P P' : ℕ}
    (hm : MonoOn h (p P) (p (P + 1))) (h1 : J₁ ⊆ passSteps p P) (h2 : J₂ ⊆ passSteps p P)
    (hsep : ∀ x ∈ J₁, ∀ y ∈ J₂, x < y) :
    (∀ c ∈ sSet h p J₁ P', ∀ c' ∈ sSet h p J₂ P', c < c') ∨
      (∀ c ∈ sSet h p J₁ P', ∀ c' ∈ sSet h p J₂ P', c' < c) := by
  have key : ∀ c ∈ sSet h p J₁ P', ∀ c' ∈ sSet h p J₂ P', ∃ τ ∈ J₁, ∃ τ' ∈ J₂,
      c = h τ ∧ c' = h τ' ∧ h τ' ≠ h (firstStep J₂) := by
    intro c hc c' hc'
    rw [mem_sSet] at hc hc'
    obtain ⟨⟨τ, hτ, rfl⟩, -, -⟩ := hc
    obtain ⟨⟨τ', hτ', rfl⟩, hne, -⟩ := hc'
    exact ⟨τ, hτ, τ', hτ', rfl, rfl, hne⟩
  rcases monoOn_cases hm with up | dn
  · left
    intro c hc c' hc'
    obtain ⟨τ, hτ, τ', hτ', rfl, rfl, hne⟩ := key c hc c' hc'
    have ha : firstStep J₂ ∈ J₂ := firstStep_mem ⟨τ', hτ'⟩
    have hτa := hsep τ hτ _ ha
    have haτ' := firstStep_le hτ'
    have m1 := mem_passSteps.1 (h1 hτ)
    have m2 := mem_passSteps.1 (h2 ha)
    have m3 := mem_passSteps.1 (h2 hτ')
    have e1 := up τ (firstStep J₂) m1.1 (le_of_lt hτa) (le_of_lt m2.2)
    have e2 := up (firstStep J₂) τ' m2.1 haτ' (le_of_lt m3.2)
    exact lt_of_le_of_lt e1 (lt_of_le_of_ne e2 (Ne.symm hne))
  · right
    intro c hc c' hc'
    obtain ⟨τ, hτ, τ', hτ', rfl, rfl, hne⟩ := key c hc c' hc'
    have ha : firstStep J₂ ∈ J₂ := firstStep_mem ⟨τ', hτ'⟩
    have hτa := hsep τ hτ _ ha
    have haτ' := firstStep_le hτ'
    have m1 := mem_passSteps.1 (h1 hτ)
    have m2 := mem_passSteps.1 (h2 ha)
    have m3 := mem_passSteps.1 (h2 hτ')
    have e1 := dn τ (firstStep J₂) m1.1 (le_of_lt hτa) (le_of_lt m2.2)
    have e2 := dn (firstStep J₂) τ' m2.1 haτ' (le_of_lt m3.2)
    exact lt_of_lt_of_le (lt_of_le_of_ne e2 hne) e1

/-- Children whose S-sets are strictly ordered are time-separated (the head is monotone in the
child's pass). -/
theorem childNode_sep {h : ℕ → ℤ} {J₁ J₂ : Finset ℕ} {P' : ℕ}
    (hm : MonoOn h (p P') (p (P' + 1)))
    (hc : ∀ c ∈ sSet h p J₁ P', ∀ c' ∈ sSet h p J₂ P', c < c') :
    TimeSep (childNode h p J₁ P') (childNode h p J₂ P') := by
  have key : ∀ x ∈ childNode h p J₁ P', ∀ y ∈ childNode h p J₂ P', h x < h y := by
    intro x hx y hy
    rw [mem_childNode_iff] at hx hy
    obtain ⟨hS₁, -, -, hx2⟩ := hx
    obtain ⟨hS₂, -, hy1, -⟩ := hy
    have := hc _ (Finset.max'_mem _ hS₁) _ (Finset.min'_mem _ hS₂)
    linarith
  rcases monoOn_cases hm with up | dn
  · left
    intro x hx y hy
    by_contra hc'
    push Not at hc'
    have mx := mem_passSteps.1 (childNode_subset h J₁ P' hx)
    have my := mem_passSteps.1 (childNode_subset h J₂ P' hy)
    have := up y x my.1 hc' (le_of_lt mx.2)
    have := key x hx y hy
    linarith
  · right
    intro x hx y hy
    by_contra hc'
    push Not at hc'
    have mx := mem_passSteps.1 (childNode_subset h J₁ P' hx)
    have my := mem_passSteps.1 (childNode_subset h J₂ P' hy)
    have := dn x y mx.1 hc' (le_of_lt my.2)
    have := key x hx y hy
    linarith

/-- Children of time-separated nodes in one pass are time-separated. -/
theorem childNode_timeSep {h : ℕ → ℤ} {J₁ J₂ : Finset ℕ} {P P' : ℕ}
    (hm : MonoOn h (p P) (p (P + 1))) (hm' : MonoOn h (p P') (p (P' + 1)))
    (h1 : J₁ ⊆ passSteps p P) (h2 : J₂ ⊆ passSteps p P) (hsep : TimeSep J₁ J₂) :
    TimeSep (childNode h p J₁ P') (childNode h p J₂ P') := by
  rcases hsep with hsep | hsep
  · rcases sSet_sep (P' := P') hm h1 h2 hsep with hc | hc
    · exact childNode_sep hm' hc
    · exact timeSep_symm (childNode_sep hm' (fun c hc' c' hc'' => hc c' hc'' c hc'))
  · rcases sSet_sep (P' := P') hm h2 h1 (fun x hx y hy => hsep y hy x hx) with hc | hc
    · exact timeSep_symm (childNode_sep hm' hc)
    · exact childNode_sep hm' (fun c hc' c' hc'' => hc c' hc'' c hc')

theorem foldl_timeSep (hp : PassPartition M w T r p) :
    ∀ (l : List (ℕ × Fin M.k)) (J₁ J₂ : Finset ℕ) (P : ℕ), P < r → J₁ ⊆ passSteps p P →
      J₂ ⊆ passSteps p P → TimeSep J₁ J₂ → l ∈ addrsBelow M.k P →
      TimeSep (l.foldl (fun J x => childNode (fun τ => workTraj M w τ x.2) p J x.1) J₁)
        (l.foldl (fun J x => childNode (fun τ => workTraj M w τ x.2) p J x.1) J₂)
  | [], _, _, _, _, _, _, hsep, _ => hsep
  | x :: l, J₁, J₂, P, hP, h1, h2, hsep, hl => by
    rcases mem_addrsBelow.1 hl with h | ⟨y, l', he, hy, hl'⟩
    · exact absurd h (List.cons_ne_nil _ _)
    · obtain ⟨rfl, rfl⟩ := List.cons.inj he
      simp only [List.foldl_cons]
      exact foldl_timeSep hp l _ _ x.1 (by omega) (childNode_subset _ _ _)
        (childNode_subset _ _ _)
        (childNode_timeSep ((hp.2.2.2 P hP).2 x.2) ((hp.2.2.2 x.1 (by omega)).2 x.2) h1 h2 hsep)
        hl'

/-- The roots of an earlier segment precede those of a later one. -/
theorem rootNode_before (M : TM) (w : List Bool) {o₁ o₂ o₁' o₂' P : ℕ} (h : o₂ ≤ o₁') :
    ∀ x ∈ rootNode (outLen M w) p o₁ o₂ P, ∀ y ∈ rootNode (outLen M w) p o₁' o₂' P, x < y := by
  classical
  intro x hx y hy
  simp only [rootNode, Finset.mem_filter] at hx hy
  by_contra hc
  push Not at hc
  rcases Nat.lt_or_ge y x with hlt | hge
  · have := outLen_mono M w (show y + 1 ≤ x by omega); omega
  · have hxy : y = x := le_antisymm hc hge
    subst hxy
    have := outLen_succ_le M w y; omega

/-- **The Disjointness Lemma, time form.** At a fixed address, the nodes of an earlier and a later
segment are time-separated. -/
theorem forestNode_timeSep (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)}
    (hα : α ∈ addresses M.k r) {o₁ o₂ o₁' o₂' : ℕ} (h : o₂ ≤ o₁') :
    TimeSep (forestNode M w p o₁ o₂ α.1 α.2) (forestNode M w p o₁' o₂' α.1 α.2) :=
  foldl_timeSep hp α.2 _ _ α.1 (mem_addresses.1 hα).1 (rootNode_subset _ _ _ _)
    (rootNode_subset _ _ _ _) (Or.inl (rootNode_before M w h)) (mem_addresses.1 hα).2

/-- **The Disjointness Lemma.** -/
theorem forestNode_disjoint (hp : PassPartition M w T r p) {α : ℕ × List (ℕ × Fin M.k)}
    (hα : α ∈ addresses M.k r) {o₁ o₂ o₁' o₂' : ℕ} (h : o₂ ≤ o₁') :
    Disjoint (forestNode M w p o₁ o₂ α.1 α.2) (forestNode M w p o₁' o₂' α.1 α.2) :=
  disjoint_of_timeSep (forestNode_timeSep hp hα h)

end Nodes

end Transpose.Tape.Impl
