import MergeDepth.SkeletonPaired

/-!
# Paid degree reduction (Proposition 4.11(c), Lemma 4.7(a))

* `card_coneRel_le`: **Lemma 4.7(a), cone sizes.** If the genie has full depth at most `D`, the cone
  relation has `|N_Γ(q)| ≤ w B`: the ends of the `Γ`-free paths of at most `D` edges from a time
  number at most `B = ∑_{h ≤ D} (k + 1)^h`, by the out-degree bound `card_blockOut_le`
  (`card_fwdLevel_le`), and each contributes the at most `w` input cells of one block.
  `card_stepBall_le` is the same for the balls `B^{D'}` of an oblivious schedule.
* `paid_trimming`: for any relation with `|N(q)| ≤ B'`, the set `H_ϑ` of coordinates whose left port
  has degree more than `ϑ` has `ϑ |H_ϑ| ≤ B' |V|`, and the incidence graph induced on its complement
  has maximum degree at most `max(B', ϑ)`.
* `skel_trimming`: **Proposition 4.11(c)**; `ball_trimming`: the same for relations inside balls
  (Corollary 3.8 of the fifth paper, as used in Lemma 3.14(a)).
-/

namespace MergeDepth

open Finset BoundedNesting DirectedRecovery

variable {k : ℕ}

/-! ### Degrees in the paired incidence graph -/

section Degrees

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
theorem degree_inl (N : V → Finset V) (p : V) :
    (pairedIncidenceGraph N).degree (.inl p) = (univ.filter fun q => p ∈ N q).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (pairedIncidenceGraph N).neighborFinset (.inl p) =
      (univ.filter fun q => p ∈ N q).map Function.Embedding.inr := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v with
    | inl p' => simp
    | inr q => simp
  rw [this, card_map]

omit [DecidableEq V] in
open Classical in
theorem degree_inr (N : V → Finset V) (q : V) :
    (pairedIncidenceGraph N).degree (.inr q) = (N q).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (pairedIncidenceGraph N).neighborFinset (.inr q) = (N q).map Function.Embedding.inl := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v with
    | inl p => simp
    | inr q' => simp
  rw [this, card_map]

open Classical in
/-- The coordinates whose left port has degree more than `ϑ`. -/
noncomputable def heavyCoords (N : V → Finset V) (ϑ : ℕ) : Finset V :=
  univ.filter fun p => ϑ < (pairedIncidenceGraph N).degree (.inl p)

open Classical in
/-- **Paid degree reduction.** If every `N(q)` has at most `B'` elements, then `ϑ |H_ϑ| ≤ B' |V|`,
and the incidence graph induced on the complement of `H_ϑ` has maximum degree at most `max(B', ϑ)`. -/
theorem paid_trimming (N : V → Finset V) {B' : ℕ} (ϑ : ℕ) (hN : ∀ q, (N q).card ≤ B') :
    (heavyCoords N ϑ).card * ϑ ≤ B' * Fintype.card V ∧
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N (heavyCoords N ϑ)ᶜ)).degree v ≤ max B' ϑ := by
  constructor
  · -- double counting of the incidences
    have hsum : ∑ p, (pairedIncidenceGraph N).degree (.inl p) = ∑ q, (N q).card := by
      simp_rw [degree_inl]
      calc ∑ p, (univ.filter fun q => p ∈ N q).card
          = ∑ p, ∑ q, (if p ∈ N q then 1 else 0 : ℕ) := by simp only [card_filter]
        _ = ∑ q, ∑ p, (if p ∈ N q then 1 else 0 : ℕ) := sum_comm
        _ = ∑ q, (N q).card := by
            refine sum_congr rfl fun q _ => ?_
            rw [← card_filter]
            congr 1
            ext p
            simp
    calc (heavyCoords N ϑ).card * ϑ = ∑ _p ∈ heavyCoords N ϑ, ϑ := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ heavyCoords N ϑ, (pairedIncidenceGraph N).degree (.inl p) :=
          sum_le_sum fun p hp => (mem_filter.mp hp).2.le
      _ ≤ ∑ p, (pairedIncidenceGraph N).degree (.inl p) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
      _ = ∑ q, (N q).card := hsum
      _ ≤ ∑ _q : V, B' := sum_le_sum fun q _ => hN q
      _ = B' * Fintype.card V := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]
  · intro v
    cases v with
    | inl p =>
      rw [degree_inl]
      refine le_trans ?_ (le_max_right _ _)
      have hp : p.1 ∉ heavyCoords N ϑ := mem_compl.mp p.2
      have hle : ¬ ϑ < (pairedIncidenceGraph N).degree (.inl p.1) := fun h =>
        hp (mem_filter.mpr ⟨mem_univ _, h⟩)
      rw [degree_inl] at hle
      refine le_trans ?_ (not_lt.mp hle)
      refine card_le_card_of_injOn Subtype.val (fun q hq => ?_) Subtype.val_injective.injOn
      have hq := (mem_filter.mp hq).2
      simp only [inducedNeighborhood, mem_subtype] at hq
      exact mem_filter.mpr ⟨mem_univ _, hq⟩
    | inr q =>
      rw [degree_inr]
      refine le_trans ?_ (le_max_left _ _)
      simp only [inducedNeighborhood]
      rw [card_subtype]
      exact (card_filter_le _ _).trans (hN q.1)

end Degrees

/-! ### Cone sizes -/

open Classical in
/-- The ends of the dependency paths of exactly `h` edges from `t`. -/
noncomputable def fwdLevel (s : Fin k → ℕ → ℤ) (T h t : ℕ) : Finset ℕ :=
  (range (t + 1)).filter fun u => ∃ π : List ℕ, IsDepPath s T (t :: π) ∧ π.length = h ∧
    (t :: π).getLastD t = u

theorem getLastD_le {s : Fin k → ℕ → ℤ} {T t : ℕ} {π : List ℕ} (hp : IsDepPath s T (t :: π)) :
    (t :: π).getLastD t ≤ t := by
  have hmem : (t :: π).getLastD t ∈ t :: π := by
    rw [List.getLastD_cons]; exact List.getLastD_mem_cons
  rcases List.mem_cons.mp hmem with h | h
  · rw [h]
  · exact (isDepPath_lt t π hp _ h).le

open Classical in
/-- Out-degrees at most `k + 1` give at most `(k + 1)^h` ends of paths of `h` edges. -/
theorem card_fwdLevel_le (s : Fin k → ℕ → ℤ) (T : ℕ) :
    ∀ h t, (fwdLevel s T h t).card ≤ (k + 1) ^ h
  | 0, t => by
    refine (card_le_card (show fwdLevel s T 0 t ⊆ {t} from fun u hu => ?_)).trans (by simp)
    obtain ⟨-, π, -, hπ, hu⟩ := mem_filter.mp hu
    rw [List.length_eq_zero_iff] at hπ
    subst hπ
    simp only [List.getLastD_cons, List.getLastD_nil] at hu
    exact mem_singleton.mpr hu.symm
  | h + 1, t => by
    have hsub : fwdLevel s T (h + 1) t ⊆
        ((range T).filter (BlockStep s T t ·)).biUnion fun t' => fwdLevel s T h t' := by
      intro u hu
      obtain ⟨-, π, hπ, hlen, hu⟩ := mem_filter.mp hu
      cases π with
      | nil => simp at hlen
      | cons t' π =>
        obtain ⟨hstep, hπ'⟩ := hπ
        have hlt := depStep_lt_lt hstep
        refine mem_biUnion.mpr ⟨t', mem_filter.mpr ⟨mem_range.mpr (by omega),
          (blockStep_iff s T t t').mpr hstep⟩, mem_filter.mpr ⟨?_, π, hπ', by simpa using hlen, ?_⟩⟩
        · have := getLastD_le hπ'
          simp only [List.getLastD_cons] at hu this
          rw [← hu]
          exact mem_range.mpr (by omega)
        · simp only [List.getLastD_cons] at hu ⊢
          exact hu
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ t' ∈ (range T).filter (BlockStep s T t ·), (fwdLevel s T h t').card
        ≤ ∑ _t' ∈ (range T).filter (BlockStep s T t ·), (k + 1) ^ h :=
          sum_le_sum fun t' _ => card_fwdLevel_le s T h t'
      _ = ((range T).filter (BlockStep s T t ·)).card * (k + 1) ^ h := by
          rw [sum_const, smul_eq_mul]
      _ ≤ (k + 1) * (k + 1) ^ h := Nat.mul_le_mul_right _ (card_blockOut_le s T t)
      _ = (k + 1) ^ (h + 1) := by ring

/-- At most `w` positions lie in one block. -/
theorem card_block_le {L w : ℕ} (hw : 1 ≤ w) (c : ℤ) :
    (univ.filter fun p : Fin L => (p : ℤ) / w = c).card ≤ w := by
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  have hmaps : ∀ p ∈ (univ.filter fun p : Fin L => (p : ℤ) / w = c),
      (p : ℤ) ∈ Ico (w * c) (w * c + w) := by
    intro p hp
    have hp := (mem_filter.mp hp).2
    obtain ⟨b1, b2⟩ := block_bounds hw' (p : ℤ)
    rw [hp] at b1 b2
    exact mem_Ico.mpr ⟨b1, b2⟩
  refine (card_le_card_of_injOn (fun p : Fin L => (p : ℤ)) hmaps ?_).trans (by simp)
  intro p _ p' _ h
  simp only at h
  exact Fin.ext (by exact_mod_cast h)

open Classical in
/-- **Lemma 4.7(a), cone sizes.** If `Γ` has full depth at most `D`, then `|N_Γ(q)| ≤ w B`. -/
theorem card_coneRel_le {w : ℕ} (hw : 1 ≤ w) {z : Tp k → ℕ → ℤ} {T D : ℕ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    {L : ℕ} (ot : ℕ → ℕ) (dm : Fin L → ℕ) (q : Fin L) :
    (coneRel w z T Γ ot dm q).card ≤ w * ∑ h ∈ range (D + 1), (k + 1) ^ h := by
  set s : Fin k → ℕ → ℤ := fun j => skel w (z (some (some j)))
  have hsub : coneRel w z T Γ ot dm q ⊆ (range (D + 1)).biUnion fun h =>
      (fwdLevel s T h (ot (dm q))).biUnion fun u =>
        univ.filter fun p : Fin L => (p : ℤ) / w = z none u / w := by
    intro p hp
    obtain ⟨π, hπ, hfree, hpu⟩ := (mem_filter.mp hp).2
    have hlen := hdepth _ hπ hfree
    simp only [List.length_cons] at hlen
    refine mem_biUnion.mpr ⟨π.length, mem_range.mpr (by omega), mem_biUnion.mpr
      ⟨(ot (dm q) :: π).getLastD (ot (dm q)), mem_filter.mpr ⟨mem_range.mpr
        (by have := getLastD_le hπ; omega), π, hπ, rfl, rfl⟩, mem_filter.mpr ⟨mem_univ _, hpu⟩⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [mul_sum]
  refine sum_le_sum fun h _ => card_biUnion_le.trans ?_
  calc ∑ u ∈ fwdLevel s T h (ot (dm q)),
        (univ.filter fun p : Fin L => (p : ℤ) / w = z none u / w).card
      ≤ ∑ _u ∈ fwdLevel s T h (ot (dm q)), w := sum_le_sum fun u _ => card_block_le hw _
    _ = (fwdLevel s T h (ot (dm q))).card * w := by rw [sum_const, smul_eq_mul]
    _ ≤ (k + 1) ^ h * w := Nat.mul_le_mul_right _ (card_fwdLevel_le s T h (ot (dm q)))
    _ = w * (k + 1) ^ h := by ring

open Classical in
/-- The balls of an oblivious schedule have at most `B_{D'} = ∑_{h ≤ D'} (k + 1)^h` positions. -/
theorem card_stepBall_le {L : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (rdStep : ℕ → Option (Fin L))
    (r t : ℕ) : (stepBall xs T rdStep r t).card ≤ ∑ h ∈ range (r + 1), (k + 1) ^ h := by
  have hsub : stepBall xs T rdStep r t ⊆ (range (r + 1)).biUnion fun h =>
      (fwdLevel xs T h t).biUnion fun u => (rdStep u).toFinset := by
    intro j hj
    obtain ⟨π, hπ, hlen, hrd⟩ := (mem_filter.mp hj).2
    refine mem_biUnion.mpr ⟨π.length, mem_range.mpr (by omega), mem_biUnion.mpr
      ⟨(t :: π).getLastD t, mem_filter.mpr ⟨mem_range.mpr (by have := getLastD_le hπ; omega),
        π, hπ, rfl, rfl⟩, by rw [hrd]; simp⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun h _ => ?_))
  refine card_biUnion_le.trans ?_
  calc ∑ u ∈ fwdLevel xs T h t, (rdStep u).toFinset.card ≤ ∑ _u ∈ fwdLevel xs T h t, 1 :=
        sum_le_sum fun u _ => by cases rdStep u <;> simp
    _ = (fwdLevel xs T h t).card := by simp
    _ ≤ (k + 1) ^ h := card_fwdLevel_le xs T h t

/-! ### Proposition 4.11(c) -/

open Classical in
/-- **Proposition 4.11(c).** For every `ϑ`, the coordinates `H_ϑ` whose left port has degree more than
`ϑ` in the incidence graph of `N_Γ` satisfy `ϑ |H_ϑ| ≤ w B L`, and the incidence graph induced on the
complement of `H_ϑ` has maximum degree at most `max(w B, ϑ)`. -/
theorem skel_trimming {w : ℕ} (hw : 1 ≤ w) {z : Tp k → ℕ → ℤ} {T D : ℕ} {Γ : Finset ℕ}
    (hdepth : ∀ π, IsDepPath (fun j => skel w (z (some (some j)))) T π → LinNet.GFree Γ π →
      π.length ≤ D + 1)
    {L : ℕ} (ot : ℕ → ℕ) (dm : Fin L → ℕ) (ϑ : ℕ) :
    (heavyCoords (coneRel w z T Γ ot dm) ϑ).card * ϑ ≤
        (w * ∑ h ∈ range (D + 1), (k + 1) ^ h) * L ∧
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood (coneRel w z T Γ ot dm)
        (heavyCoords (coneRel w z T Γ ot dm) ϑ)ᶜ)).degree v ≤
          max (w * ∑ h ∈ range (D + 1), (k + 1) ^ h) ϑ := by
  have h := paid_trimming (coneRel w z T Γ ot dm) ϑ (card_coneRel_le hw hdepth ot dm)
  rwa [Fintype.card_fin] at h

open Classical in
/-- **Corollary 3.8 of the fifth paper for relations inside balls** (Lemma 3.14(a)). -/
theorem ball_trimming {L : ℕ} (xs : Fin k → ℕ → ℤ) (T : ℕ) (rdStep : ℕ → Option (Fin L))
    (D' : ℕ) (tout : Fin L → ℕ) (N : Fin L → Finset (Fin L))
    (hN : ∀ q, N q ⊆ stepBall xs T rdStep D' (tout q)) (ϑ : ℕ) :
    (heavyCoords N ϑ).card * ϑ ≤ (∑ h ∈ range (D' + 1), (k + 1) ^ h) * L ∧
      ∀ v, (pairedIncidenceGraph (inducedNeighborhood N (heavyCoords N ϑ)ᶜ)).degree v ≤
        max (∑ h ∈ range (D' + 1), (k + 1) ^ h) ϑ := by
  have h := paid_trimming N ϑ (fun q => (card_le_card (hN q)).trans
    (card_stepBall_le xs T rdStep D' (tout q)))
  rwa [Fintype.card_fin] at h

end MergeDepth
