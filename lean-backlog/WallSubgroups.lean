import WallBundle

/-!
# The subgroup form of the bundle bound

One subgroup `Hs u` of a finite group per vertex `u` of a bipartite host. If the intersection
over the neighbours of each vertex lies in that vertex's subgroup, and intersecting with one
more vertex multiplies the index by at most `Q ^ newCells`, the hypothesis bounds the index of
the total intersection by `Q ^ v` (`GroupBoundAt`).

* The bundle hypothesis implies this form (`groupBoundAt_of_bundleBoundAt`): the logarithm of
  the index, in units of `log Q`, is an admissible function.
* The instance used by the proof is the symmetric group of a finite set with label stabilisers
  (`LabelBoundAt`). For a code `D`, take the permutations of `D` and the stabiliser of the
  restriction of the words to the cells of each vertex, with `Q = |α| ^ |D|`. The total
  intersection is trivial, so its index is `|D| !`, and `|D| ! ≤ |α| ^ (|D| v)` gives
  `|D| ≤ e · |α| ^ v` (`card_le_of_labelBoundAt`).
* One common deficit for this form implies the conjecture
  (`conjecture_of_groupCommonDeficit`).

Nothing here asserts any of these hypotheses.
-/

namespace LeanBacklog.WallSubgroups

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells
open LeanBacklog.WallBipartite LeanBacklog.WallBundle

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- The intersection of the subgroups attached to the vertices of `S` (the whole group for
`S = ∅`). -/
def meet {G : Type} [Group G] {n m : ℕ} (Hs : Fin m ⊕ Fin n → Subgroup G)
    (S : Finset (Fin m ⊕ Fin n)) : Subgroup G :=
  ⨅ u ∈ S, Hs u

/-- The subgroup form at one size. `G` is a finite group with one subgroup per vertex, `Q ≥ 2`
a natural number. If the intersection over the neighbours of each vertex lies in that vertex's
subgroup, and the index of `meet K ⊓ Hs u` in `meet K` is at most `Q ^ newCells K u`, then the
index of the total intersection is at most `Q ^ v`. -/
def GroupBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (G : Type) [Group G] [Fintype G] (Hs : Fin m ⊕ Fin n → Subgroup G) (Q : ℕ), 2 ≤ Q →
      (∀ u, meet Hs (nbrs H_col H_row u) ≤ Hs u) →
      (∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
        (Hs u).relIndex (meet Hs K) ≤ Q ^ newCells K u) →
      ((meet Hs univ).index : ℝ) ≤ (Q : ℝ) ^ v

/-- **The subgroup hypothesis.** One deficit `δ` for every degree bound and all large sizes. -/
def GroupCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, GroupBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-- Permutations of `X` that preserve the label `f`. -/
def labelStabilizer {X β : Type} (f : X → β) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, f (σ x) = f x}
  mul_mem' := by
    intro σ τ hσ hτ x
    have hσ' : ∀ x, f (σ x) = f x := hσ
    have hτ' : ∀ x, f (τ x) = f x := hτ
    rw [Equiv.Perm.mul_apply, hσ', hτ']
  one_mem' := by
    intro x
    rfl
  inv_mem' := by
    intro σ hσ x
    have hσ' : ∀ x, f (σ x) = f x := hσ
    have := hσ' (σ⁻¹ x)
    have hx : σ (σ⁻¹ x) = x := by simp
    rw [hx] at this
    exact this.symm

/-- The instance of the subgroup form that the proof uses: the symmetric group of a finite set,
each subgroup the stabiliser of a labelling. -/
def LabelBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (X : Type) [Fintype X] [DecidableEq X] (β : Type) (f : Fin m ⊕ Fin n → X → β) (Q : ℕ),
      2 ≤ Q →
      (∀ u, meet (fun u => labelStabilizer (f u)) (nbrs H_col H_row u) ≤
        labelStabilizer (f u)) →
      (∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
        (labelStabilizer (f u)).relIndex (meet (fun u => labelStabilizer (f u)) K) ≤
          Q ^ newCells K u) →
      ((meet (fun u => labelStabilizer (f u)) univ).index : ℝ) ≤ (Q : ℝ) ^ v

/-! ## Intersections -/

section Meet

variable {G : Type} [Group G] {n m : ℕ} (Hs : Fin m ⊕ Fin n → Subgroup G)

theorem mem_meet {S : Finset (Fin m ⊕ Fin n)} {g : G} : g ∈ meet Hs S ↔ ∀ u ∈ S, g ∈ Hs u := by
  simp [meet, Subgroup.mem_iInf]

theorem meet_empty : meet Hs ∅ = ⊤ := by
  ext g
  simp [mem_meet]

theorem meet_insert (u : Fin m ⊕ Fin n) (K : Finset (Fin m ⊕ Fin n)) :
    meet Hs (insert u K) = Hs u ⊓ meet Hs K := by
  ext g
  simp [mem_meet, Subgroup.mem_inf]

theorem meet_union (S T : Finset (Fin m ⊕ Fin n)) :
    meet Hs (S ∪ T) = meet Hs S ⊓ meet Hs T := by
  ext g
  simp only [mem_meet, Subgroup.mem_inf, mem_union]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Or.inl hu), fun u hu => h u (Or.inr hu)⟩
  · rintro ⟨h1, h2⟩ u (hu | hu)
    · exact h1 u hu
    · exact h2 u hu

theorem meet_anti {S T : Finset (Fin m ⊕ Fin n)} (h : S ⊆ T) : meet Hs T ≤ meet Hs S := by
  intro g hg
  rw [mem_meet] at hg ⊢
  exact fun u hu => hg u (h hu)

end Meet

/-! ## The guard: the bundle bound implies the subgroup bound -/

section Guard

variable {G : Type} [Group G] [Fintype G]

theorem index_pos' (H : Subgroup G) : 0 < H.index :=
  Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)

theorem log_index_nonneg (H : Subgroup G) : 0 ≤ Real.log (H.index : ℝ) :=
  Real.log_nonneg (by exact_mod_cast index_pos' H)

omit [Fintype G] in
/-- The index of an intersection, against a common overgroup. -/
theorem index_inf_mul_le {A B L : Subgroup G} (hA : A ≤ L) (hB : B ≤ L) :
    (A ⊓ B).index * L.index ≤ A.index * B.index := by
  have h1 := Subgroup.relIndex_mul_index (le_trans inf_le_left hA : A ⊓ B ≤ L)
  have h2 := Subgroup.relIndex_mul_index hA
  have h3 := Subgroup.relIndex_mul_index hB
  have h4 : (A ⊓ B).relIndex L ≤ A.relIndex L * B.relIndex L := Subgroup.relIndex_inf_le
  rw [← h1, ← h2, ← h3]
  calc (A ⊓ B).relIndex L * L.index * L.index
      ≤ (A.relIndex L * B.relIndex L) * L.index * L.index := by gcongr
    _ = A.relIndex L * L.index * (B.relIndex L * L.index) := by ring

/-- The logarithm of the index of the intersection, in units of `log Q`, is admissible. -/
theorem isBundleAdmissible_logIndex {n m : ℕ} (H_col : Fin m → Finset (Fin n))
    (H_row : Fin n → Finset (Fin m)) (Hs : Fin m ⊕ Fin n → Subgroup G) {Q : ℕ} (hQ : 2 ≤ Q)
    (hrec : ∀ u, meet Hs (nbrs H_col H_row u) ≤ Hs u)
    (hcap : ∀ (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n), u ∉ K →
      (Hs u).relIndex (meet Hs K) ≤ Q ^ newCells K u) :
    IsBundleAdmissible H_col H_row
      (fun S => Real.log ((meet Hs S).index : ℝ) / Real.log Q) := by
  have hlQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have ipos : ∀ S, (0 : ℝ) < ((meet Hs S).index : ℝ) := fun S => by
    exact_mod_cast index_pos' (meet Hs S)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show Real.log ((meet Hs ∅).index : ℝ) / Real.log Q = 0
    rw [meet_empty, Subgroup.index_top, Nat.cast_one, Real.log_one, zero_div]
  · intro S T hST
    show Real.log ((meet Hs S).index : ℝ) / Real.log Q ≤
      Real.log ((meet Hs T).index : ℝ) / Real.log Q
    apply div_le_div_of_nonneg_right _ hlQ.le
    apply Real.log_le_log (ipos S)
    exact_mod_cast Nat.le_of_dvd (index_pos' _) (Subgroup.index_dvd_of_le (meet_anti Hs hST))
  · intro S T
    show Real.log ((meet Hs (S ∪ T)).index : ℝ) / Real.log Q +
        Real.log ((meet Hs (S ∩ T)).index : ℝ) / Real.log Q ≤
      Real.log ((meet Hs S).index : ℝ) / Real.log Q +
        Real.log ((meet Hs T).index : ℝ) / Real.log Q
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hlQ.le
    rw [← Real.log_mul (ipos _).ne' (ipos _).ne', ← Real.log_mul (ipos _).ne' (ipos _).ne']
    apply Real.log_le_log (mul_pos (ipos _) (ipos _))
    rw [meet_union]
    exact_mod_cast index_inf_mul_le (meet_anti Hs inter_subset_left)
      (meet_anti Hs inter_subset_right)
  · intro K u hu
    show Real.log ((meet Hs (insert u K)).index : ℝ) / Real.log Q -
      Real.log ((meet Hs K).index : ℝ) / Real.log Q ≤ _
    rw [← sub_div, div_le_iff₀ hlQ]
    have hidx : (meet Hs (insert u K)).index = (Hs u).relIndex (meet Hs K) * (meet Hs K).index := by
      rw [meet_insert, ← Subgroup.inf_relIndex_right]
      exact (Subgroup.relIndex_mul_index inf_le_right).symm
    have hrel0 : 0 < (Hs u).relIndex (meet Hs K) := by
      have := index_pos' (meet Hs (insert u K))
      rw [hidx] at this
      exact Nat.pos_of_mul_pos_right this
    rw [hidx, Nat.cast_mul, Real.log_mul (by exact_mod_cast hrel0.ne') (ipos K).ne']
    have : Real.log ((Hs u).relIndex (meet Hs K) : ℝ) ≤ newCells K u * Real.log Q := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by exact_mod_cast hrel0)
      exact_mod_cast hcap K u hu
    linarith
  · intro u
    show Real.log ((meet Hs (insert u (nbrs H_col H_row u))).index : ℝ) / Real.log Q =
      Real.log ((meet Hs (nbrs H_col H_row u)).index : ℝ) / Real.log Q
    rw [meet_insert, inf_eq_right.mpr (hrec u)]

end Guard

/-- **The bundle bound implies the subgroup bound.** -/
theorem groupBoundAt_of_bundleBoundAt {n m w : ℕ} {v : ℝ} (h : BundleBoundAt n m w v) :
    GroupBoundAt n m w v := by
  intro H_col H_row hcol hrow hsym G _ _ Hs Q hQ hrec hcap
  have hb : Real.log ((meet Hs univ).index : ℝ) / Real.log Q ≤ v :=
    h H_col H_row hcol hrow hsym _ (isBundleAdmissible_logIndex H_col H_row Hs hQ hrec hcap)
  have hlQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  rw [div_le_iff₀ hlQ] at hb
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hi : (0 : ℝ) < ((meet Hs univ).index : ℝ) := by exact_mod_cast index_pos' _
  rw [Real.rpow_def_of_pos hQ0, ← Real.exp_log hi]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **The subgroup bound gives the label bound.** -/
theorem labelBoundAt_of_groupBoundAt {n m w : ℕ} {v : ℝ} (h : GroupBoundAt n m w v) :
    LabelBoundAt n m w v := by
  intro H_col H_row hcol hrow hsym X _ _ β f Q hQ hrec hcap
  exact h H_col H_row hcol hrow hsym (Equiv.Perm X) (fun u => labelStabilizer (f u)) Q hQ
    hrec hcap

/-! ## The bridge from codes, by counting -/

/-- A map on `K` that separates left cosets of `H` bounds the relative index. -/
theorem relIndex_le_card_of_sep {G : Type} [Group G] {H K : Subgroup G} {T : Type} [Fintype T]
    (φ : K → T) (hφ : ∀ a b : K, φ a = φ b → ((a : G)⁻¹ * b) ∈ H) :
    H.relIndex K ≤ Fintype.card T := by
  rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]
  apply Nat.card_le_card_of_injective (fun c => φ c.out)
  intro c d hcd
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf]
  simpa using hφ _ _ hcd

/-- `N ! ≤ t ^ N` gives `N ≤ e t`. -/
theorem le_exp_mul_of_factorial_le {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (h : (N.factorial : ℝ) ≤ t ^ N) : (N : ℝ) ≤ Real.exp 1 * t := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero]
    positivity
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have h1 := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  rw [div_le_iff₀ hf, ← Real.exp_one_pow] at h1
  have h2 : (N : ℝ) ^ N ≤ (Real.exp 1 * t) ^ N := by
    rw [mul_pow]
    calc (N : ℝ) ^ N ≤ Real.exp 1 ^ N * N.factorial := h1
      _ ≤ Real.exp 1 ^ N * t ^ N := by gcongr
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg N) (by positivity) hN.ne').mp h2

section Bridge

variable {n m : ℕ} {α : Type}

/-- The restriction of a word of the code to the cells of a vertex. -/
def bundleLabel (D : Finset (Fin n × Fin m → α)) (u : Fin m ⊕ Fin n) (x : D) :
    Fin n × Fin m → Option α :=
  MotionDepthCodes.view (cellsOf {u}) (x : Fin n × Fin m → α)

theorem mem_cellsOf_singleton_inl {a : Fin m} {p : Fin n × Fin m} :
    p ∈ cellsOf ({Sum.inl a} : Finset (Fin m ⊕ Fin n)) ↔ p.2 = a := by
  simp [mem_cellsOf]

theorem mem_cellsOf_singleton_inr {b : Fin n} {p : Fin n × Fin m} :
    p ∈ cellsOf ({Sum.inr b} : Finset (Fin m ⊕ Fin n)) ↔ p.1 = b := by
  simp [mem_cellsOf]

/-- Two words of a code that agree on the cells of all neighbours of `u` agree on the cells
of `u`. -/
theorem agree_cellsOf_of_nbrs {H_col : Fin m → Finset (Fin n)} {H_row : Fin n → Finset (Fin m)}
    {D : Finset (Fin n × Fin m → α)} (hD : IsBipartiteTwoSidedCode H_col H_row D)
    {x y : Fin n × Fin m → α} (hx : x ∈ D) (hy : y ∈ D) (u : Fin m ⊕ Fin n)
    (h : ∀ u' ∈ nbrs H_col H_row u, ∀ p ∈ cellsOf ({u'} : Finset (Fin m ⊕ Fin n)), x p = y p) :
    ∀ p ∈ cellsOf ({u} : Finset (Fin m ⊕ Fin n)), x p = y p := by
  cases u with
  | inl a =>
    intro p hp
    rw [mem_cellsOf_singleton_inl] at hp
    have := hD.1 x hx y hy a (fun b hb a' => h (Sum.inr b)
      (by simp [nbrs, hb]) (b, a') (by rw [mem_cellsOf_singleton_inr])) p.1
    have hp' : p = (p.1, a) := Prod.ext rfl hp
    rw [hp']
    exact this
  | inr b =>
    intro p hp
    rw [mem_cellsOf_singleton_inr] at hp
    have := hD.2 x hx y hy b (fun a ha b' => h (Sum.inl a)
      (by simp [nbrs, ha]) (b', a) (by rw [mem_cellsOf_singleton_inl])) p.2
    have hp' : p = (b, p.2) := Prod.ext hp rfl
    rw [hp']
    exact this

theorem mem_labelStabilizer_bundleLabel {D : Finset (Fin n × Fin m → α)} {u : Fin m ⊕ Fin n}
    {σ : Equiv.Perm D} :
    σ ∈ labelStabilizer (bundleLabel D u) ↔
      ∀ x : D, ∀ p ∈ cellsOf ({u} : Finset (Fin m ⊕ Fin n)),
        (σ x : Fin n × Fin m → α) p = (x : Fin n × Fin m → α) p := by
  show (∀ x, bundleLabel D u (σ x) = bundleLabel D u x) ↔ _
  simp only [bundleLabel, MotionDepthCodes.view_eq_iff]

/-- A permutation fixing every vertex label fixes every word. -/
theorem meet_univ_eq_bot (D : Finset (Fin n × Fin m → α)) :
    meet (fun u => labelStabilizer (bundleLabel D u)) univ = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_meet] at hσ
  rw [Subgroup.mem_bot]
  ext x : 1
  apply Subtype.ext
  funext p
  have := (mem_labelStabilizer_bundleLabel.mp (hσ (Sum.inr p.1) (mem_univ _))) x p
    (by rw [mem_cellsOf_singleton_inr])
  simpa using this

/-- Recovery for label stabilisers of a code. -/
theorem meet_nbrs_le (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    {D : Finset (Fin n × Fin m → α)} (hD : IsBipartiteTwoSidedCode H_col H_row D)
    (u : Fin m ⊕ Fin n) :
    meet (fun u => labelStabilizer (bundleLabel D u)) (nbrs H_col H_row u) ≤
      labelStabilizer (bundleLabel D u) := by
  intro σ hσ
  rw [mem_meet] at hσ
  rw [mem_labelStabilizer_bundleLabel]
  intro x
  exact agree_cellsOf_of_nbrs hD (σ x).2 x.2 u
    (fun u' hu' => mem_labelStabilizer_bundleLabel.mp (hσ u' hu') x)

/-- The cap for label stabilisers of a code: at most `|α| ^ (|D| c)` cosets, where `c` is the
number of new cells. -/
theorem relIndex_bundleLabel_le [Fintype α] [Nonempty α] (D : Finset (Fin n × Fin m → α))
    (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n) :
    (labelStabilizer (bundleLabel D u)).relIndex
        (meet (fun u => labelStabilizer (bundleLabel D u)) K) ≤
      (Fintype.card α ^ D.card) ^ newCells K u := by
  classical
  set E : Finset (Fin n × Fin m) := cellsOf {u} \ cellsOf K with hE
  set M := meet (fun u => labelStabilizer (bundleLabel D u)) K with hM
  have hfix : ∀ σ ∈ M, ∀ x : D, ∀ p ∈ cellsOf K,
      (σ x : Fin n × Fin m → α) p = (x : Fin n × Fin m → α) p := by
    intro σ hσ x p hp
    obtain ⟨k, hk, hpk⟩ : ∃ k ∈ K, p ∈ cellsOf ({k} : Finset (Fin m ⊕ Fin n)) := by
      rw [mem_cellsOf] at hp
      rcases hp with hp | hp
      · exact ⟨_, hp, by rw [mem_cellsOf_singleton_inr]⟩
      · exact ⟨_, hp, by rw [mem_cellsOf_singleton_inl]⟩
    rw [hM, mem_meet] at hσ
    exact mem_labelStabilizer_bundleLabel.mp (hσ k hk) x p hpk
  let φ : M → (D → (E → α)) := fun σ x p =>
    (((σ : Equiv.Perm D)⁻¹ x : D) : Fin n × Fin m → α) p.1
  have hsep : ∀ a b : M, φ a = φ b →
      ((a : Equiv.Perm D)⁻¹ * b) ∈ labelStabilizer (bundleLabel D u) := by
    intro a b hab
    rw [mem_labelStabilizer_bundleLabel]
    intro y p hp
    rw [Equiv.Perm.mul_apply]
    set x : D := (b : Equiv.Perm D) y with hx
    have hy : y = (b : Equiv.Perm D)⁻¹ x := by rw [hx]; simp
    rw [hy]
    by_cases hpK : p ∈ cellsOf K
    · rw [hfix _ (M.inv_mem a.2) x p hpK, hfix _ (M.inv_mem b.2) x p hpK]
    · have hpE : p ∈ E := by rw [hE, mem_sdiff]; exact ⟨hp, hpK⟩
      exact congrFun (congrFun hab x) ⟨p, hpE⟩
  have h1 := relIndex_le_card_of_sep φ hsep
  have hcardT : Fintype.card (D → (E → α)) = (Fintype.card α ^ E.card) ^ D.card := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_coe, Fintype.card_coe]
  have hEc : E.card ≤ newCells K u := card_sdiff_cellsOf_le K u
  refine h1.trans (le_of_eq_of_le hcardT ?_)
  rw [← pow_mul, ← pow_mul]
  have hq : 0 < Fintype.card α := Fintype.card_pos
  exact Nat.pow_le_pow_right hq (by rw [mul_comm]; exact Nat.mul_le_mul_left _ hEc)

/-- **The label bound bounds every code**, up to the factor `e`. -/
theorem card_le_of_labelBoundAt {n m w : ℕ} {v : ℝ} [Fintype α] [Nonempty α]
    (h : LabelBoundAt n m w v)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ Real.exp 1 * (Fintype.card α : ℝ) ^ v := by
  classical
  have hα0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rcases D.eq_empty_or_nonempty with hDe | hne
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
  have hN : 1 ≤ D.card := hne.card_pos
  have hQ : 2 ≤ Fintype.card α ^ D.card :=
    le_trans hq (Nat.le_self_pow (by omega) _)
  have hb := h H_col H_row hcol hrow hsym D (Fin n × Fin m → Option α) (bundleLabel D)
    (Fintype.card α ^ D.card) hQ (meet_nbrs_le H_col H_row hD)
    (fun K u _ => relIndex_bundleLabel_le D K u)
  rw [meet_univ_eq_bot, Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_coe] at hb
  have hpow : ((Fintype.card α ^ D.card : ℕ) : ℝ) ^ v =
      ((Fintype.card α : ℝ) ^ v) ^ D.card := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (Fintype.card α : ℝ) D.card,
      ← Real.rpow_mul hα0.le, mul_comm, Real.rpow_mul hα0.le, Real.rpow_natCast]
  rw [hpow] at hb
  exact le_exp_mul_of_factorial_le (Real.rpow_nonneg hα0.le v) hb

/-- The subgroup bound bounds every code, up to the factor `e`. -/
theorem card_le_of_groupBoundAt {n m w : ℕ} {v : ℝ} [Fintype α] [Nonempty α]
    (h : GroupBoundAt n m w v)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b)
    (D : Finset (Fin n × Fin m → α)) (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    (D.card : ℝ) ≤ Real.exp 1 * (Fintype.card α : ℝ) ^ v :=
  card_le_of_labelBoundAt (labelBoundAt_of_groupBoundAt h) H_col H_row hcol hrow hsym D hD

end Bridge

/-! ## The implications -/

/-- The factor `e` is absorbed by a slack `η` once `η d ^ 2 ≥ 2`. -/
theorem exp_one_mul_rpow_le {A s t : ℝ} (hA : 2 ≤ A) (hs : 2 ≤ s) :
    Real.exp 1 * A ^ t ≤ A ^ (t + s) := by
  have hA0 : 0 < A := by linarith
  rw [Real.rpow_add hA0, mul_comm (A ^ t)]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hA0.le t)
  have h1 : A ^ (2 : ℝ) ≤ A ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  rw [Real.rpow_two] at h1
  have h2 := Real.exp_one_lt_d9
  nlinarith

theorem two_card_bits (d : ℕ) : (2 : ℝ) ≤ (Fintype.card (Fin (entryBits d) → Bool) : ℝ) := by
  have hb : 1 ≤ entryBits d := by unfold entryBits; omega
  have : 2 ≤ Fintype.card (Fin (entryBits d) → Bool) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ entryBits d := Nat.pow_le_pow_right (by norm_num) hb
  exact_mod_cast this

/-- For `d > 2 / η`, `η d ^ 2 ≥ 2`. -/
theorem two_le_mul_sq {η : ℝ} (hη : 0 < η) {d : ℕ} (hd : ⌈2 / η⌉₊ + 1 ≤ d) :
    2 ≤ η * (d : ℝ) ^ 2 := by
  have h1 : (2 / η : ℝ) ≤ ⌈2 / η⌉₊ := Nat.le_ceil _
  have h2 : ((⌈2 / η⌉₊ : ℕ) : ℝ) + 1 ≤ d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by linarith [(Nat.cast_nonneg ⌈2 / η⌉₊ : (0 : ℝ) ≤ _)]
  have h3 : 2 ≤ η * d := by
    rw [div_le_iff₀ hη] at h1
    nlinarith
  nlinarith

/-- **The subgroup hypothesis implies the bipartite common deficit.** -/
theorem bipartiteCommonDeficit_of_group (h : GroupCommonDeficit) : BipartiteCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w η hη => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨max n₀ (⌈2 / η⌉₊ + 1), fun d hd => ?_⟩
  intro H_col H_row D hcol hrow hsym hD
  have h1 := card_le_of_groupBoundAt (hn₀ d ((le_max_left _ _).trans hd)) H_col H_row hcol hrow
    hsym D hD
  have h2 := exp_one_mul_rpow_le (t := (1 - δ) * (d : ℝ) ^ 2) (two_card_bits d)
    (two_le_mul_sq hη ((le_max_right _ _).trans hd))
  have h3 : (1 - δ) * (d : ℝ) ^ 2 + η * (d : ℝ) ^ 2 = (1 - δ + η) * (d : ℝ) ^ 2 := by ring
  rw [h3] at h2
  exact h1.trans h2

theorem commonDeficit_of_group (h : GroupCommonDeficit) : LeanBacklog.Wall.CommonDeficit :=
  bipartiteCommonDeficit_iff_commonDeficit.mp (bipartiteCommonDeficit_of_group h)

/-- **The subgroup hypothesis implies the conjecture.** -/
theorem conjecture_of_groupCommonDeficit (h : GroupCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCommonDeficit (bipartiteCommonDeficit_of_group h)

/-! ## The window-wise form -/

/-- One window per resource triple, cofinally many dimensions, in subgroup form. -/
def WindowwiseGroupCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R : ℕ) (θ δ : ℝ), 0 < θ ∧ budgetRate k G c θ R < δ ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀,
        GroupBoundAt d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2)

theorem windowwiseBipartite_of_windowwiseGroup (h : WindowwiseGroupCriterion) :
    WindowwiseBipartiteCriterion := by
  intro k G c hk hG hc
  obtain ⟨R, θ, δ, hθ, hT, hcof⟩ := h k G c hk hG hc
  set δ' := (budgetRate k G c θ R + δ) / 2 with hδ'
  have hη : 0 < δ - δ' := by rw [hδ']; linarith
  refine ⟨R, θ, δ', hθ, by rw [hδ']; linarith, fun d₀ => ?_⟩
  obtain ⟨d, hd, hb⟩ := hcof (max d₀ (⌈2 / (δ - δ')⌉₊ + 1))
  refine ⟨d, (le_max_left _ _).trans hd, ?_⟩
  intro H_col H_row D hcol hrow hsym hD
  have h1 := card_le_of_groupBoundAt hb H_col H_row hcol hrow hsym D hD
  have h2 := exp_one_mul_rpow_le (t := (1 - δ) * (d : ℝ) ^ 2) (two_card_bits d)
    (two_le_mul_sq hη ((le_max_right _ _).trans hd))
  have h3 : (1 - δ) * (d : ℝ) ^ 2 + (δ - δ') * (d : ℝ) ^ 2 = (1 - δ') * (d : ℝ) ^ 2 := by ring
  rw [h3] at h2
  exact h1.trans h2

theorem conjecture_of_windowwiseGroupCriterion (h : WindowwiseGroupCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_windowwiseBipartiteCriterion (windowwiseBipartite_of_windowwiseGroup h)

#print axioms isBundleAdmissible_logIndex
#print axioms groupBoundAt_of_bundleBoundAt
#print axioms labelBoundAt_of_groupBoundAt
#print axioms relIndex_le_card_of_sep
#print axioms le_exp_mul_of_factorial_le
#print axioms meet_univ_eq_bot
#print axioms meet_nbrs_le
#print axioms relIndex_bundleLabel_le
#print axioms card_le_of_labelBoundAt
#print axioms card_le_of_groupBoundAt
#print axioms bipartiteCommonDeficit_of_group
#print axioms commonDeficit_of_group
#print axioms conjecture_of_groupCommonDeficit
#print axioms windowwiseBipartite_of_windowwiseGroup
#print axioms conjecture_of_windowwiseGroupCriterion

end LeanBacklog.WallSubgroups
