import WallCounting
import WallPermutation

/-!
# The branching form of the bundle bound

A *labelling system* on a bipartite host is a finite set `𝒳` of labellings of the vertices.
It satisfies *recovery* if, within `𝒳`, the label at a vertex is determined by the labels at its
neighbours (`MotionDepthCodes.IsStorageCode`), and it has *branching* `q` if, among the members
of `𝒳` that agree with a given member on a vertex set `K`, at most `q ^ newCells K v` different
labels occur at a vertex `v ∉ K` (`HasBranching`). The branching form (`BranchingBoundAt`)
bounds the size of every such system by `q ^ v`.

* For a code `D` over an alphabet of `q ≥ 2` symbols, the labellings `u ↦` (the restriction of a
  word to the cells of `u`) form a labelling system of the same size with recovery and branching
  `q`. Hence the branching form implies the bipartite bound at the same size and exponent,
  with no constant lost (`bipartiteBoundAt_of_branchingBoundAt`).
* One common deficit for the branching form implies the conjecture
  (`conjecture_of_branchingCommonDeficit`); so do the exact-budget forms
  (`conjecture_of_branchingCriterion`, `conjecture_of_windowwiseBranchingCriterion`) and the
  permutation-host form (`conjecture_of_permutationBranchingCommonDeficit`).
* The restricted counting form implies the branching form up to the factor `e`
  (`card_le_of_separatedCounting`), hence for common deficits
  (`branchingCommonDeficit_of_separatedCounting`).

Nothing here asserts any of these hypotheses.
-/

namespace LeanBacklog.WallBranching

open Finset Transpose Transpose.Tape Transpose.Tape.Impl
open LeanBacklog.RowSpread LeanBacklog.BlockTCC LeanBacklog.WallFarCells
open LeanBacklog.WallBipartite LeanBacklog.WallPermutation LeanBacklog.WallBundle
open LeanBacklog.WallSubgroups LeanBacklog.WallCounting

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Definitions -/

/-- The members of `𝒳` that agree with `x` at every vertex of `K`. -/
def agreeing {β : Type} [DecidableEq β] {n m : ℕ} (𝒳 : Finset (Fin m ⊕ Fin n → β))
    (K : Finset (Fin m ⊕ Fin n)) (x : Fin m ⊕ Fin n → β) : Finset (Fin m ⊕ Fin n → β) :=
  𝒳.filter fun y => ∀ u ∈ K, y u = x u

/-- Branching: among the members of `𝒳` agreeing with a member `x` on `K`, at most
`q ^ newCells K v` different labels occur at a vertex `v ∉ K`. -/
def HasBranching {β : Type} [DecidableEq β] {n m : ℕ} (q : ℕ)
    (𝒳 : Finset (Fin m ⊕ Fin n → β)) : Prop :=
  ∀ (K : Finset (Fin m ⊕ Fin n)) (v : Fin m ⊕ Fin n), v ∉ K → ∀ x ∈ 𝒳,
    ((agreeing 𝒳 K x).image fun y => y v).card ≤ q ^ newCells K v

/-- The branching form at one size. -/
def BranchingBoundAt (n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (β : Type) [DecidableEq β] (𝒳 : Finset (Fin m ⊕ Fin n → β)) (q : ℕ), 2 ≤ q →
      MotionDepthCodes.IsStorageCode (nbrs H_col H_row) 𝒳 →
      HasBranching q 𝒳 →
      (𝒳.card : ℝ) ≤ (q : ℝ) ^ v

/-- **The branching hypothesis.** One deficit `δ` for every degree bound and all large sizes. -/
def BranchingCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, BranchingBoundAt n n w ((1 - δ) * (n : ℝ) ^ 2)

/-- The same on hosts given by `w` permutations. -/
def PermutationBranchingBoundAt (N w : ℕ) (v : ℝ) : Prop :=
  ∀ (σ : Fin w → Equiv.Perm (Fin N)) (β : Type) [DecidableEq β]
    (𝒳 : Finset (Fin N ⊕ Fin N → β)) (q : ℕ), 2 ≤ q →
      MotionDepthCodes.IsStorageCode (nbrs (permCol σ) (permRow σ)) 𝒳 →
      HasBranching q 𝒳 →
      (𝒳.card : ℝ) ≤ (q : ℝ) ^ v

/-- The permutation-host branching hypothesis. -/
def PermutationBranchingCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    PermutationBranchingBoundAt n w ((1 - δ) * (n : ℝ) ^ 2)

/-! ## The bridge from codes -/

section Bridge

variable {n m : ℕ} {α : Type}

/-- The labelling of a word: at each vertex, the restriction of the word to the cells of that
vertex. -/
def restrictLabel (x : Fin n × Fin m → α) : Fin m ⊕ Fin n → Fin n × Fin m → Option α :=
  fun u => MotionDepthCodes.view (cellsOf {u}) x

/-- Every cell lies in the bundle of its row, so the labelling determines the word. -/
theorem restrictLabel_injective :
    Function.Injective (restrictLabel : (Fin n × Fin m → α) → _) := by
  intro x y h
  funext p
  have := congrFun (congrFun h (Sum.inr p.1)) p
  simpa [restrictLabel, MotionDepthCodes.view, mem_cellsOf_singleton_inr] using this

/-- Labellings agreeing on `K` come from words agreeing on the cells of `K`. -/
theorem eq_on_cellsOf_of_restrictLabel {K : Finset (Fin m ⊕ Fin n)} {x y : Fin n × Fin m → α}
    (h : ∀ u ∈ K, restrictLabel y u = restrictLabel x u) :
    ∀ p ∈ cellsOf K, y p = x p := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ : ∃ k ∈ K, p ∈ cellsOf ({k} : Finset (Fin m ⊕ Fin n)) := by
    rw [mem_cellsOf] at hp
    rcases hp with hp | hp
    · exact ⟨_, hp, by rw [mem_cellsOf_singleton_inr]⟩
    · exact ⟨_, hp, by rw [mem_cellsOf_singleton_inl]⟩
  exact (MotionDepthCodes.view_eq_iff _ _ _).mp (h k hk) p hpk

variable [DecidableEq α]

/-- Recovery: the labelling system of a code is a storage code on the host. -/
theorem isStorageCode_image_restrictLabel {H_col : Fin m → Finset (Fin n)}
    {H_row : Fin n → Finset (Fin m)} {D : Finset (Fin n × Fin m → α)}
    (hD : IsBipartiteTwoSidedCode H_col H_row D) :
    MotionDepthCodes.IsStorageCode (nbrs H_col H_row) (D.image restrictLabel) := by
  intro X hX Y hY v hagree
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hX
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hY
  show MotionDepthCodes.view (cellsOf {v}) x = MotionDepthCodes.view (cellsOf {v}) y
  rw [MotionDepthCodes.view_eq_iff]
  exact agree_cellsOf_of_nbrs hD hx hy v
    (fun u' hu' => (MotionDepthCodes.view_eq_iff _ _ _).mp (hagree u' hu'))

/-- Branching: the labelling system of a code over `q` symbols has branching `q`. -/
theorem hasBranching_image_restrictLabel [Fintype α] [Nonempty α] (D : Finset (Fin n × Fin m → α)) :
    HasBranching (Fintype.card α) (D.image restrictLabel) := by
  intro K v _ X hX
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hX
  set E : Finset (Fin n × Fin m) := cellsOf {v} \ cellsOf K with hE
  let g : (E → α) → Fin n × Fin m → Option α := fun h p =>
    if hp : p ∈ cellsOf ({v} : Finset (Fin m ⊕ Fin n)) then
      some (if hK : p ∈ cellsOf K then x p else h ⟨p, by rw [hE, mem_sdiff]; exact ⟨hp, hK⟩⟩)
    else none
  have hsub : ((agreeing (D.image restrictLabel) K (restrictLabel x)).image fun Y => Y v) ⊆
      univ.image g := by
    intro Z hZ
    obtain ⟨Y, hY, rfl⟩ := mem_image.mp hZ
    rw [agreeing, mem_filter] at hY
    obtain ⟨hY, hYK⟩ := hY
    obtain ⟨y, _, rfl⟩ := mem_image.mp hY
    have hyx := eq_on_cellsOf_of_restrictLabel hYK
    refine mem_image.mpr ⟨fun p => y p.1, mem_univ _, ?_⟩
    funext p
    simp only [g, restrictLabel, MotionDepthCodes.view]
    by_cases hp : p ∈ cellsOf ({v} : Finset (Fin m ⊕ Fin n))
    · by_cases hK : p ∈ cellsOf K
      · simp only [hp, hK, hyx p hK, ↓reduceDIte, ↓reduceIte]
      · simp only [hp, hK, ↓reduceDIte, ↓reduceIte]
    · simp only [hp, ↓reduceDIte, ↓reduceIte]
  have hq : 0 < Fintype.card α := Fintype.card_pos
  calc _ ≤ (univ.image g).card := card_le_card hsub
    _ ≤ (univ : Finset (E → α)).card := card_image_le
    _ = Fintype.card α ^ E.card := by rw [card_univ, Fintype.card_fun, Fintype.card_coe]
    _ ≤ Fintype.card α ^ newCells K v := Nat.pow_le_pow_right hq (card_sdiff_cellsOf_le K v)

end Bridge

/-- **The branching bound implies the bipartite bound**, at the same size and exponent, over
every nonempty finite alphabet. -/
theorem bipartiteBoundAt_of_branchingBoundAt {n m w : ℕ} {v : ℝ} {α : Type} [Fintype α]
    [Nonempty α] (h : BranchingBoundAt n m w v) : BipartiteBoundAt α n m w v := by
  classical
  intro H_col H_row D hcol hrow hsym hD
  rcases Nat.lt_or_ge (Fintype.card α) 2 with hq | hq
  · have hq' : Fintype.card α = 1 := by
      have := Fintype.card_pos (α := α)
      omega
    have hsub : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hq'.le
    have hle : D.card ≤ 1 :=
      card_le_one.mpr (fun x _ y _ => funext fun p => Subsingleton.elim _ _)
    rw [hq', Nat.cast_one, Real.one_rpow]
    exact_mod_cast hle
  · have hb := h H_col H_row hcol hrow hsym (Fin n × Fin m → Option α) (D.image restrictLabel)
      (Fintype.card α) hq (isStorageCode_image_restrictLabel hD) (hasBranching_image_restrictLabel D)
    rwa [card_image_of_injective _ restrictLabel_injective] at hb

/-! ## The implications -/

/-- **The branching hypothesis implies the bipartite common deficit.** -/
theorem bipartiteCommonDeficit_of_branching (h : BranchingCommonDeficit) :
    BipartiteCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w η hη => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨n₀, fun d hd => ?_⟩
  refine (bipartiteBoundAt_of_branchingBoundAt (hn₀ d hd)).mono_v ?_
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  nlinarith

theorem commonDeficit_of_branching (h : BranchingCommonDeficit) :
    LeanBacklog.Wall.CommonDeficit :=
  bipartiteCommonDeficit_iff_commonDeficit.mp (bipartiteCommonDeficit_of_branching h)

/-- **The branching hypothesis implies the conjecture.** -/
theorem conjecture_of_branchingCommonDeficit (h : BranchingCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCommonDeficit (bipartiteCommonDeficit_of_branching h)

/-! ## Permutation hosts -/

/-- A storage code stays a storage code when the helper sets grow. -/
theorem isStorageCode_mono {V β : Type} {N N' : V → Finset V} (hN : ∀ v, N v ⊆ N' v)
    {C : Finset (V → β)} (h : MotionDepthCodes.IsStorageCode N C) :
    MotionDepthCodes.IsStorageCode N' C :=
  fun x hx y hy v hv => h x hx y hy v (fun u hu => hv u (hN v hu))

/-- **The branching bound and its permutation form are the same statement.** -/
theorem branchingBoundAt_iff_permutation {N w : ℕ} {v : ℝ} :
    BranchingBoundAt N N w v ↔ PermutationBranchingBoundAt N w v := by
  constructor
  · intro h σ β _ 𝒳 q hq hrec hbr
    exact h (permCol σ) (permRow σ) (card_permCol_le σ) (card_permRow_le σ)
      (mem_permCol_iff_mem_permRow σ) β 𝒳 q hq hrec hbr
  · intro h H_col H_row hcol hrow hsym β _ 𝒳 q hq hrec hbr
    obtain ⟨σ, hc, hr⟩ := exists_perm_cover H_col H_row hcol hrow hsym
    exact h σ β 𝒳 q hq (isStorageCode_mono (nbrs_mono hc hr) hrec) hbr

theorem permutationBranchingCommonDeficit_iff :
    PermutationBranchingCommonDeficit ↔ BranchingCommonDeficit := by
  unfold PermutationBranchingCommonDeficit BranchingCommonDeficit
  simp only [branchingBoundAt_iff_permutation]

/-- **The permutation-host branching hypothesis implies the conjecture.** -/
theorem conjecture_of_permutationBranchingCommonDeficit (h : PermutationBranchingCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_branchingCommonDeficit (permutationBranchingCommonDeficit_iff.mp h)

/-! ## The exact-budget forms -/

/-- The conjecture's quantifiers with the branching bound on `d × d`. -/
def BranchingCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c → ∀ d₀ : ℕ,
    ∃ (d R : ℕ) (θ δ : ℝ), max d₀ 1 ≤ d ∧ 0 < θ ∧
      BranchingBoundAt d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2) ∧
      (2*(adaptiveAllowance k G c*d+cutBudget k G c d θ):ℕ) +
        (entryBits d*crossBudget d (endWindow k G θ) R:ℕ) <
          δ*(d*d*entryBits d:ℕ)

/-- One window per resource triple, cofinally many dimensions, in branching form. -/
def WindowwiseBranchingCriterion : Prop :=
  ∀ k G c : ℕ, 5 ≤ k → 1 ≤ G → 4 ≤ c →
    ∃ (R : ℕ) (θ δ : ℝ), 0 < θ ∧ budgetRate k G c θ R < δ ∧
      ∀ d₀ : ℕ, ∃ d ≥ d₀,
        BranchingBoundAt d d (endWindow k G θ+R+1) ((1-δ)*(d:ℝ)^2)

theorem bipartiteCriterion_of_branchingCriterion (h : BranchingCriterion) :
    BipartiteCriterion := by
  intro k G c hk hG hc d₀
  obtain ⟨d, R, θ, δ, hd, hθ, hb, hgap⟩ := h k G c hk hG hc d₀
  exact ⟨d, R, θ, δ, hd, hθ, bipartiteBoundAt_of_branchingBoundAt hb, hgap⟩

theorem windowwiseBipartite_of_windowwiseBranching (h : WindowwiseBranchingCriterion) :
    WindowwiseBipartiteCriterion := by
  intro k G c hk hG hc
  obtain ⟨R, θ, δ, hθ, hT, hcof⟩ := h k G c hk hG hc
  refine ⟨R, θ, δ, hθ, hT, fun d₀ => ?_⟩
  obtain ⟨d, hd, hb⟩ := hcof d₀
  exact ⟨d, hd, bipartiteBoundAt_of_branchingBoundAt hb⟩

/-- **The branching criterion implies the conjecture.** -/
theorem conjecture_of_branchingCriterion (h : BranchingCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCriterion (bipartiteCriterion_of_branchingCriterion h)

/-- **The window-wise branching criterion implies the conjecture.** -/
theorem conjecture_of_windowwiseBranchingCriterion (h : WindowwiseBranchingCriterion) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_windowwiseBipartiteCriterion (windowwiseBipartite_of_windowwiseBranching h)

/-! ## The guard: the restricted counting form implies the branching form -/

/-- The cap for a labelling system with branching `q`: intersecting with one more vertex
multiplies the index of the label stabilisers by at most `(q ^ |𝒳|) ^ newCells`. -/
theorem relIndex_le_of_hasBranching {n m : ℕ} {β : Type} [DecidableEq β]
    {𝒳 : Finset (Fin m ⊕ Fin n → β)} {q : ℕ} (hbr : HasBranching q 𝒳)
    (K : Finset (Fin m ⊕ Fin n)) (u : Fin m ⊕ Fin n) (hu : u ∉ K) :
    (labelStabilizer (fun x : 𝒳 => (x : Fin m ⊕ Fin n → β) u)).relIndex
        (meet (fun u => labelStabilizer (fun x : 𝒳 => (x : Fin m ⊕ Fin n → β) u)) K) ≤
      (q ^ 𝒳.card) ^ newCells K u := by
  classical
  set f : Fin m ⊕ Fin n → 𝒳 → β := fun u x => (x : Fin m ⊕ Fin n → β) u with hf
  set M := meet (fun u => labelStabilizer (f u)) K with hM
  let L : 𝒳 → Finset β := fun x => (agreeing 𝒳 K x).image fun y => y u
  have hmem : ∀ σ : M, ∀ x : 𝒳, f u ((σ : Equiv.Perm 𝒳)⁻¹ x) ∈ L x := by
    intro σ x
    have hσ := (mem_meet_labelStabilizer_iff f).mp (M.inv_mem σ.2)
    refine mem_image.mpr ⟨(((σ : Equiv.Perm 𝒳)⁻¹ x : 𝒳) : Fin m ⊕ Fin n → β), ?_, rfl⟩
    rw [agreeing, mem_filter]
    exact ⟨((σ : Equiv.Perm 𝒳)⁻¹ x).2, fun k hk => hσ k hk x⟩
  let φ : M → ((x : 𝒳) → ↥(L x)) := fun σ x => ⟨f u ((σ : Equiv.Perm 𝒳)⁻¹ x), hmem σ x⟩
  have hsep : ∀ a b : M, φ a = φ b → ((a : Equiv.Perm 𝒳)⁻¹ * b) ∈ labelStabilizer (f u) := by
    intro a b hab
    rw [mem_labelStabilizer_iff]
    intro y
    rw [Equiv.Perm.mul_apply]
    set x : 𝒳 := (b : Equiv.Perm 𝒳) y with hx
    have hy : y = (b : Equiv.Perm 𝒳)⁻¹ x := by rw [hx]; simp
    rw [hy]
    exact congrArg Subtype.val (congrFun hab x)
  have h1 := relIndex_le_card_of_sep φ hsep
  rw [Fintype.card_pi] at h1
  refine h1.trans ?_
  calc ∏ x : 𝒳, Fintype.card ↥(L x) = ∏ x : 𝒳, (L x).card := by
        simp only [Fintype.card_coe]
    _ ≤ ∏ _x : 𝒳, q ^ newCells K u := Finset.prod_le_prod (fun x _ => hbr K u hu x x.2)
    _ = (q ^ 𝒳.card) ^ newCells K u := by
        rw [prod_const, card_univ, Fintype.card_coe, ← pow_mul, ← pow_mul, mul_comm]

/-- **The restricted counting bound bounds every labelling system with branching**, up to the
factor `e`. -/
theorem card_le_of_separatedCounting {n m w : ℕ} {v : ℝ} (h : SeparatedCountingBoundAt n m w v)
    (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m))
    (hcol : ∀ a, (H_col a).card ≤ w) (hrow : ∀ b, (H_row b).card ≤ w)
    (hsym : ∀ a b, b ∈ H_col a ↔ a ∈ H_row b)
    (β : Type) [DecidableEq β] (𝒳 : Finset (Fin m ⊕ Fin n → β)) (q : ℕ) (hq : 2 ≤ q)
    (hrec : MotionDepthCodes.IsStorageCode (nbrs H_col H_row) 𝒳) (hbr : HasBranching q 𝒳) :
    (𝒳.card : ℝ) ≤ Real.exp 1 * (q : ℝ) ^ v := by
  classical
  have hb := h H_col H_row hcol hrow hsym 𝒳 β (fun u x => (x : Fin m ⊕ Fin n → β) u) q hq
    (fun x y hxy => Subtype.ext (funext hxy))
    (fun u x y hxy => hrec x x.2 y y.2 u hxy)
    (fun K u hu => by
      rw [← relIndex_mul_classFactorial _ K u, Fintype.card_coe]
      exact Nat.mul_le_mul_right _ (relIndex_le_of_hasBranching hbr K u hu))
  rw [Fintype.card_coe] at hb
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [mul_comm, Real.rpow_mul hq0, Real.rpow_natCast] at hb
  exact le_exp_mul_of_factorial_le (Real.rpow_nonneg hq0 v) hb

/-- **The restricted counting hypothesis implies the branching hypothesis** (the deficit is
halved to absorb the factor `e`). -/
theorem branchingCommonDeficit_of_separatedCounting (h : SeparatedCountingCommonDeficit) :
    BranchingCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ / 2, by positivity, fun w => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨max n₀ (⌈2 / (δ / 2)⌉₊ + 1), fun n hn => ?_⟩
  intro H_col H_row hcol hrow hsym β _ 𝒳 q hq hrec hbr
  have h1 := card_le_of_separatedCounting (hn₀ n ((le_max_left _ _).trans hn)) H_col H_row
    hcol hrow hsym β 𝒳 q hq hrec hbr
  have h2 := exp_one_mul_rpow_le (A := (q : ℝ)) (t := (1 - δ) * (n : ℝ) ^ 2)
    (by exact_mod_cast hq) (two_le_mul_sq (by positivity : (0 : ℝ) < δ / 2)
      ((le_max_right _ _).trans hn))
  have h3 : (1 - δ) * (n : ℝ) ^ 2 + δ / 2 * (n : ℝ) ^ 2 = (1 - δ / 2) * (n : ℝ) ^ 2 := by ring
  rw [h3] at h2
  exact h1.trans h2

#print axioms restrictLabel_injective
#print axioms isStorageCode_image_restrictLabel
#print axioms hasBranching_image_restrictLabel
#print axioms bipartiteBoundAt_of_branchingBoundAt
#print axioms bipartiteCommonDeficit_of_branching
#print axioms commonDeficit_of_branching
#print axioms conjecture_of_branchingCommonDeficit
#print axioms isStorageCode_mono
#print axioms branchingBoundAt_iff_permutation
#print axioms permutationBranchingCommonDeficit_iff
#print axioms conjecture_of_permutationBranchingCommonDeficit
#print axioms bipartiteCriterion_of_branchingCriterion
#print axioms windowwiseBipartite_of_windowwiseBranching
#print axioms conjecture_of_branchingCriterion
#print axioms conjecture_of_windowwiseBranchingCriterion
#print axioms relIndex_le_of_hasBranching
#print axioms card_le_of_separatedCounting
#print axioms branchingCommonDeficit_of_separatedCounting

/-! ## The fixed-alphabet form -/

/-- The branching form at one size and one alphabet size `q`. -/
def BranchingBoundAtAlphabet (q n m w : ℕ) (v : ℝ) : Prop :=
  ∀ (H_col : Fin m → Finset (Fin n)) (H_row : Fin n → Finset (Fin m)),
    (∀ a, (H_col a).card ≤ w) → (∀ b, (H_row b).card ≤ w) →
    (∀ a b, b ∈ H_col a ↔ a ∈ H_row b) →
    ∀ (β : Type) [DecidableEq β] (𝒳 : Finset (Fin m ⊕ Fin n → β)),
      MotionDepthCodes.IsStorageCode (nbrs H_col H_row) 𝒳 →
      HasBranching q 𝒳 →
      (𝒳.card : ℝ) ≤ (q : ℝ) ^ v

/-- The branching hypothesis at the canonical alphabet of the transposition problem only. -/
def CanonicalBranchingCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    BranchingBoundAtAlphabet (2 ^ entryBits n) n n w ((1 - δ) * (n : ℝ) ^ 2)

theorem branchingBoundAt_iff_forall_alphabet {n m w : ℕ} {v : ℝ} :
    BranchingBoundAt n m w v ↔ ∀ q, 2 ≤ q → BranchingBoundAtAlphabet q n m w v := by
  constructor
  · intro h q hq H_col H_row hcol hrow hsym β _ 𝒳 hrec hbr
    exact h H_col H_row hcol hrow hsym β 𝒳 q hq hrec hbr
  · intro h H_col H_row hcol hrow hsym β _ 𝒳 q hq hrec hbr
    exact h q hq H_col H_row hcol hrow hsym β 𝒳 hrec hbr

/-- **The bridge at one alphabet size**: exact, with `q = |α|`. -/
theorem bipartiteBoundAt_of_branchingBoundAtAlphabet {n m w : ℕ} {v : ℝ} {α : Type}
    [Fintype α] [Nonempty α] (h : BranchingBoundAtAlphabet (Fintype.card α) n m w v) :
    BipartiteBoundAt α n m w v := by
  classical
  intro H_col H_row D hcol hrow hsym hD
  have hb := h H_col H_row hcol hrow hsym (Fin n × Fin m → Option α) (D.image restrictLabel)
    (isStorageCode_image_restrictLabel hD) (hasBranching_image_restrictLabel D)
  rwa [card_image_of_injective _ restrictLabel_injective] at hb

theorem two_le_two_pow_entryBits (d : ℕ) : 2 ≤ 2 ^ entryBits d := by
  have hb : 1 ≤ entryBits d := by unfold entryBits; omega
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ entryBits d := Nat.pow_le_pow_right (by norm_num) hb

theorem card_canonical_alphabet (d : ℕ) :
    Fintype.card (Fin (entryBits d) → Bool) = 2 ^ entryBits d := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem canonicalBranchingCommonDeficit_of_branching (h : BranchingCommonDeficit) :
    CanonicalBranchingCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  exact ⟨n₀, fun n hn => branchingBoundAt_iff_forall_alphabet.mp (hn₀ n hn) _
    (two_le_two_pow_entryBits n)⟩

/-- **The canonical-alphabet branching hypothesis implies the bipartite common deficit.** -/
theorem bipartiteCommonDeficit_of_canonicalBranching (h : CanonicalBranchingCommonDeficit) :
    BipartiteCommonDeficit := by
  obtain ⟨δ, hδ, hb⟩ := h
  refine ⟨δ, hδ, fun w η hη => ?_⟩
  obtain ⟨n₀, hn₀⟩ := hb w
  refine ⟨n₀, fun d hd => ?_⟩
  have hb' : BranchingBoundAtAlphabet (Fintype.card (Fin (entryBits d) → Bool)) d d w
      ((1 - δ) * (d : ℝ) ^ 2) := by
    rw [card_canonical_alphabet]
    exact hn₀ d hd
  refine (bipartiteBoundAt_of_branchingBoundAtAlphabet hb').mono_v ?_
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  nlinarith

/-- **The canonical-alphabet branching hypothesis implies the conjecture.** -/
theorem conjecture_of_canonicalBranchingCommonDeficit (h : CanonicalBranchingCommonDeficit) :
    LeanBacklog.Wall.Conjecture :=
  conjecture_of_bipartiteCommonDeficit (bipartiteCommonDeficit_of_canonicalBranching h)

/-- The fixed-alphabet branching form on hosts given by `w` permutations. -/
def PermutationBranchingBoundAtAlphabet (q N w : ℕ) (v : ℝ) : Prop :=
  ∀ (σ : Fin w → Equiv.Perm (Fin N)) (β : Type) [DecidableEq β]
    (𝒳 : Finset (Fin N ⊕ Fin N → β)),
      MotionDepthCodes.IsStorageCode (nbrs (permCol σ) (permRow σ)) 𝒳 →
      HasBranching q 𝒳 →
      (𝒳.card : ℝ) ≤ (q : ℝ) ^ v

/-- The canonical-alphabet branching hypothesis on permutation hosts. -/
def CanonicalPermutationBranchingCommonDeficit : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    PermutationBranchingBoundAtAlphabet (2 ^ entryBits n) n w ((1 - δ) * (n : ℝ) ^ 2)

theorem branchingBoundAtAlphabet_iff_permutation {q N w : ℕ} {v : ℝ} :
    BranchingBoundAtAlphabet q N N w v ↔ PermutationBranchingBoundAtAlphabet q N w v := by
  constructor
  · intro h σ β _ 𝒳 hrec hbr
    exact h (permCol σ) (permRow σ) (card_permCol_le σ) (card_permRow_le σ)
      (mem_permCol_iff_mem_permRow σ) β 𝒳 hrec hbr
  · intro h H_col H_row hcol hrow hsym β _ 𝒳 hrec hbr
    obtain ⟨σ, hc, hr⟩ := exists_perm_cover H_col H_row hcol hrow hsym
    exact h σ β 𝒳 (isStorageCode_mono (nbrs_mono hc hr) hrec) hbr

theorem canonicalPermutationBranchingCommonDeficit_iff :
    CanonicalPermutationBranchingCommonDeficit ↔ CanonicalBranchingCommonDeficit := by
  unfold CanonicalPermutationBranchingCommonDeficit CanonicalBranchingCommonDeficit
  simp only [branchingBoundAtAlphabet_iff_permutation]

theorem conjecture_of_canonicalPermutationBranchingCommonDeficit
    (h : CanonicalPermutationBranchingCommonDeficit) : LeanBacklog.Wall.Conjecture :=
  conjecture_of_canonicalBranchingCommonDeficit
    (canonicalPermutationBranchingCommonDeficit_iff.mp h)

/-! ## Only opposite-side sets matter -/

/-- Branching stated only for sets `K` on the side opposite to `v`. -/
def HasOppositeBranching {β : Type} [DecidableEq β] {n m : ℕ} (q : ℕ)
    (𝒳 : Finset (Fin m ⊕ Fin n → β)) : Prop :=
  ∀ (K : Finset (Fin m ⊕ Fin n)) (v : Fin m ⊕ Fin n), (∀ u ∈ K, u.isLeft ≠ v.isLeft) → ∀ x ∈ 𝒳,
    ((agreeing 𝒳 K x).image fun y => y v).card ≤ q ^ newCells K v

/-- `newCells` only counts the side opposite to `v`. -/
theorem newCells_filter_opposite {n m : ℕ} (K : Finset (Fin m ⊕ Fin n)) (v : Fin m ⊕ Fin n) :
    newCells (K.filter fun u => u.isLeft ≠ v.isLeft) v = newCells K v := by
  cases v with
  | inl a =>
    simp only [newCells, Finset.filter_filter]
    congr 2
    apply Finset.filter_congr
    intro u _
    cases u <;> simp
  | inr b =>
    simp only [newCells, Finset.filter_filter]
    congr 2
    apply Finset.filter_congr
    intro u _
    cases u <;> simp

/-- **Branching is equivalent to branching on opposite-side sets.** -/
theorem hasBranching_iff_hasOppositeBranching {β : Type} [DecidableEq β] {n m : ℕ} {q : ℕ}
    {𝒳 : Finset (Fin m ⊕ Fin n → β)} : HasBranching q 𝒳 ↔ HasOppositeBranching q 𝒳 := by
  constructor
  · intro h K v hK x hx
    exact h K v (fun hv => hK v hv rfl) x hx
  · intro h K v _ x hx
    set K' := K.filter fun u => u.isLeft ≠ v.isLeft with hK'
    have hopp : ∀ u ∈ K', u.isLeft ≠ v.isLeft := fun u hu => (mem_filter.mp hu).2
    have hsub : agreeing 𝒳 K x ⊆ agreeing 𝒳 K' x := by
      intro y hy
      rw [agreeing, mem_filter] at hy ⊢
      exact ⟨hy.1, fun u hu => hy.2 u (mem_filter.mp hu).1⟩
    calc ((agreeing 𝒳 K x).image fun y => y v).card
        ≤ ((agreeing 𝒳 K' x).image fun y => y v).card := card_le_card (image_subset_image hsub)
      _ ≤ q ^ newCells K' v := h K' v hopp x hx
      _ = q ^ newCells K v := by rw [hK', newCells_filter_opposite]

#print axioms branchingBoundAt_iff_forall_alphabet
#print axioms bipartiteBoundAt_of_branchingBoundAtAlphabet
#print axioms canonicalBranchingCommonDeficit_of_branching
#print axioms bipartiteCommonDeficit_of_canonicalBranching
#print axioms conjecture_of_canonicalBranchingCommonDeficit
#print axioms branchingBoundAtAlphabet_iff_permutation
#print axioms canonicalPermutationBranchingCommonDeficit_iff
#print axioms conjecture_of_canonicalPermutationBranchingCommonDeficit
#print axioms newCells_filter_opposite
#print axioms hasBranching_iff_hasOppositeBranching

end LeanBacklog.WallBranching
