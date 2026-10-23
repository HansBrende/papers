import MotionDepthCodes.StorageCode

/-!
# Theorem S: linear storage codes on triangle-free subcubic graphs

Let `G` be a triangle-free graph and `M` a matrix over a field `F` with unit
diagonal whose off-diagonal entries vanish on non-edges of `G`. The recovery set
of `v` is `S_v = {u ≠ v : M v u ≠ 0}`. Suppose every vertex satisfies

  (★★) `|S_v| ≤ 2`, or `|S_v| = 3` and `r ∈ S_v` whenever `v ∈ S_r`.

Then `dim ker M ≤ ⌊N/2⌋`. Every such matrix on a triangle-free graph of maximum
degree at most 3 satisfies (★★), so on these graphs no linear storage code over
any field has rate above one half.

The proof is the minimal-counterexample argument of the paper, run as a strong
induction over vertex subsets `W`. Codes on `W` are subspaces of `V → F`
(`subCode`), so deleting vertices is an inclusion of subspaces. The peeling
process is replaced by a maximal "good chain": a chain that cannot be extended
leaves every chain vertex with no recovery neighbours outside the chain, and its
rows then determine every codeword from fewer than half of the coordinates.
-/

namespace MotionDepthCodes

open Finset Module
open scoped BigOperators
set_option autoImplicit false

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F]

/-! ## Codes on vertex subsets -/

/-- Vectors vanishing on `U`. -/
def zeroOn (U : Finset V) : Submodule F (V → F) where
  carrier := {x | ∀ u ∈ U, x u = 0}
  add_mem' := by
    intro x y hx hy u hu
    simp [hx u hu, hy u hu]
  zero_mem' := by
    intro u _
    rfl
  smul_mem' := by
    intro c x hx u hu
    simp [hx u hu]

omit [Fintype V] [DecidableEq V] in
theorem mem_zeroOn {U : Finset V} {x : V → F} : x ∈ (zeroOn U : Submodule F (V → F)) ↔
    ∀ u ∈ U, x u = 0 := Iff.rfl

/-- The code of `M` on `W`: vectors supported on `W` that satisfy the rows of `W`. -/
def subCode (M : Matrix V V F) (W : Finset V) : Submodule F (V → F) where
  carrier := {x | (∀ u, u ∉ W → x u = 0) ∧ ∀ v ∈ W, ∑ u, M v u * x u = 0}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun u hu => by simp [hx1 u hu, hy1 u hu], fun v hv => ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hx2 v hv, hy2 v hv, add_zero]
  zero_mem' := ⟨fun _ _ => rfl, fun v _ => by simp⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2⟩
    refine ⟨fun u hu => by simp [hx1 u hu], fun v hv => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    calc ∑ u, M v u * (c * x u) = c * ∑ u, M v u * x u := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
      _ = 0 := by rw [hx2 v hv, mul_zero]

omit [DecidableEq V] in
theorem mem_subCode {M : Matrix V V F} {W : Finset V} {x : V → F} :
    x ∈ subCode M W ↔ (∀ u, u ∉ W → x u = 0) ∧ ∀ v ∈ W, ∑ u, M v u * x u = 0 := Iff.rfl

omit [DecidableEq V] in
theorem subCode_empty (M : Matrix V V F) : subCode M ∅ = ⊥ := by
  ext x
  simp only [mem_subCode, Finset.notMem_empty, not_false_eq_true, forall_const,
    false_implies, implies_true, and_true, Submodule.mem_bot]
  constructor
  · intro h
    funext u
    exact h u
  · rintro rfl u
    rfl

omit [DecidableEq V] in
theorem subCode_univ (M : Matrix V V F) : subCode M univ = LinearMap.ker M.mulVecLin := by
  ext x
  simp only [mem_subCode, Finset.mem_univ, not_true_eq_false, false_implies, implies_true,
    true_implies, true_and, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro h
    funext v
    simpa [Matrix.mulVec, dotProduct] using h v
  · intro h v
    simpa [Matrix.mulVec, dotProduct] using congrFun h v

omit [DecidableEq V] in
theorem card_sub_le_finrank_zeroOn (U : Finset V) :
    Fintype.card V - U.card ≤ finrank F (zeroOn U : Submodule F (V → F)) := by
  let ρ : (V → F) →ₗ[F] (U → F) :=
    { toFun := fun x u => x u
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker ρ = zeroOn U := by
    ext x
    simp only [LinearMap.mem_ker, mem_zeroOn]
    constructor
    · intro h u hu
      exact congrFun h ⟨u, hu⟩
    · intro h
      funext u
      exact h u u.2
  have h1 := LinearMap.finrank_range_add_finrank_ker ρ
  have h2 : finrank F (LinearMap.range ρ) ≤ U.card := by
    calc finrank F (LinearMap.range ρ) ≤ finrank F (U → F) := Submodule.finrank_le _
      _ = U.card := by simp
  rw [hker, Module.finrank_fintype_fun_eq_card] at h1
  omega

omit [DecidableEq V] in
/-- Imposing `|U|` coordinate conditions lowers the dimension by at most `|U|`. -/
theorem finrank_le_card_add_finrank_inf_zeroOn (P : Submodule F (V → F)) (U : Finset V) :
    finrank F P ≤ U.card + finrank F (P ⊓ zeroOn U : Submodule F (V → F)) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P (zeroOn U)
  have h2 : finrank F (P ⊔ zeroOn U : Submodule F (V → F)) ≤ Fintype.card V := by
    calc _ ≤ finrank F (V → F) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card F
  have h3 := card_sub_le_finrank_zeroOn (F := F) U
  have h4 : U.card ≤ Fintype.card V := Finset.card_le_univ U
  omega

/-- Deletion (F1): codewords vanishing on `U` are codewords of `W \ U`. -/
theorem subCode_inf_zeroOn_le (M : Matrix V V F) (W U : Finset V) :
    subCode M W ⊓ zeroOn U ≤ subCode M (W \ U) := by
  rintro x ⟨⟨hx1, hx2⟩, hx3⟩
  refine ⟨fun u hu => ?_, fun v hv => hx2 v (Finset.mem_sdiff.mp hv).1⟩
  by_cases huW : u ∈ W
  · have huU : u ∈ U := by
      by_contra h
      exact hu (Finset.mem_sdiff.mpr ⟨huW, h⟩)
    exact hx3 u huU
  · exact hx1 u huW

omit [DecidableEq V] in
/-- A row of `W`, restricted to any set containing its live terms. -/
theorem row_sum_eq_zero {M : Matrix V V F} {W : Finset V} {x : V → F} (hx : x ∈ subCode M W)
    {v : V} (hv : v ∈ W) (T : Finset V) (hT : ∀ u, M v u ≠ 0 → x u ≠ 0 → u ∈ T) :
    ∑ u ∈ T, M v u * x u = 0 := by
  have hsub : ∑ u ∈ T, M v u * x u = ∑ u, M v u * x u := by
    apply Finset.sum_subset (Finset.subset_univ T)
    intro u _ huT
    by_contra hne
    exact huT (hT u (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
  rw [hsub]
  exact hx.2 v hv

/-! ## Recovery sets and the hypotheses -/

section Main

variable [DecidableEq F]

/-- The recovery set of `v`: the vertices `u ≠ v` with `M v u ≠ 0`. -/
def recSet (M : Matrix V V F) (v : V) : Finset V :=
  univ.filter fun u => u ≠ v ∧ M v u ≠ 0

theorem mem_recSet {M : Matrix V V F} {v u : V} : u ∈ recSet M v ↔ u ≠ v ∧ M v u ≠ 0 := by
  simp [recSet]

/-- The reciprocity condition (★★) at `v`: at most two recovery neighbours, or
exactly three that include every vertex recovering from `v`. -/
def Star (M : Matrix V V F) (v : V) : Prop :=
  (recSet M v).card ≤ 2 ∨ ((recSet M v).card = 3 ∧ ∀ r, v ∈ recSet M r → r ∈ recSet M v)

/-- No recovery triangle: two vertices that recover a common vertex do not recover
each other. This holds whenever the code lives on a triangle-free graph. -/
def RecTriangleFree (M : Matrix V V F) : Prop :=
  ∀ r p q, p ∈ recSet M r → q ∈ recSet M r → q ∉ recSet M p

/-- The standing hypotheses of Theorem S: unit diagonal and no recovery triangle.
The reciprocity condition (★★) is imposed separately, only on the vertices where
the argument runs. -/
structure ThmSHyp (M : Matrix V V F) : Prop where
  diag : ∀ v, M v v = 1
  triangleFree : RecTriangleFree M

/-! ## Chains -/

/-- The vertex set of a chain started at `v₀`. Chains list their steps
`(parent, p, q)` newest first. -/
def chainX (v₀ : V) : List (V × V × V) → Finset V
  | [] => {v₀}
  | (_, p, q) :: c => insert p (insert q (chainX v₀ c))

/-- The free coordinates of a chain: `v₀` and the first vertex of each pair. -/
def chainD (v₀ : V) : List (V × V × V) → Finset V
  | [] => {v₀}
  | (_, p, _) :: c => insert p (chainD v₀ c)

/-- A good chain: each new pair is exactly the part of its parent's recovery set
outside the chain so far. -/
def GoodChain (M : Matrix V V F) (W : Finset V) (v₀ : V) : List (V × V × V) → Prop
  | [] => True
  | (r, p, q) :: c => GoodChain M W v₀ c ∧ r ∈ chainX v₀ c ∧ p ≠ q ∧
      recSet M r ∩ (W \ chainX v₀ c) = {p, q}

section Chain

variable {M : Matrix V V F} {W : Finset V} {v₀ : V}

theorem GoodChain.mem_pair {r p q : V} {c : List (V × V × V)} (h : GoodChain M W v₀ ((r, p, q) :: c)) :
    p ∈ recSet M r ∩ (W \ chainX v₀ c) ∧ q ∈ recSet M r ∩ (W \ chainX v₀ c) := by
  have hpq : recSet M r ∩ (W \ chainX v₀ c) = {p, q} := h.2.2.2
  rw [hpq]
  simp

theorem chainX_subset (hv₀ : v₀ ∈ W) : ∀ c, GoodChain M W v₀ c → chainX v₀ c ⊆ W
  | [], _ => by simpa [chainX] using hv₀
  | (r, p, q) :: c, h => by
    obtain ⟨hp, hq⟩ := GoodChain.mem_pair h
    have ih := chainX_subset hv₀ c h.1
    intro u hu
    simp only [chainX, Finset.mem_insert] at hu
    rcases hu with hu | hu | hu
    · rw [hu]
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1
    · rw [hu]
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).2).1
    · exact ih hu

theorem chainX_card : ∀ c, GoodChain M W v₀ c → (chainX v₀ c).card = 2 * c.length + 1
  | [], _ => by simp [chainX]
  | (r, p, q) :: c, h => by
    obtain ⟨hp, hq⟩ := GoodChain.mem_pair h
    have hpq : p ≠ q := h.2.2.1
    have ih := chainX_card c h.1
    have hq' : q ∉ chainX v₀ c := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).2).2
    have hp' : p ∉ insert q (chainX v₀ c) := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hpq, (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).2⟩
    simp only [chainX, Finset.card_insert_of_notMem hp', Finset.card_insert_of_notMem hq', ih,
      List.length_cons]
    ring

omit [DecidableEq F] [Fintype V] in
theorem chainD_card_le : ∀ c : List (V × V × V), (chainD v₀ c).card ≤ c.length + 1
  | [] => by simp [chainD]
  | (r, p, q) :: c => by
    simp only [chainD, List.length_cons]
    have := chainD_card_le c
    exact (Finset.card_insert_le _ _).trans (by omega)

theorem chain_parent : ∀ c, GoodChain M W v₀ c → ∀ u ∈ chainX v₀ c, u ≠ v₀ →
    ∃ r ∈ chainX v₀ c, u ∈ recSet M r
  | [], _, u, hu, hne => by
    simp only [chainX, Finset.mem_singleton] at hu
    exact absurd hu hne
  | (r, p, q) :: c, h, u, hu, hne => by
    obtain ⟨hp, hq⟩ := GoodChain.mem_pair h
    have hr : r ∈ chainX v₀ c := h.2.1
    have hrX : r ∈ chainX v₀ ((r, p, q) :: c) := by
      simp only [chainX, Finset.mem_insert]
      exact Or.inr (Or.inr hr)
    simp only [chainX, Finset.mem_insert] at hu
    rcases hu with hu | hu | hu
    · exact ⟨r, hrX, hu ▸ (Finset.mem_inter.mp hp).1⟩
    · exact ⟨r, hrX, hu ▸ (Finset.mem_inter.mp hq).1⟩
    · obtain ⟨r', hr', hu'⟩ := chain_parent c h.1 u hu hne
      refine ⟨r', ?_, hu'⟩
      simp only [chainX, Finset.mem_insert]
      exact Or.inr (Or.inr hr')

/-- Codewords vanishing on the free coordinates vanish on the whole chain. -/
theorem chain_det (hv₀ : v₀ ∈ W) : ∀ c, GoodChain M W v₀ c → ∀ x ∈ subCode M W,
    (∀ u ∈ chainD v₀ c, x u = 0) → ∀ u ∈ chainX v₀ c, x u = 0
  | [], _, x, _, hD, u, hu => hD u (by simpa [chainD, chainX] using hu)
  | (r, p, q) :: c, h, x, hx, hD, u, hu => by
    obtain ⟨hp, hq⟩ := GoodChain.mem_pair h
    have hr : r ∈ chainX v₀ c := h.2.1
    have hset : recSet M r ∩ (W \ chainX v₀ c) = {p, q} := h.2.2.2
    have hpq : p ≠ q := h.2.2.1
    have hDc : ∀ w ∈ chainD v₀ c, x w = 0 := fun w hw => hD w (by
      simp only [chainD, Finset.mem_insert]
      exact Or.inr hw)
    have hXc := chain_det hv₀ c h.1 x hx hDc
    have hxp : x p = 0 := hD p (by simp [chainD])
    have hrW : r ∈ W := chainX_subset hv₀ c h.1 hr
    have hrow := row_sum_eq_zero hx hrW {q} (by
      intro w hMw hxw
      have hwW : w ∈ W := by
        by_contra hw
        exact hxw (hx.1 w hw)
      have hwX : w ∉ chainX v₀ c := fun hw => hxw (hXc w hw)
      have hwr : w ≠ r := fun e => hwX (e ▸ hr)
      have hwrec : w ∈ recSet M r ∩ (W \ chainX v₀ c) :=
        Finset.mem_inter.mpr ⟨mem_recSet.mpr ⟨hwr, hMw⟩, Finset.mem_sdiff.mpr ⟨hwW, hwX⟩⟩
      rw [hset] at hwrec
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwrec ⊢
      rcases hwrec with hw | hw
      · exact absurd (by rw [hw]; exact hxp) hxw
      · exact hw)
    rw [Finset.sum_singleton] at hrow
    have hMq : M r q ≠ 0 := (mem_recSet.mp (Finset.mem_inter.mp hq).1).2
    have hxq : x q = 0 := (mul_eq_zero.mp hrow).resolve_left hMq
    simp only [chainX, Finset.mem_insert] at hu
    rcases hu with hu | hu | hu
    · rw [hu]
      exact hxp
    · rw [hu]
      exact hxq
    · exact hXc u hu

end Chain

/-! ## The minimal counterexample -/

section Counterexample

variable {M : Matrix V V F} {W : Finset V}

omit [DecidableEq F] in
/-- The start: a counterexample has odd order, dimension `⌊N/2⌋ + 1`, and every
singleton deletion is tight. -/
theorem start_facts (ih : ∀ t ⊂ W, finrank F (subCode M t) ≤ t.card / 2)
    (hlt : W.card / 2 < finrank F (subCode M W)) :
    Odd W.card ∧ finrank F (subCode M W) = W.card / 2 + 1 ∧
      ∀ v ∈ W, subCode M (W \ {v}) = subCode M W ⊓ zeroOn {v} ∧
        finrank F (subCode M (W \ {v})) = W.card / 2 := by
  have hne : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [subCode_empty] at hlt
    simp at hlt
  obtain ⟨v₁, hv₁⟩ := hne
  have hpos : 0 < W.card := Finset.card_pos.mpr ⟨v₁, hv₁⟩
  have key : ∀ v ∈ W, finrank F (subCode M W) ≤ 1 + finrank F (subCode M (W \ {v})) := by
    intro v _
    have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W) {v}
    have h2 := Submodule.finrank_mono (subCode_inf_zeroOn_le M W {v})
    simp only [Finset.card_singleton] at h1
    omega
  have ihv : ∀ v ∈ W, finrank F (subCode M (W \ {v})) ≤ (W.card - 1) / 2 := by
    intro v hv
    have hsub : W \ {v} ⊂ W := Finset.sdiff_ssubset (by simpa using hv) (by simp)
    have h := ih _ hsub
    rwa [Finset.card_sdiff_of_subset (by simpa using hv), Finset.card_singleton] at h
  have hodd : Odd W.card := by
    have h1 := key v₁ hv₁
    have h2 := ihv v₁ hv₁
    rcases Nat.even_or_odd W.card with ⟨k, hk⟩ | ho
    · omega
    · exact ho
  obtain ⟨k, hk⟩ := hodd
  have hd : finrank F (subCode M W) = W.card / 2 + 1 := by
    have h1 := key v₁ hv₁
    have h2 := ihv v₁ hv₁
    omega
  refine ⟨⟨k, hk⟩, hd, fun v hv => ?_⟩
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W) {v}
  simp only [Finset.card_singleton] at h1
  have h2 := ihv v hv
  have heq : subCode M W ⊓ zeroOn {v} = subCode M (W \ {v}) := by
    apply Submodule.eq_of_le_of_finrank_le (subCode_inf_zeroOn_le M W {v})
    omega
  refine ⟨heq.symm, ?_⟩
  rw [← heq]
  have h3 := Submodule.finrank_mono (subCode_inf_zeroOn_le M W {v})
  omega

omit [DecidableEq F] in
/-- (2a) No coordinate vanishes on a tight code. -/
theorem no_forced_zero (ih : ∀ t ⊂ W, finrank F (subCode M t) ≤ t.card / 2)
    {X : Finset V} (hXW : X ⊆ W) (hpar : Even (W.card - X.card))
    (hdim : finrank F (subCode M (W \ X)) = (W.card - X.card) / 2) {s : V} (hs : s ∈ W \ X)
    (hzero : ∀ y ∈ subCode M (W \ X), y s = 0) : False := by
  have hle : subCode M (W \ X) ≤ subCode M ((W \ X) \ {s}) := by
    intro y hy
    apply subCode_inf_zeroOn_le M (W \ X) {s}
    exact ⟨hy, fun u hu => by rw [Finset.mem_singleton.mp hu]; exact hzero y hy⟩
  have hsub : (W \ X) \ {s} ⊂ W := by
    rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset.trans Finset.sdiff_subset)]
    exact ⟨s, (Finset.mem_sdiff.mp hs).1, by simp⟩
  have h1 := ih _ hsub
  have h2 := Submodule.finrank_mono hle
  have hcard : ((W \ X) \ {s}).card = W.card - X.card - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hs),
      Finset.card_sdiff_of_subset hXW, Finset.card_singleton]
  have hpos : 1 ≤ W.card - X.card := by
    have : (W \ X).Nonempty := ⟨s, hs⟩
    have h := Finset.card_pos.mpr this
    rwa [Finset.card_sdiff_of_subset hXW] at h
  obtain ⟨k, hk⟩ := hpar
  omega

omit [DecidableEq F] in
/-- (2c) The pair step. -/
theorem pair_step (ih : ∀ t ⊂ W, finrank F (subCode M t) ≤ t.card / 2)
    {X : Finset V} (hXW : X ⊆ W) (hpar : Even (W.card - X.card))
    (hdim : finrank F (subCode M (W \ X)) = (W.card - X.card) / 2) {p q : V}
    (hp : p ∈ W \ X) (hq : q ∈ W \ X) (hpq : p ≠ q)
    (hiff : ∀ y ∈ subCode M (W \ X), y p = 0 ↔ y q = 0) :
    subCode M (W \ insert p (insert q X)) = subCode M (W \ X) ⊓ zeroOn {p} ∧
      finrank F (subCode M (W \ insert p (insert q X))) = (W.card - X.card) / 2 - 1 := by
  have hset : W \ insert p (insert q X) = (W \ X) \ {p, q} := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hle : subCode M (W \ X) ⊓ zeroOn {p} ≤ subCode M (W \ insert p (insert q X)) := by
    rintro y ⟨hy, hyp⟩
    have hyp' : y p = 0 := hyp p (Finset.mem_singleton_self p)
    rw [hset]
    apply subCode_inf_zeroOn_le M (W \ X) {p, q}
    refine ⟨hy, fun u hu => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hyp'
    · exact (hiff y hy).mp hyp'
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M (W \ X)) {p}
  simp only [Finset.card_singleton] at h1
  have hsub : W \ insert p (insert q X) ⊂ W := by
    rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
    exact ⟨p, (Finset.mem_sdiff.mp hp).1, by simp⟩
  have h2 := ih _ hsub
  have hcard : (W \ insert p (insert q X)).card = W.card - X.card - 2 := by
    rw [hset, Finset.card_sdiff_of_subset, Finset.card_sdiff_of_subset hXW, Finset.card_pair hpq]
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hp
    · exact hq
  have hpos : 2 ≤ W.card - X.card := by
    have h := Finset.card_le_card (show ({p, q} : Finset V) ⊆ W \ X by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hp
      · exact hq)
    rwa [Finset.card_pair hpq, Finset.card_sdiff_of_subset hXW] at h
  obtain ⟨k, hk⟩ := hpar
  have heq : subCode M (W \ X) ⊓ zeroOn {p} = subCode M (W \ insert p (insert q X)) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    omega
  refine ⟨heq.symm, ?_⟩
  rw [← heq]
  have h3 := Submodule.finrank_mono hle
  omega

end Counterexample

/-! ## The theorem -/

section Theorem

variable {M : Matrix V V F}

/-- Some vertex of an odd set has at most two recovery neighbours in it: otherwise
the recovery relation on `W` would be a symmetric 3-regular graph of odd order. -/
theorem exists_small_rec {W : Finset V} (hstar : ∀ v ∈ W, Star M v) (hodd : Odd W.card) :
    ∃ v₀ ∈ W, (recSet M v₀ ∩ W).card ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have h3 : ∀ v ∈ W, (recSet M v ∩ W).card = 3 ∧ ∀ r, v ∈ recSet M r → r ∈ recSet M v := by
    intro v hv
    have hlt := hcon v hv
    have hsub := Finset.card_le_card (Finset.inter_subset_left : recSet M v ∩ W ⊆ recSet M v)
    rcases hstar v hv with h2 | ⟨h3, hrec⟩
    · omega
    · exact ⟨by omega, hrec⟩
  let H : SimpleGraph W :=
    { Adj := fun a b => (b : V) ∈ recSet M a
      symm := ⟨fun a b hab => (h3 b b.2).2 a hab⟩
      loopless := ⟨fun a ha => (mem_recSet.mp ha).1 rfl⟩ }
  have hdeg : ∀ a : W, H.degree a = 3 := by
    intro a
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter (G := H)]
    have hmap : (Finset.univ.filter (H.Adj a)).map (Function.Embedding.subtype (· ∈ W)) =
        recSet M a ∩ W := by
      ext u
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype, Finset.mem_inter, H]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨hb, b.2⟩
      · rintro ⟨hu, huW⟩
        exact ⟨⟨u, huW⟩, hu, rfl⟩
    rw [← Finset.card_map, hmap, (h3 a a.2).1]
  have heven := H.even_card_odd_degree_vertices
  have hall : (Finset.univ.filter fun a : W => Odd (H.degree a)) = Finset.univ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hdeg a]
    decide
  rw [hall, Finset.card_univ, Fintype.card_coe] at heven
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- A counterexample yields a contradiction: run a maximal good chain. -/
theorem chain_contradiction (hyp : ThmSHyp M) {W : Finset V} (hstar : ∀ v ∈ W, Star M v)
    (ih : ∀ t ⊂ W, finrank F (subCode M t) ≤ t.card / 2)
    (hlt : W.card / 2 < finrank F (subCode M W)) : False := by
  obtain ⟨hodd, hd, hsing⟩ := start_facts ih hlt
  obtain ⟨v₀, hv₀, hv₀rec⟩ := exists_small_rec hstar hodd
  obtain ⟨k, hk⟩ := hodd
  -- every good chain is tight and its code lies inside the code of `W`
  have inv : ∀ c, GoodChain M W v₀ c → subCode M (W \ chainX v₀ c) ≤ subCode M W ∧
      finrank F (subCode M (W \ chainX v₀ c)) = (W.card - (chainX v₀ c).card) / 2 := by
    intro c
    induction c with
    | nil =>
      intro _
      obtain ⟨h1, h2⟩ := hsing v₀ hv₀
      change subCode M (W \ {v₀}) ≤ subCode M W ∧
        finrank F (subCode M (W \ {v₀})) = (W.card - ({v₀} : Finset V).card) / 2
      refine ⟨by rw [h1]; exact inf_le_left, ?_⟩
      rw [h2, Finset.card_singleton]
      omega
    | cons e c ihc =>
      obtain ⟨r, p, q⟩ := e
      intro h
      obtain ⟨hle, hdim⟩ := ihc h.1
      obtain ⟨hp, hq⟩ := GoodChain.mem_pair h
      have hr : r ∈ chainX v₀ c := h.2.1
      have hpq : p ≠ q := h.2.2.1
      have hset : recSet M r ∩ (W \ chainX v₀ c) = {p, q} := h.2.2.2
      have hXW := chainX_subset hv₀ c h.1
      have hcard := chainX_card c h.1
      have hcardW := Finset.card_le_card hXW
      have hpar : Even (W.card - (chainX v₀ c).card) :=
        ⟨(W.card - (chainX v₀ c).card) / 2, by omega⟩
      have hiff : ∀ y ∈ subCode M (W \ chainX v₀ c), y p = 0 ↔ y q = 0 := by
        intro y hy
        have hrow := row_sum_eq_zero (hle hy) (hXW hr) {p, q} (by
          intro w hMw hyw
          have hwS : w ∈ W \ chainX v₀ c := by
            by_contra hw
            exact hyw (hy.1 w hw)
          have hwr : w ≠ r := fun e => (Finset.mem_sdiff.mp hwS).2 (e ▸ hr)
          have hw : w ∈ recSet M r ∩ (W \ chainX v₀ c) :=
            Finset.mem_inter.mpr ⟨mem_recSet.mpr ⟨hwr, hMw⟩, hwS⟩
          rwa [hset] at hw)
        rw [Finset.sum_pair hpq] at hrow
        have hMp : M r p ≠ 0 := (mem_recSet.mp (Finset.mem_inter.mp hp).1).2
        have hMq : M r q ≠ 0 := (mem_recSet.mp (Finset.mem_inter.mp hq).1).2
        constructor
        · intro h0
          rw [h0, mul_zero, zero_add] at hrow
          exact (mul_eq_zero.mp hrow).resolve_left hMq
        · intro h0
          rw [h0, mul_zero, add_zero] at hrow
          exact (mul_eq_zero.mp hrow).resolve_left hMp
      obtain ⟨heq, hdim'⟩ := pair_step ih hXW hpar hdim (Finset.mem_inter.mp hp).2
        (Finset.mem_inter.mp hq).2 hpq hiff
      have hcard' := chainX_card ((r, p, q) :: c) h
      simp only [chainX, List.length_cons] at hcard'
      change subCode M (W \ insert p (insert q (chainX v₀ c))) ≤ subCode M W ∧
        finrank F (subCode M (W \ insert p (insert q (chainX v₀ c)))) =
          (W.card - (insert p (insert q (chainX v₀ c))).card) / 2
      refine ⟨by rw [heq]; exact le_trans inf_le_left hle, ?_⟩
      rw [hdim', hcard', hcard]
      omega
  -- a maximal good chain gives too many determined coordinates
  have final : ∀ n, ∀ c, GoodChain M W v₀ c → W.card - (chainX v₀ c).card = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro c hc hn
      obtain ⟨hle, hdim⟩ := inv c hc
      have hXW := chainX_subset hv₀ c hc
      have hcard := chainX_card c hc
      have hcardW := Finset.card_le_card hXW
      have hpar : Even (W.card - (chainX v₀ c).card) :=
        ⟨(W.card - (chainX v₀ c).card) / 2, by omega⟩
      have hle2 : ∀ u ∈ chainX v₀ c, (recSet M u ∩ (W \ chainX v₀ c)).card ≤ 2 := by
        intro u hu
        by_cases hu0 : u = v₀
        · rw [hu0]
          calc (recSet M v₀ ∩ (W \ chainX v₀ c)).card ≤ (recSet M v₀ ∩ W).card :=
                Finset.card_le_card (Finset.inter_subset_inter_left Finset.sdiff_subset)
            _ ≤ 2 := hv₀rec
        · obtain ⟨r, hr, hur⟩ := chain_parent c hc u hu hu0
          rcases hstar u (hXW hu) with h2 | ⟨h3, hrecip⟩
          · exact (Finset.card_le_card Finset.inter_subset_left).trans h2
          · have hrS : r ∈ recSet M u := hrecip r hur
            calc (recSet M u ∩ (W \ chainX v₀ c)).card ≤ ((recSet M u).erase r).card := by
                  apply Finset.card_le_card
                  intro w hw
                  obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
                  refine Finset.mem_erase.mpr ⟨?_, hw1⟩
                  rintro rfl
                  exact (Finset.mem_sdiff.mp hw2).2 hr
              _ = 2 := by rw [Finset.card_erase_of_mem hrS, h3]
      have hne1 : ∀ u ∈ chainX v₀ c, (recSet M u ∩ (W \ chainX v₀ c)).card ≠ 1 := by
        intro u hu h1
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
        have hwmem : w ∈ recSet M u ∩ (W \ chainX v₀ c) := by rw [hw]; simp
        apply no_forced_zero ih hXW hpar hdim (Finset.mem_inter.mp hwmem).2
        intro y hy
        have hrow := row_sum_eq_zero (hle hy) (hXW hu) {w} (by
          intro z hMz hyz
          have hzS : z ∈ W \ chainX v₀ c := by
            by_contra hz
            exact hyz (hy.1 z hz)
          have hzu : z ≠ u := fun e => (Finset.mem_sdiff.mp hzS).2 (e ▸ hu)
          have hz : z ∈ recSet M u ∩ (W \ chainX v₀ c) :=
            Finset.mem_inter.mpr ⟨mem_recSet.mpr ⟨hzu, hMz⟩, hzS⟩
          rwa [hw] at hz)
        rw [Finset.sum_singleton] at hrow
        have hMw : M u w ≠ 0 := (mem_recSet.mp (Finset.mem_inter.mp hwmem).1).2
        exact (mul_eq_zero.mp hrow).resolve_left hMw
      by_cases hext : ∃ u ∈ chainX v₀ c, (recSet M u ∩ (W \ chainX v₀ c)).card = 2
      · obtain ⟨u, hu, h2⟩ := hext
        obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp h2
        have hc' : GoodChain M W v₀ ((u, p, q) :: c) := ⟨hc, hu, hpq, hset⟩
        have hX' := chainX_subset hv₀ _ hc'
        have hcard' := chainX_card _ hc'
        have hcardW' := Finset.card_le_card hX'
        simp only [List.length_cons] at hcard'
        exact ihn _ (by omega) ((u, p, q) :: c) hc' rfl
      · push Not at hext
        have hempty : ∀ u ∈ chainX v₀ c, recSet M u ∩ (W \ chainX v₀ c) = ∅ := by
          intro u hu
          have h2 := hle2 u hu
          have h1 := hne1 u hu
          have h2' := hext u hu
          exact Finset.card_eq_zero.mp (by omega)
        cases c with
        | nil =>
          -- the row of `v₀` forces `x v₀ = 0` on the whole code
          have hz : subCode M W ≤ zeroOn {v₀} := by
            intro x hx u hu
            rw [Finset.mem_singleton.mp hu]
            have hrow := row_sum_eq_zero hx hv₀ {v₀} (by
              intro z hMz hxz
              by_contra hzv
              have hzW : z ∈ W := by
                by_contra hz
                exact hxz (hx.1 z hz)
              have hz : z ∈ recSet M v₀ ∩ (W \ chainX v₀ []) := by
                refine Finset.mem_inter.mpr ⟨mem_recSet.mpr ⟨fun e => hzv (by simp [e]), hMz⟩, ?_⟩
                simp only [chainX, Finset.mem_sdiff, Finset.mem_singleton]
                exact ⟨hzW, fun e => hzv (by simp [e])⟩
              rw [hempty v₀ (by simp [chainX])] at hz
              simp at hz)
            rw [Finset.sum_singleton, hyp.diag, one_mul] at hrow
            exact hrow
          have hle' : subCode M W ≤ subCode M (W \ {v₀}) := by
            rw [(hsing v₀ hv₀).1]
            exact le_inf le_rfl hz
          have := Submodule.finrank_mono hle'
          rw [(hsing v₀ hv₀).2] at this
          omega
        | cons e rest =>
          obtain ⟨r, p, q⟩ := e
          obtain ⟨hp, hq⟩ := GoodChain.mem_pair hc
          have hrest : GoodChain M W v₀ rest := hc.1
          have hqp : q ∉ recSet M p :=
            hyp.triangleFree r p q (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1
          have hpX : p ∈ chainX v₀ ((r, p, q) :: rest) := by simp [chainX]
          have hpW : p ∈ W := hXW hpX
          -- codewords vanishing on `chainD rest` vanish on the whole chain
          have hdet : subCode M W ⊓ zeroOn (chainD v₀ rest) ≤
              subCode M (W \ chainX v₀ ((r, p, q) :: rest)) := by
            rintro x ⟨hx, hxD⟩
            have hXr := chain_det hv₀ rest hrest x hx hxD
            have hrow := row_sum_eq_zero hx hpW {p} (by
              intro z hMz hxz
              by_contra hzp
              have hzW : z ∈ W := by
                by_contra hz
                exact hxz (hx.1 z hz)
              have hzrest : z ∉ chainX v₀ rest := fun h => hxz (hXr z h)
              have hzrec : z ∈ recSet M p := mem_recSet.mpr ⟨fun e => hzp (by simp [e]), hMz⟩
              by_cases hzX : z ∈ chainX v₀ ((r, p, q) :: rest)
              · simp only [chainX, Finset.mem_insert] at hzX
                rcases hzX with hzX | hzX | hzX
                · exact hzp (by simp [hzX])
                · exact hqp (hzX ▸ hzrec)
                · exact hzrest hzX
              · have hz : z ∈ recSet M p ∩ (W \ chainX v₀ ((r, p, q) :: rest)) :=
                  Finset.mem_inter.mpr ⟨hzrec, Finset.mem_sdiff.mpr ⟨hzW, hzX⟩⟩
                rw [hempty p hpX] at hz
                simp at hz)
            rw [Finset.sum_singleton, hyp.diag, one_mul] at hrow
            have hxD' : ∀ u ∈ chainD v₀ ((r, p, q) :: rest), x u = 0 := by
              intro u hu
              simp only [chainD, Finset.mem_insert] at hu
              rcases hu with hu | hu
              · rw [hu]
                exact hrow
              · exact hxD u hu
            have hXc := chain_det hv₀ _ hc x hx hxD'
            exact subCode_inf_zeroOn_le M W _ ⟨hx, hXc⟩
          have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M W) (chainD v₀ rest)
          have h2 := Submodule.finrank_mono hdet
          have h3 := chainD_card_le (v₀ := v₀) rest
          simp only [List.length_cons] at hcard
          omega
  exact final _ [] trivial rfl

/-- **Theorem S (half bound).** If `M` has unit diagonal and no recovery triangle,
then on every vertex set `W` on which (★★) holds the code has dimension at most
`⌊|W|/2⌋`. -/
theorem finrank_subCode_le_half (hyp : ThmSHyp M) :
    ∀ W : Finset V, (∀ v ∈ W, Star M v) → finrank F (subCode M W) ≤ W.card / 2 := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
    intro hstar
    by_contra hlt
    push Not at hlt
    exact chain_contradiction hyp hstar
      (fun t ht => ih t ht fun v hv => hstar v (ht.subset hv)) hlt

end Theorem

end Main

/-! ## Graphs of maximum degree at most three -/

/-- On a triangle-free graph, a pattern matrix with unit diagonal satisfies the
standing hypotheses of Theorem S. -/
theorem thmSHyp_of_cliqueFree [DecidableEq F] {G : SimpleGraph V} {M : Matrix V V F}
    (hdiag : ∀ v, M v v = 1) (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (htri : G.CliqueFree 3) : ThmSHyp M := by
  have hadj : ∀ v u, u ∈ recSet M v → G.Adj v u := by
    intro v u hu
    obtain ⟨hne, hM⟩ := mem_recSet.mp hu
    by_contra h
    exact hM (hpat v u (Ne.symm hne) h)
  refine ⟨hdiag, fun r p q hp hq hqp => ?_⟩
  exact htri {r, p, q} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hadj r p hp, hadj r q hq, hadj p q hqp⟩)

/-- On a graph of maximum degree at most 3, every pattern matrix satisfies (★★) at
every vertex. -/
theorem star_of_degree_le_three [DecidableEq F] {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Matrix V V F} (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0)
    (hdeg : ∀ v, G.degree v ≤ 3) (v : V) : Star M v := by
  have hpattern : ∀ v u, u ∈ recSet M v → G.Adj v u := by
    intro v u hu
    obtain ⟨hne, hM⟩ := mem_recSet.mp hu
    by_contra hadj
    exact hM (hpat v u (Ne.symm hne) hadj)
  have hsub : recSet M v ⊆ G.neighborFinset v := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset]
    exact hpattern v u hu
  have hcard := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  by_cases h2 : (recSet M v).card ≤ 2
  · exact Or.inl h2
  · right
    have hdv := hdeg v
    have heq : recSet M v = G.neighborFinset v :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        omega)
    refine ⟨by omega, fun r hr => ?_⟩
    rw [heq, SimpleGraph.mem_neighborFinset]
    exact (hpattern r v hr).symm

/-- **Theorem S.** On a triangle-free graph of maximum degree at most 3, every
matrix over any field with unit diagonal whose off-diagonal support lies in the
edges has nullity at most `⌊N/2⌋`. -/
theorem finrank_ker_le_half_of_degree_le_three {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Matrix V V F} (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ Fintype.card V / 2 := by
  classical
  have h := finrank_subCode_le_half (thmSHyp_of_cliqueFree hdiag hpat htri) univ
    (fun v _ => star_of_degree_le_three hpat hdeg v)
  rwa [subCode_univ, Finset.card_univ] at h

/-- **Theorem S, rank form**: `rank M ≥ ⌈N/2⌉`. -/
theorem rank_ge_half_of_degree_le_three {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Matrix V V F} (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) :
    (Fintype.card V + 1) / 2 ≤ M.rank := by
  have h1 := finrank_ker_le_half_of_degree_le_three hdiag hpat htri hdeg
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h2
  have h3 : M.rank = finrank F (LinearMap.range M.mulVecLin) := rfl
  omega

/-! ## Splitting along separated vertex sets (the Tutte–Berge form) -/

section Split

variable [DecidableEq F] {G : SimpleGraph V} {M : Matrix V V F}

/-- Codes split over vertex sets with no edges between them. -/
theorem finrank_subCode_union_le (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u) {A B : Finset V}
    (hdisj : Disjoint A B) (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b ∧ ¬ G.Adj b a) :
    finrank F (subCode M (A ∪ B)) ≤ finrank F (subCode M A) + finrank F (subCode M B) := by
  have hzero : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0 := by
    intro v u hvu hadj
    by_contra hM
    exact hadj (hpat v u (mem_recSet.mpr ⟨Ne.symm hvu, hM⟩))
  have hle : subCode M (A ∪ B) ≤ subCode M A ⊔ subCode M B := by
    intro x hx
    let xA : V → F := fun u => if u ∈ A then x u else 0
    let xB : V → F := fun u => if u ∈ A then 0 else x u
    have hxA : xA ∈ subCode M A := by
      refine ⟨fun u hu => by simp [xA, hu], fun v hv => ?_⟩
      have hrow := hx.2 v (Finset.mem_union_left B hv)
      rw [← hrow]
      apply Finset.sum_congr rfl
      intro u _
      by_cases huA : u ∈ A
      · simp [xA, huA]
      · simp only [xA, huA, ite_false, mul_zero]
        by_cases hxu : x u = 0
        · rw [hxu, mul_zero]
        · have huB : u ∈ B := by
            rcases Finset.mem_union.mp (by by_contra h; exact hxu (hx.1 u h)) with h | h
            · exact absurd h huA
            · exact h
          rw [hzero v u (fun e => huA (e ▸ hv)) (hsep v hv u huB).1, zero_mul]
    have hxB : xB ∈ subCode M B := by
      refine ⟨fun u hu => ?_, fun v hv => ?_⟩
      · by_cases huA : u ∈ A
        · simp [xB, huA]
        · simp only [xB, huA, ite_false]
          exact hx.1 u (by simp [huA, hu])
      · have hrow := hx.2 v (Finset.mem_union_right A hv)
        rw [← hrow]
        apply Finset.sum_congr rfl
        intro u _
        by_cases huA : u ∈ A
        · simp only [xB, huA, ite_true, mul_zero]
          have hvu : v ≠ u := fun e => Finset.disjoint_left.mp hdisj huA (e ▸ hv)
          rw [hzero v u hvu (hsep u huA v hv).2, zero_mul]
        · simp [xB, huA]
    have hsum : xA + xB = x := by
      funext u
      by_cases huA : u ∈ A <;> simp [xA, xB, huA]
    rw [← hsum]
    exact Submodule.add_mem_sup hxA hxB
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (subCode M A) (subCode M B)
  omega

/-- Codes split over a family of pairwise separated vertex sets. -/
theorem finrank_subCode_biUnion_le (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u)
    (P : Finset (Finset V)) (hdisj : (P : Set (Finset V)).PairwiseDisjoint id)
    (hsep : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → ∀ a ∈ B, ∀ b ∈ B', ¬ G.Adj a b) :
    finrank F (subCode M (P.biUnion id)) ≤ ∑ B ∈ P, finrank F (subCode M B) := by
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.biUnion_empty, Finset.sum_empty, subCode_empty, finrank_bot]
  | insert B P hB ih =>
    have hdisj' : (P : Set (Finset V)).PairwiseDisjoint id :=
      hdisj.subset (by intro x hx; simp only [Finset.coe_insert]; exact Or.inr hx)
    have hsep' : ∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → ∀ a ∈ C, ∀ b ∈ C', ¬ G.Adj a b :=
      fun C hC C' hC' hne => hsep C (Finset.mem_insert_of_mem hC) C' (Finset.mem_insert_of_mem hC') hne
    rw [Finset.biUnion_insert, Finset.sum_insert hB]
    change finrank F (subCode M (B ∪ P.biUnion id)) ≤ _
    have hBd : Disjoint B (P.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro C hC
      have hne : B ≠ C := fun e => hB (e ▸ hC)
      exact hdisj (Finset.mem_insert_self B P) (Finset.mem_insert_of_mem hC) hne
    have hBs : ∀ a ∈ B, ∀ b ∈ P.biUnion id, ¬ G.Adj a b ∧ ¬ G.Adj b a := by
      intro a ha b hb
      obtain ⟨C, hC, hbC⟩ := Finset.mem_biUnion.mp hb
      have hne : B ≠ C := fun e => hB (e ▸ hC)
      exact ⟨hsep B (Finset.mem_insert_self B P) C (Finset.mem_insert_of_mem hC) hne a ha b hbC,
        hsep C (Finset.mem_insert_of_mem hC) B (Finset.mem_insert_self B P) (Ne.symm hne) b hbC a ha⟩
    have h1 := finrank_subCode_union_le hpat hBd hBs
    have h2 := ih hdisj' hsep'
    omega

/-- **Theorem S, Tutte–Berge form.** Let `M` have unit diagonal, no recovery
triangle and off-diagonal support in the edges of `G`. For every vertex set `U`
outside which (★★) holds, and every partition of the remaining vertices into
pairwise separated blocks (for example the components of `G - U`),
`dim ker M ≤ |U| + Σ_B ⌊|B|/2⌋`. Minimising over `U`, the Tutte–Berge formula
turns the right side into the matching number. Taking `U` to contain the vertices
violating (★★) gives the heavy-vertex corollary. -/
theorem finrank_ker_le_barrier (hyp : ThmSHyp M) (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u)
    (U : Finset V) (hstar : ∀ v, v ∉ U → Star M v) (P : Finset (Finset V))
    (hcover : P.biUnion id = univ \ U) (hdisj : (P : Set (Finset V)).PairwiseDisjoint id)
    (hsep : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → ∀ a ∈ B, ∀ b ∈ B', ¬ G.Adj a b) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ U.card + ∑ B ∈ P, B.card / 2 := by
  rw [← subCode_univ]
  have h1 := finrank_le_card_add_finrank_inf_zeroOn (subCode M univ) U
  have h2 := Submodule.finrank_mono (subCode_inf_zeroOn_le M univ U)
  have h3 := finrank_subCode_biUnion_le hpat P hdisj hsep
  rw [hcover] at h3
  have h4 : ∑ B ∈ P, finrank F (subCode M B) ≤ ∑ B ∈ P, B.card / 2 := by
    apply Finset.sum_le_sum
    intro B hB
    apply finrank_subCode_le_half hyp B
    intro v hv
    have hv' : v ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨B, hB, hv⟩
    rw [hcover] at hv'
    exact hstar v (Finset.mem_sdiff.mp hv').2
  omega

open Classical in
/-- **Heavy vertices** (the half-bound form of the barrier with a single block): with `H` the set
of vertices violating (★★), `dim ker M ≤ |H| + ⌊(N − |H|)/2⌋`. -/
theorem finrank_ker_le_heavy (hyp : ThmSHyp M) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ (univ.filter fun v => ¬ Star M v).card +
      (Fintype.card V - (univ.filter fun v => ¬ Star M v).card) / 2 := by
  set H := univ.filter fun v => ¬ Star M v
  have h := finrank_ker_le_barrier (G := ⊤) hyp (fun v u hu => (mem_recSet.mp hu).1.symm) H
    (fun v hv => by simpa [H] using hv) {univ \ H} (by simp) (by simp) (by simp)
  rwa [Finset.sum_singleton, Finset.card_sdiff_of_subset (Finset.subset_univ H), Finset.card_univ] at h

end Split

/-! ## Linear storage codes -/

/-- A linear storage code on `G`: a subspace in which every coordinate is
determined by the neighbouring coordinates. -/
def IsLinearStorageCode (G : SimpleGraph V) (C : Submodule F (V → F)) : Prop :=
  ∀ v, ∀ x ∈ C, (∀ u, G.Adj v u → x u = 0) → x v = 0

omit [DecidableEq V] in
/-- In a linear storage code each coordinate is a fixed linear combination of the
neighbouring coordinates. -/
theorem IsLinearStorageCode.exists_coeffs {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : Submodule F (V → F)} (hC : IsLinearStorageCode G C) (v : V) :
    ∃ d : V → F, (∀ u, ¬ G.Adj v u → d u = 0) ∧ ∀ x ∈ C, x v = ∑ u, d u * x u := by
  let L : V → C →ₗ[F] F := fun u => if G.Adj v u then (LinearMap.proj u).comp C.subtype else 0
  let K : C →ₗ[F] F := (LinearMap.proj v).comp C.subtype
  have h : ⨅ u, LinearMap.ker (L u) ≤ LinearMap.ker K := by
    intro x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
    refine hC v x x.2 (fun u hu => ?_)
    have := hx u
    simpa [L, hu] using this
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (mem_span_of_iInf_ker_le_ker h)
  refine ⟨fun u => if G.Adj v u then c u else 0, fun u hu => by simp [hu], ?_⟩
  intro x hx
  have h1 := congrArg (fun f => f ⟨x, hx⟩) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, K, LinearMap.comp_apply,
    Submodule.coe_subtype, LinearMap.proj_apply] at h1
  rw [← h1]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : G.Adj v u <;> simp [L, hu]

/-- Every linear storage code lies in the kernel of a pattern matrix. -/
theorem IsLinearStorageCode.exists_pattern {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : Submodule F (V → F)} (hC : IsLinearStorageCode G C) :
    ∃ M : Matrix V V F, (∀ v, M v v = 1) ∧ (∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) ∧
      C ≤ LinearMap.ker M.mulVecLin := by
  choose d hd0 hd using hC.exists_coeffs
  refine ⟨Matrix.of fun v u => (if u = v then 1 else 0) - d v u, ?_, ?_, ?_⟩
  · intro v
    simp [Matrix.of_apply, hd0 v v (G.loopless.irrefl v)]
  · intro v u hvu hadj
    simp [Matrix.of_apply, Ne.symm hvu, hd0 v u hadj]
  · intro x hx
    rw [LinearMap.mem_ker]
    funext v
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    rw [← hd v x hx, sub_self]

/-- **Theorem S for linear storage codes.** On a triangle-free graph of maximum
degree at most 3, every linear storage code over any field has dimension at most
`⌊N/2⌋`. -/
theorem IsLinearStorageCode.finrank_le_half {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : Submodule F (V → F)} (hC : IsLinearStorageCode G C) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) : finrank F C ≤ Fintype.card V / 2 := by
  obtain ⟨M, hdiag, hpat, hle⟩ := hC.exists_pattern
  exact (Submodule.finrank_mono hle).trans
    (finrank_ker_le_half_of_degree_le_three hdiag hpat htri hdeg)

/-- Over a finite field: `|C|² ≤ |F|^N`. -/
theorem IsLinearStorageCode.card_sq_le [Fintype F] {G : SimpleGraph V} [DecidableRel G.Adj]
    {C : Submodule F (V → F)} [Fintype C] (hC : IsLinearStorageCode G C)
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    Fintype.card C ^ 2 ≤ Fintype.card F ^ Fintype.card V := by
  have h := hC.finrank_le_half htri hdeg
  rw [Module.card_eq_pow_finrank (K := F) (V := C), ← pow_mul]
  apply Nat.pow_le_pow_right Fintype.card_pos
  omega

omit [DecidableEq V] in
/-- Conversely, every subspace of the kernel of a matrix with unit diagonal and off-diagonal support in
the edges of `G` is a linear storage code: `x_v = -Σ_{u ~ v} M_{vu} x_u`. -/
theorem isLinearStorageCode_of_le_ker {G : SimpleGraph V} {M : Matrix V V F} (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) {C : Submodule F (V → F)}
    (hle : C ≤ LinearMap.ker M.mulVecLin) : IsLinearStorageCode G C := by
  intro v x hx hzero
  have hrow : ∑ u, M v u * x u = 0 := by
    have := congrFun (LinearMap.mem_ker.mp (hle hx)) v
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this
  rw [Finset.sum_eq_single v (fun u _ huv => ?_) (by simp), hdiag v, one_mul] at hrow
  · exact hrow
  · by_cases hadj : G.Adj v u
    · rw [hzero u hadj, mul_zero]
    · rw [hpat v u (Ne.symm huv) hadj, zero_mul]

open Classical in
/-- Over a finite field, a subspace is a storage code in the sense of `IsStorageCode` (agreement on
the neighbourhood forces agreement) exactly when it is a linear storage code (`IsLinearStorageCode`,
vanishing on the neighbourhood forces vanishing). -/
theorem isStorageCode_iff_isLinearStorageCode [Fintype F] {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : Submodule F (V → F)) :
    IsStorageCode (nbhd G) (univ.filter (· ∈ C)) ↔ IsLinearStorageCode G C := by
  constructor
  · intro h v x hx hzero
    have := h x (by simpa using hx) 0 (by simp) v
      (fun u hu => by
        simp only [nbhd, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        simpa using hzero u hu)
    simpa using this
  · intro h x hx y hy v hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hsub : x - y ∈ C := C.sub_mem hx hy
    have := h v (x - y) hsub (fun u hu => by
      have := hxy u (by simpa [nbhd] using hu)
      simp [this])
    simpa [sub_eq_zero] using this

/-! ## The matching code -/

/-- The encoding map of a matching with edges `u i — w i`: the vector equal to `g i` on both
ends of edge `i` and zero elsewhere. -/
def matchingEncode {m : ℕ} (u w : Fin m → V) : (Fin m → F) →ₗ[F] (V → F) where
  toFun g v := ∑ i, if v = u i ∨ v = w i then g i else 0
  map_add' g g' := by
    funext v
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  map_smul' c g := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp

omit [Fintype V] in
theorem matchingEncode_other {m : ℕ} {u w : Fin m → V} (g : Fin m → F) {v : V} (hu : ∀ i, v ≠ u i) (hw : ∀ i, v ≠ w i) :
    matchingEncode (F := F) u w g v = 0 := by
  show (∑ i, if v = u i ∨ v = w i then g i else 0) = 0
  exact Finset.sum_eq_zero fun i _ => by simp [hu i, hw i]


section
variable {m : ℕ} {u w : Fin m → V} (hinj : Function.Injective (Sum.elim u w))
include hinj

omit [Fintype V] [DecidableEq V] in
theorem matching_u_inj {i j : Fin m} : u i = u j ↔ i = j :=
  ⟨fun h => Sum.inl_injective (hinj (by simpa using h)), fun h => h ▸ rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem matching_w_inj {i j : Fin m} : w i = w j ↔ i = j :=
  ⟨fun h => Sum.inr_injective (hinj (by simpa using h)), fun h => h ▸ rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem matching_u_ne_w (i j : Fin m) : u i ≠ w j := fun h =>
  Sum.inl_ne_inr (hinj (by simpa using h))

omit [Fintype V] in
theorem matchingEncode_u (g : Fin m → F) (j : Fin m) : matchingEncode (F := F) u w g (u j) = g j := by
  show (∑ i, if u j = u i ∨ u j = w i then g i else 0) = g j
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have h1 : ¬ u j = u i := fun h => hij ((matching_u_inj hinj).mp h).symm
    have h2 : ¬ u j = w i := matching_u_ne_w hinj j i
    simp [h1, h2]
  · simp

omit [Fintype V] in
theorem matchingEncode_w (g : Fin m → F) (j : Fin m) : matchingEncode (F := F) u w g (w j) = g j := by
  show (∑ i, if w j = u i ∨ w j = w i then g i else 0) = g j
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have h1 : ¬ w j = u i := fun h => matching_u_ne_w hinj i j h.symm
    have h2 : ¬ w j = w i := fun h => hij ((matching_w_inj hinj).mp h).symm
    simp [h1, h2]
  · simp

omit [Fintype V] in
theorem matchingEncode_injective : Function.Injective (matchingEncode (F := F) u w) := by
  intro g g' h
  funext j
  rw [← matchingEncode_u hinj g j, ← matchingEncode_u hinj g' j, h]

end

omit [Fintype V] in
/-- **The matching code.** If `u i — w i` (`i < m`) are `m` pairwise disjoint edges of `G`, then
the vectors constant on each of these edges and zero elsewhere form a linear storage code on `G`,
over any field, of dimension `m`. -/
theorem exists_linearStorageCode_of_matching {G : SimpleGraph V} {m : ℕ} (u w : Fin m → V)
    (hadj : ∀ i, G.Adj (u i) (w i)) (hinj : Function.Injective (Sum.elim u w)) :
    ∃ C : Submodule F (V → F), IsLinearStorageCode G C ∧ finrank F C = m := by
  refine ⟨LinearMap.range (matchingEncode (F := F) u w), ?_, ?_⟩
  · rintro v x ⟨g, rfl⟩ hzero
    by_cases hu : ∃ j, v = u j
    · obtain ⟨j, rfl⟩ := hu
      have := hzero (w j) (hadj j)
      rw [matchingEncode_w hinj] at this
      rw [matchingEncode_u hinj, this]
    · by_cases hw : ∃ j, v = w j
      · obtain ⟨j, rfl⟩ := hw
        have := hzero (u j) (hadj j).symm
        rw [matchingEncode_u hinj] at this
        rw [matchingEncode_w hinj, this]
      · push Not at hu hw
        exact matchingEncode_other g hu hw
  · rw [LinearMap.finrank_range_of_inj (matchingEncode_injective hinj), Module.finrank_fin_fun]

/-- **Minrank and matchings.** For every matching of `m` edges there is a matrix with unit
diagonal and off-diagonal support in the edges of `G` whose nullity is at least `m`. -/
theorem exists_pattern_finrank_ker_ge_of_matching {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    (u w : Fin m → V) (hadj : ∀ i, G.Adj (u i) (w i)) (hinj : Function.Injective (Sum.elim u w)) :
    ∃ M : Matrix V V F, (∀ v, M v v = 1) ∧ (∀ v u', v ≠ u' → ¬ G.Adj v u' → M v u' = 0) ∧
      m ≤ finrank F (LinearMap.ker M.mulVecLin) := by
  obtain ⟨C, hC, hdim⟩ := exists_linearStorageCode_of_matching (F := F) u w hadj hinj
  obtain ⟨M, hdiag, hpat, hle⟩ := hC.exists_pattern
  exact ⟨M, hdiag, hpat, hdim ▸ Submodule.finrank_mono hle⟩

end MotionDepthCodes
