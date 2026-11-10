import SwapRigidity.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Relation

/-!
# Class-uniform rules on a cycle (Theorem TP, the translate pigeonhole)

Matrices are indexed by `ZMod n`.  The map `rot c` rotates the columns of a matrix by `c`.
A subspace `𝒳` of matrices is a *class-uniform code* for a colouring `cls` of the rows if row
`c` of every `X ∈ 𝒳` is a fixed linear function of `rot c X` that depends only on the class of
`c` (`IsClassUniformCode`).

The main results bound the dimension of such a code.

* `IsClassUniformCode.row_eq_of_rot_mem`: covariance.  If two rotates of `X` lie in the code,
  rows of one class whose index sums agree are rotates of one another.
* `IsClassUniformCode.finrank_le`: for a non-empty set `Δ` of shifts and a set `S` of rows
  that meets every component of the link graph,
  `|Δ| * dim 𝒳 ≤ (|Δ| - 1) * n ^ 2 + n * |S|`.
* `IsClassUniformCode.two_mul_finrank_le`: with the shifts `{0, 1}` and `S` containing every
  row at which the class changes, `2 * dim 𝒳 ≤ n ^ 2 + n * |S|`.
* `IsClassUniformCode.two_mul_finrank_le_of_const`: for one class, `2 * dim 𝒳 ≤ n ^ 2 + n`.
-/

namespace SwapRigidity

open Module

variable {F : Type*} [Field F] {n : ℕ} {κ : Type*}

/-- Rotation of the columns of a matrix indexed by `ZMod n`: `(rot c X) i j = X i (j + c)`. -/
def rot (c : ZMod n) : Matrix (ZMod n) (ZMod n) F →ₗ[F] Matrix (ZMod n) (ZMod n) F where
  toFun X := Matrix.of fun i j => X i (j + c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Entries of a rotated matrix. -/
@[simp]
theorem rot_apply (c : ZMod n) (X : Matrix (ZMod n) (ZMod n) F) (i j : ZMod n) :
    rot c X i j = X i (j + c) :=
  rfl

/-- Rotations compose by adding the shifts. -/
theorem rot_rot (c δ : ZMod n) (X : Matrix (ZMod n) (ZMod n) F) :
    rot c (rot δ X) = rot (c + δ) X := by
  ext i j
  simp [add_assoc]

/-- The space of `n × n` matrices indexed by `ZMod n` has dimension `n * n`. -/
theorem finrank_matrix_zmod [NeZero n] : finrank F (Matrix (ZMod n) (ZMod n) F) = n * n := by
  rw [Module.finrank_matrix, ZMod.card, finrank_self, mul_one]

/-- A subspace `𝒳` of matrices is a *class-uniform code* for the row colouring `cls` if there
are linear decoders `dec k`, one for each class `k`, such that row `c` of every `X ∈ 𝒳` is
`dec (cls c)` applied to `X` with its columns rotated by `c`. -/
def IsClassUniformCode (cls : ZMod n → κ) (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    Prop :=
  ∃ dec : κ → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F)),
    ∀ X ∈ 𝒳, ∀ c, X c = dec (cls c) (rot c X)

/-- The link relation of Theorem TP: rows `c` and `c'` lie in one class and
`c + δ = c' + δ'` for two shifts `δ, δ' ∈ Δ`. -/
def Link (cls : ZMod n → κ) (Δ : Finset (ZMod n)) (c c' : ZMod n) : Prop :=
  cls c = cls c' ∧ ∃ δ ∈ Δ, ∃ δ' ∈ Δ, c + δ = c' + δ'

namespace IsClassUniformCode

variable {cls : ZMod n → κ} {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)}

/-- **Covariance.**  If the rotates of `X` by `δ` and by `δ'` both lie in a class-uniform code,
and `c`, `c'` are rows of one class with `c + δ = c' + δ'`, then row `c'` is row `c` rotated
by `c' - c`: `X c' (j + δ') = X c (j + δ)` for all `j`. -/
theorem row_eq_of_rot_mem (h : IsClassUniformCode cls 𝒳) {X : Matrix (ZMod n) (ZMod n) F}
    {c c' δ δ' : ZMod n} (hδ : rot δ X ∈ 𝒳) (hδ' : rot δ' X ∈ 𝒳) (hcls : cls c = cls c')
    (hc : c + δ = c' + δ') (j : ZMod n) : X c' (j + δ') = X c (j + δ) := by
  obtain ⟨dec, hdec⟩ := h
  have h1 := hdec _ hδ c
  have h2 := hdec _ hδ' c'
  rw [rot_rot, hc] at h1
  rw [rot_rot, ← hcls] at h2
  exact congrFun (h2.trans h1.symm) j

/-- In the common preimage of a class-uniform code under the rotations in `Δ`, a row vanishes
if and only if every row in the same component of the link graph vanishes. -/
theorem row_eq_zero_iff_of_eqvGen (h : IsClassUniformCode cls 𝒳) {Δ : Finset (ZMod n)}
    {X : Matrix (ZMod n) (ZMod n) F} (hX : ∀ δ ∈ Δ, rot δ X ∈ 𝒳) {c c' : ZMod n}
    (hcc' : Relation.EqvGen (Link cls Δ) c c') : X c = 0 ↔ X c' = 0 := by
  induction hcc' with
  | rel a b hab =>
    obtain ⟨hcls, δ, hδ, δ', hδ', hsum⟩ := hab
    have key := h.row_eq_of_rot_mem (hX δ hδ) (hX δ' hδ') hcls hsum
    constructor
    · intro ha
      funext j
      have hj := key (j - δ')
      rw [sub_add_cancel] at hj
      rw [hj, ha]
      rfl
    · intro hb
      funext j
      have hj := key (j - δ)
      rw [sub_add_cancel] at hj
      rw [← hj, hb]
      rfl
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable [NeZero n]

/-- **Theorem TP, general shift set.**  Let `Δ` be a non-empty set of shifts and
let `S` be a set of rows such that every row is joined to a row of `S` in the equivalence
closure `Relation.EqvGen` of the link relation `Link cls Δ` (so `|S|` is at least the number
of components of the link graph, with equality for a set of representatives).  Then every
class-uniform code satisfies `|Δ| * dim 𝒳 ≤ (|Δ| - 1) * n ^ 2 + n * |S|`. -/
theorem finrank_le (h : IsClassUniformCode cls 𝒳) {Δ : Finset (ZMod n)} (hΔ : Δ.Nonempty)
    {S : Finset (ZMod n)} (hS : ∀ c, ∃ s ∈ S, Relation.EqvGen (Link cls Δ) c s) :
    Δ.card * finrank F 𝒳 ≤ (Δ.card - 1) * n ^ 2 + n * S.card := by
  -- the common preimage of the code under the rotations in `Δ`
  set 𝒳' : Submodule F (Matrix (ZMod n) (ZMod n) F) := ⨅ δ ∈ Δ, 𝒳.comap (rot δ) with h𝒳'
  have hmem : ∀ X ∈ 𝒳', ∀ δ ∈ Δ, rot δ X ∈ 𝒳 := by
    intro X hX δ hδ
    simp only [h𝒳', Submodule.mem_iInf, Submodule.mem_comap] at hX
    exact hX δ hδ
  -- pigeonhole: the common preimage is large
  have hcount : Δ.card * finrank F 𝒳 + n * n ≤ Δ.card * (n * n) + finrank F 𝒳' := by
    have := card_mul_finrank_add_le_iInf_comap Δ 𝒳 (fun δ => rot δ)
    rwa [finrank_matrix_zmod] at this
  -- restriction to the rows in `S` is injective on the common preimage
  let res : 𝒳' →ₗ[F] (S → ZMod n → F) :=
    { toFun := fun X s => (X : Matrix (ZMod n) (ZMod n) F) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    funext c
    obtain ⟨s, hs, hcs⟩ := hS c
    exact (h.row_eq_zero_iff_of_eqvGen (hmem X X.2) hcs).2 (congrFun hX ⟨s, hs⟩)
  have hdim : finrank F 𝒳' ≤ n * S.card := by
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hpi : finrank F (S → ZMod n → F) = n * S.card := by
      rw [Module.finrank_pi_fintype]
      simp [ZMod.card, mul_comm]
    rwa [hpi] at hle
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hΔ.card_pos.ne'
  rw [hk, Nat.succ_eq_add_one, add_mul, one_mul, add_mul, one_mul] at hcount
  rw [hk, Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_two, add_mul, one_mul]
  omega

/-- **Theorem TP, unit shift.**  Let `S` be a non-empty set of rows containing
every row `c` whose class differs from that of `c - 1` (for cyclic interval classes: the first
row of each interval).  Then `2 * dim 𝒳 ≤ n ^ 2 + n * |S|`. -/
theorem two_mul_finrank_le (h : IsClassUniformCode cls 𝒳) {S : Finset (ZMod n)}
    (hS : S.Nonempty) (hcls : ∀ c ∉ S, cls (c - 1) = cls c) :
    2 * finrank F 𝒳 ≤ n ^ 2 + n * S.card := by
  have hlink : ∀ c ∉ S, Link cls {0, 1} (c - 1) c := fun c hc =>
    ⟨hcls c hc, 1, by simp, 0, by simp, by simp⟩
  -- walking down from `c` reaches `S`
  have hstep : ∀ k : ℕ, ∀ c : ZMod n, c - (k : ZMod n) ∈ S →
      ∃ s ∈ S, Relation.EqvGen (Link cls {0, 1}) c s := by
    intro k
    induction k with
    | zero =>
      intro c hc
      exact ⟨c, by simpa using hc, Relation.EqvGen.refl _⟩
    | succ k ih =>
      intro c hc
      by_cases hcS : c ∈ S
      · exact ⟨c, hcS, Relation.EqvGen.refl _⟩
      · have hc' : c - 1 - (k : ZMod n) ∈ S := by
          have e : c - 1 - (k : ZMod n) = c - ((k + 1 : ℕ) : ZMod n) := by
            push_cast
            ring
          rwa [e]
        obtain ⟨s, hs, hrel⟩ := ih (c - 1) hc'
        exact ⟨s, hs, Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (hlink c hcS))) hrel⟩
  have hconn : ∀ c, ∃ s ∈ S, Relation.EqvGen (Link cls {0, 1}) c s := by
    intro c
    obtain ⟨s₀, hs₀⟩ := hS
    refine hstep (c - s₀).val c ?_
    rwa [ZMod.natCast_zmod_val, sub_sub_cancel]
  have hmain := h.finrank_le (Δ := {0, 1}) (Finset.insert_nonempty _ _) hconn
  by_cases h01 : (0 : ZMod n) = 1
  · -- `n = 1`: the shift set is a singleton, and the trivial bound suffices
    have hD : finrank F 𝒳 ≤ n * n := finrank_matrix_zmod (F := F) (n := n) ▸ 𝒳.finrank_le
    rw [← h01, Finset.pair_eq_singleton, Finset.card_singleton, pow_two] at hmain
    rw [pow_two]
    omega
  · rw [Finset.card_pair h01] at hmain
    omega

/-- **Theorem TP, one class.**  If all rows have the same class, then
`2 * dim 𝒳 ≤ n ^ 2 + n`: the pairing bound `n (n + 1) / 2`. -/
theorem two_mul_finrank_le_of_const (h : IsClassUniformCode cls 𝒳)
    (hconst : ∀ c c', cls c = cls c') : 2 * finrank F 𝒳 ≤ n ^ 2 + n := by
  have := h.two_mul_finrank_le (S := {0}) (Finset.singleton_nonempty 0)
    (fun c _ => hconst _ _)
  simpa using this

end IsClassUniformCode

end SwapRigidity
