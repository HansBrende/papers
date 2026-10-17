import Transpose.Tape.PlainRobust.CEVote

/-!
# Plain ⟹ robust for linear codes

A code is **linear** (over `F₂`, edge values read as bit vectors) if XOR-ing two inputs XORs every
encoded and decoded value (`NetCode.IsLinear`). For a linear code the set of inputs on which it is
correct is closed under XOR (`correct_xor`), so it is a subspace; if it contains a set `F` of
co-entropy `≤ C n w`, it is a subspace of codimension `≤ C n w`, i.e. the kernel of an additive
syndrome map, and `noCode_affine_of_noCode` applies. Hence `NoCode_TM` rules out linear codes on
every set of co-entropy `O(n w)` (`noCode_linear_of_noCode`): a counterexample to plain ⟹ robust must
use a nonlinear code.
-/

namespace Transpose.Tape.Impl

open Transpose TSDiagram

/-- A code is **linear**: XOR-ing the inputs (in-values and visible bits) XORs every value. -/
def _root_.Transpose.Tape.NetCode.IsLinear (C : NetCode) : Prop :=
  (∀ e (f f' : ℕ × ℕ → ℕ) (v v' : ℕ → Bool),
    C.enc e (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) = C.enc e f v ^^^ C.enc e f' v') ∧
  (∀ o (f f' : ℕ × ℕ → ℕ) (v v' : ℕ → Bool),
    C.dec o (fun e' => f e' ^^^ f' e') (fun d => xor (v d) (v' d)) =
      xor (C.dec o f v) (C.dec o f' v'))

section Linear

variable {k : ℕ} (D : TSDiagram k)

theorem visible_xorVec (n w r y : ℕ) {L : ℕ} (x x' : Fin L → Bool) :
    D.visible n w r y (xorVec x x') =
      fun d => xor (D.visible n w r y x d) (D.visible n w r y x' d) := by
  funext d
  simp only [TSDiagram.visible, xorVec]
  split_ifs <;> simp

/-- **The values of a linear code are XOR-linear in the input.** -/
theorem inVals_xor {C : NetCode} (hC : C.IsLinear) (E : Finset (ℕ × ℕ)) (vis vis' : ℕ → ℕ → Bool) :
    ∀ u, C.inVals E (fun y d => xor (vis y d) (vis' y d)) u =
      fun e => C.inVals E vis u e ^^^ C.inVals E vis' u e := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  funext e
  rw [inVals_eq, inVals_eq, inVals_eq]
  split_ifs with hc
  · rw [ih e.1 hc.2.2]
    exact hC.1 e _ _ _ _
  · rfl

/-- **The inputs on which a linear code is correct are closed under XOR.** -/
theorem correct_xor {n G : ℕ} {C : NetCode} (hC : C.IsLinear)
    {x x' : Fin (n * n * entryBits n) → Bool}
    (hx : D.Solves n G (D.profileCap n G) {x} C) (hx' : D.Solves n G (D.profileCap n G) {x'} C) :
    D.Solves n G (D.profileCap n G) {xorVec x x'} C := by
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  obtain ⟨he, ho⟩ := hx x (Set.mem_singleton x)
  obtain ⟨he', ho'⟩ := hx' x' (Set.mem_singleton x')
  have hvis : (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x')) =
      fun y d => xor (D.visible n (entryBits n) (blockSize G n) y x d)
        (D.visible n (entryBits n) (blockSize G n) y x' d) := by
    funext y; exact visible_xorVec D _ _ _ y x x'
  have hin := inVals_xor hC (D.edges (blockSize G n))
    (fun y => D.visible n (entryBits n) (blockSize G n) y x)
    (fun y => D.visible n (entryBits n) (blockSize G n) y x')
  refine ⟨fun e hE => ?_, fun d hd => ?_⟩
  · show C.enc e (C.inVals _ (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x')) e.1)
      ((fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x')) e.1) < _
    rw [hvis, hin e.1]
    beta_reduce
    rw [hC.1]
    exact Nat.xor_lt_two_pow (he e hE) (he' e hE)
  · show C.dec _ (C.inVals _ (fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x')) _)
      ((fun y => D.visible n (entryBits n) (blockSize G n) y (xorVec x x')) _) = _
    rw [hvis, hin]
    beta_reduce
    rw [hC.2]
    have h1 := ho d hd
    have h2 := ho' d hd
    simp only [NetCode.outVal] at h1 h2
    rw [h1, h2]
    rfl

end Linear

/-! ### XOR-closed sets are kernels of syndrome maps -/

/-- Bits as `ZMod 2`. -/
def toW {L : ℕ} (x : Fin L → Bool) : Fin L → ZMod 2 := fun d => if x d then 1 else 0

theorem toW_xor {L : ℕ} (x y : Fin L → Bool) : toW (xorVec x y) = toW x + toW y := by
  funext d
  simp only [toW, xorVec, Pi.add_apply]
  rcases Bool.eq_false_or_eq_true (x d) with hx | hx <;>
    rcases Bool.eq_false_or_eq_true (y d) with hy | hy <;> simp [hx, hy]
  all_goals decide

theorem toW_injective {L : ℕ} : Function.Injective (toW (L := L)) := by
  intro x y h
  funext d
  have := congrFun h d
  simp only [toW] at this
  cases hx : x d <;> cases hy : y d <;> simp_all

theorem toW_zero {L : ℕ} : toW (fun _ : Fin L => false) = 0 := by
  funext d; simp [toW]

/-- An XOR-closed set containing `0`, as an additive subgroup of `Fin L → ZMod 2`. -/
def xorSubgroup {L : ℕ} (S : Set (Fin L → Bool)) (h0 : (fun _ => false) ∈ S)
    (hS : ∀ x y, x ∈ S → y ∈ S → xorVec x y ∈ S) : AddSubgroup (Fin L → ZMod 2) where
  carrier := toW '' S
  zero_mem' := ⟨_, h0, toW_zero⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨xorVec x y, hS x y hx hy, toW_xor x y⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    funext d
    simp only [toW, Pi.neg_apply]
    rcases Bool.eq_false_or_eq_true (x d) with h | h <;> simp [h]

/-- **An XOR-closed set of size `≥ 2^{L-m}` is the kernel of an additive map into at most `m` bits.** -/
theorem exists_syndrome {L m : ℕ} (S : Set (Fin L → Bool)) (h0 : (fun _ => false) ∈ S)
    (hS : ∀ x y, x ∈ S → y ∈ S → xorVec x y ∈ S) (hcard : 2 ^ L ≤ 2 ^ m * S.ncard) :
    ∃ (s : ℕ) (φ : (Fin L → Bool) → (Fin s → ZMod 2)), s ≤ m ∧
      (∀ x y, φ (xorVec x y) = φ x + φ y) ∧ ∀ x, φ x = 0 ↔ x ∈ S := by
  classical
  set A := xorSubgroup S h0 hS with hA
  set S' : Submodule (ZMod 2) (Fin L → ZMod 2) := AddSubgroup.toZModSubmodule 2 A with hS'
  set b := Module.finBasis (ZMod 2) ((Fin L → ZMod 2) ⧸ S') with hb
  refine ⟨Module.finrank (ZMod 2) ((Fin L → ZMod 2) ⧸ S'),
    fun x => b.equivFun (S'.mkQ (toW x)), ?_, ?_, ?_⟩
  · -- the dimension bound, by counting
    have hQ : Nat.card ((Fin L → ZMod 2) ⧸ S') =
        2 ^ Module.finrank (ZMod 2) ((Fin L → ZMod 2) ⧸ S') := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have hW : Nat.card (Fin L → ZMod 2) = 2 ^ L := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hLag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S'.toAddSubgroup
    have hsub : Nat.card S'.toAddSubgroup = S.ncard := by
      have e1 : Nat.card S'.toAddSubgroup = (toW '' S).ncard := Nat.card_coe_set_eq (toW '' S)
      rw [e1, Set.ncard_image_of_injective _ toW_injective]
    have hquot : Nat.card ((Fin L → ZMod 2) ⧸ S'.toAddSubgroup) =
        Nat.card ((Fin L → ZMod 2) ⧸ S') := rfl
    rw [hquot, hQ, hW, hsub] at hLag
    have hpos : 0 < S.ncard := by
      rcases Nat.eq_zero_or_pos S.ncard with h | h
      · rw [h, Nat.mul_zero] at hcard
        exact absurd hcard (Nat.not_le.2 (Nat.two_pow_pos _))
      · exact h
    have h2 : 2 ^ Module.finrank (ZMod 2) ((Fin L → ZMod 2) ⧸ S') * S.ncard ≤ 2 ^ m * S.ncard := by
      rw [← hLag]; exact hcard
    have h3 := Nat.le_of_mul_le_mul_right h2 hpos
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  · intro x y
    beta_reduce
    rw [toW_xor, map_add, map_add]
  · intro x
    rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show toW x ∈ (A : Set (Fin L → ZMod 2)) ↔ x ∈ S
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← toW_injective hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩

/-! ### Additive maps are row sums -/

/-- The vector with the bits of `u` on row `i` (as positions of `Fin L`) and `false` elsewhere. -/
def rowMask {L : ℕ} (n w i : ℕ) (u : ℕ → Bool) : Fin L → Bool :=
  fun d => if d.val / (n * w) = i then u d.val else false

/-- The rows `< j` of an input. -/
def prefixRows {L : ℕ} (n w j : ℕ) (x : Fin L → Bool) : Fin L → Bool :=
  fun d => if d.val / (n * w) < j then x d else false

theorem additive_zero {L s : ℕ} {φ : (Fin L → Bool) → (Fin s → ZMod 2)}
    (hφ : ∀ x y, φ (xorVec x y) = φ x + φ y) : φ (fun _ => false) = 0 := by
  have h := hφ (fun _ => false) (fun _ => false)
  have e : xorVec (fun _ : Fin L => false) (fun _ => false) = fun _ => false := by
    funext d; simp [xorVec]
  rw [e] at h
  have : φ (fun _ => false) + φ (fun _ => false) = φ (fun _ => false) + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

/-- **An additive map of the input is a row sum.** -/
theorem rowSum_additive {n w s : ℕ} {φ : (Fin (n * n * w) → Bool) → (Fin s → ZMod 2)}
    (hφ : ∀ x y, φ (xorVec x y) = φ x + φ y) (x : Fin (n * n * w) → Bool) :
    rowSum n w (fun i u => φ (rowMask n w i u)) x = φ x := by
  -- the partial sums are the values on the first rows
  have step : ∀ j, ∑ i ∈ Finset.range j, φ (rowMask n w i (rowOf n w i (xbits x))) =
      φ (prefixRows n w j x) := by
    intro j
    induction j with
    | zero =>
      rw [Finset.sum_range_zero]
      have e : prefixRows n w 0 x = fun _ => false := by
        funext d; simp [prefixRows]
      rw [e, additive_zero hφ]
    | succ j ih =>
      rw [Finset.sum_range_succ, ih, ← hφ]
      congr 1
      funext d
      simp only [prefixRows, xorVec, rowMask, rowOf, xbits, d.2, dite_true]
      by_cases h1 : d.val / (n * w) < j
      · have h2 : ¬ d.val / (n * w) = j := by omega
        have h3 : d.val / (n * w) < j + 1 := by omega
        simp [h1, h2, h3]
      · by_cases h2 : d.val / (n * w) = j
        · have h3 : d.val / (n * w) < j + 1 := by omega
          simp [h2]
        · have h3 : ¬ d.val / (n * w) < j + 1 := by omega
          simp [h1, h2, h3]
  unfold rowSum
  rw [step n]
  congr 1
  funext d
  simp only [prefixRows]
  rw [ite_eq_left]
  have hd : d.val < n * (n * w) := lt_of_lt_of_eq d.2 (Nat.mul_assoc n n w)
  have hnw : 0 < n * w := by
    rcases Nat.eq_zero_or_pos (n * w) with h | h
    · rw [h, Nat.mul_zero] at hd; omega
    · exact h
  rw [Nat.div_lt_iff_lt_mul hnw]
  exact hd

theorem rowMask_xor {L : ℕ} (n w i : ℕ) (u v : ℕ → Bool) :
    rowMask (L := L) n w i (fun d => xor (u d) (v d)) = xorVec (rowMask n w i u) (rowMask n w i v) := by
  funext d
  simp only [rowMask, xorVec]
  split_ifs <;> simp

/-! ### Linear codes -/

/-- **Plain ⟹ no linear code on any set of co-entropy `O(n w)`.** Under `NoCode_TM`, for all
constants and all large `n`: no linear code solves complete exchange at the profile capacities on a
set `F` with `2^L ≤ 2^{C n w} |F|`. (Its correctness set is an XOR-closed set containing `F`, hence the
kernel of an additive syndrome map of `≤ C n w` bits, which is a row sum; then
`noCode_affine_of_noCode`.) -/
theorem noCode_linear_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, code.IsLinear → ¬ D.Solves n G (D.profileCap n G) F code := by
  classical
  obtain ⟨n₀, hn₀⟩ := noCode_affine_of_noCode h k G c C hG
  refine ⟨n₀, fun n hn D hD hT F hF code hlin hsol => ?_⟩
  set S : Set (Fin (n * n * entryBits n) → Bool) :=
    {x | D.Solves n G (D.profileCap n G) {x} code} with hSdef
  have hFS : F ⊆ S := fun x hx => (solves_iff_forall_singleton D).1 hsol x hx
  have hFne : F.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty, Nat.mul_zero] at hF
    exact absurd hF (Nat.not_le.2 (Nat.two_pow_pos _))
  obtain ⟨x₀, hx₀⟩ := hFne
  have hxor : ∀ x y, x ∈ S → y ∈ S → xorVec x y ∈ S := fun x y hx hy => correct_xor D hlin hx hy
  have h0 : (fun _ => false) ∈ S := by
    have := hxor x₀ x₀ (hFS hx₀) (hFS hx₀)
    have e : xorVec x₀ x₀ = fun _ => false := by funext d; simp [xorVec]
    rwa [e] at this
  have hcard : 2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * S.ncard :=
    le_trans hF (Nat.mul_le_mul_left _ (Set.ncard_le_ncard hFS (Set.toFinite _)))
  obtain ⟨s, φ, hs, hφ, hker⟩ := exists_syndrome S h0 hxor hcard
  have hs' : s ≤ C * (n * entryBits n) := by
    have : C * n * entryBits n = C * (n * entryBits n) := by ring
    omega
  have hgadd : ∀ i (u v : ℕ → Bool),
      (fun i u => φ (rowMask n (entryBits n) i u)) i (fun d => xor (u d) (v d)) =
        (fun i u => φ (rowMask n (entryBits n) i u)) i u +
        (fun i u => φ (rowMask n (entryBits n) i u)) i v := by
    intro i u v
    simp only
    rw [rowMask_xor, hφ]
  have hb : ∃ x₁ : Fin (n * n * entryBits n) → Bool,
      rowSum n (entryBits n) (fun i u => φ (rowMask n (entryBits n) i u)) x₁ = 0 :=
    ⟨fun _ => false, by rw [rowSum_additive hφ, additive_zero hφ]⟩
  apply hn₀ n hn D hD hT s hs' (fun i u => φ (rowMask n (entryBits n) i u)) hgadd 0 hb code
  rw [solves_iff_forall_singleton]
  intro x hx
  have hx' : rowSum n (entryBits n) (fun i u => φ (rowMask n (entryBits n) i u)) x = 0 := hx
  rw [rowSum_additive hφ] at hx'
  exact (hker x).1 hx'

end Transpose.Tape.Impl
