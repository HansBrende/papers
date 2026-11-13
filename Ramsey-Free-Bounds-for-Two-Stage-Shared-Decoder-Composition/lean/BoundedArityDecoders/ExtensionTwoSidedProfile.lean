import BoundedArityDecoders.SwapCodeAnswers

/-!
# Extension Result 3: Characteristic-Free Two-Sided Coarse–Fine Bound (`Problem 9.3`)

Formal statement specifications corresponding to **Result 3** (`Theorem 3` and its concrete
comparison against one-sided `Theorem TP`) in `extension.md`:

1. **Coarse–Fine Interval-Rotation Decomposition (`HasCoarseFineIntervalDecomposition`)**:
   * `cyclicRunEndpointCount` & `cyclicRunCount`: number of cyclic runs `m_S` of a subset
     `S ⊆ Fin d`.
   * `HasCoarseFineIntervalDecomposition`: side `M` uses fine intervals supported inside `S`
     (`|S| = s`, `m` cyclic runs), `c` pairwise-disjoint coarse cyclic intervals partitioning the
     complement `L = (Fin d) \ S`, and whole-cycle rotations.
   * `contiguousFineSet`, `contiguousCoarseComplement`, & `InContiguousCoarseFineSpan`: explicit
     two-scale instance with `s` contiguous fine singletons (`m = 1`) and `1` complementary coarse
     interval of length `d - s` (`c = 1`).

2. **`Theorem 3` (`Extension_Theorem3_TwoSidedCoarseFineSpec`)**:
   * Over **every** field `F` of **every** characteristic,
     `dim_F swapCode(A, B) ≤ (1/2) d^2 + (1/4) s_B(d - s_A) + (1/2) s_A s_B`
     `+ (1/2) c_B d + (1/4) c_A s_B + (1/2) s_B m_A + (1/4) m_B(d - s_A)`,
     and symmetrically with `A ↔ B` swapped.

3. **Concrete Win Over One-Sided `Theorem TP` (`Extension_Theorem3_ConcreteWinOverTPSpec`)**:
   * On the contiguous fine-singleton + one-coarse-interval family (`c_A = c_B = m_A = m_B = 1`,
     `s_A = α d`, `s_B = β d`), `Theorem 3` gives leading coefficient
     `1/2 + (1/4) min(β(1 + α), α(1 + β))`, which is **strictly smaller** than one-sided
     `Theorem TP`'s `1/2 + (1/2) min(α, β)` for every `α, β ∈ (0, 1)`.
   * At `α = β = 1/2` (`d = 2k`, `s_A = s_B = k`), `Theorem 3` gives `(11/16) d^2 + d`
     (`11/16 = 0.6875 < 3/4`), strictly below `(3/4) d^2` for all `d ≥ 17` (and strictly below
     one-sided `Theorem TP`'s `(3/4) d^2 + d/2` for all `d ≥ 10`, i.e. `k ≥ 5`).
-/

namespace BoundedArityDecoders

open Module
open scoped BigOperators

section CoarseFineDefs

/-- Number of cyclic run right-endpoints `|{r ∈ S : (r + 1) mod d ∉ S}|` of `S ⊆ Fin d`:
equals `0` when `S = ∅` or `S = univ`, and equals the number of maximal cyclic runs of `S`
whenever `∅ ⊂ S ⊂ univ`. -/
def cyclicRunEndpointCount {d : ℕ} [NeZero d] (S : Finset (Fin d)) : ℕ :=
  (S.filter fun r : Fin d =>
    (⟨(r.val + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) ∉ S).card

/-- Number of cyclic runs `m_S` of `S ⊆ Fin d`: `0` if `S = ∅`, `1` if `S = univ`, and the number
of maximal cyclic runs `cyclicRunEndpointCount S` when `∅ ⊂ S ⊂ univ`. -/
def cyclicRunCount {d : ℕ} [NeZero d] (S : Finset (Fin d)) : ℕ :=
  if S = Finset.univ then 1 else cyclicRunEndpointCount S

/-- Matrix family `M : α → Matrix (Fin d) (Fin d) F` admits a **coarse–fine cyclic-interval
decomposition** with fine union `S ⊆ Fin d` and `c` coarse intervals partitioning the complement
`L = Finset.univ \ S` if there exist `c` pairwise-disjoint nonempty cyclic intervals
`coarse : Fin c → Finset (Fin d)` whose union is `Finset.univ \ S` such that every `M a` lies in
the `F`-span of `{P_I σ^e}` over intervals/subsets `I ⊆ S`, coarse intervals `I = coarse i`, and
whole-cycle rotations `I = Finset.univ`. -/
def HasCoarseFineIntervalDecomposition {F : Type*} [Field F] {d : ℕ} [NeZero d] {α : Type*}
    (S : Finset (Fin d)) (c : ℕ) (M : α → Matrix (Fin d) (Fin d) F) : Prop :=
  ∃ coarse : Fin c → Finset (Fin d),
    (∀ i : Fin c, ∃ len : ℕ, 1 ≤ len ∧ len ≤ d ∧ IsCyclicInterval len (coarse i)) ∧
    Pairwise (fun i j : Fin c => Disjoint (coarse i) (coarse j)) ∧
    Finset.univ.biUnion coarse = Finset.univ \ S ∧
    ∀ a : α, M a ∈ Submodule.span F
      ({X | ∃ (I : Finset (Fin d)) (_hI : I ⊆ S) (e : Fin d),
          X = intervalMaskRotMatrix F I e} ∪
       {X | ∃ (i : Fin c) (e : Fin d),
          X = intervalMaskRotMatrix F (coarse i) e} ∪
       {X | ∃ e : Fin d,
          X = intervalMaskRotMatrix F Finset.univ e})

/-- Exact real-valued RHS of `Theorem 3` (prior to `A ↔ B` symmetrization):
`(1/2) d^2 + (1/4) s_B(d - s_A) + (1/2) s_A s_B + (1/2) c_B d + (1/4) c_A s_B + (1/2) s_B m_A + (1/4) m_B(d - s_A)`. -/
noncomputable def theorem3UnsymmetrizedBound (d sA mA cA sB mB cB : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (d : ℝ) ^ 2 +
    (1 / 4 : ℝ) * (sB : ℝ) * ((d : ℝ) - (sA : ℝ)) +
    (1 / 2 : ℝ) * (sA : ℝ) * (sB : ℝ) +
    (1 / 2 : ℝ) * (cB : ℝ) * (d : ℝ) +
    (1 / 4 : ℝ) * (cA : ℝ) * (sB : ℝ) +
    (1 / 2 : ℝ) * (sB : ℝ) * (mA : ℝ) +
    (1 / 4 : ℝ) * (mB : ℝ) * ((d : ℝ) - (sA : ℝ))

/-- Contiguous fine support `{0, 1, …, s - 1} ⊆ Fin d` (`1 ≤ s < d`, `m = 1` cyclic run). -/
def contiguousFineSet {d : ℕ} [NeZero d] (s : ℕ) : Finset (Fin d) :=
  (Finset.range s).image fun u => ⟨u % d, Nat.mod_lt _ (NeZero.pos d)⟩

/-- Complementary single coarse interval `{s, s + 1, …, d - 1} ⊆ Fin d` (`c = 1`). -/
def contiguousCoarseComplement {d : ℕ} [NeZero d] (s : ℕ) : Finset (Fin d) :=
  Finset.univ \ contiguousFineSet (d := d) s

/-- Concrete interval-rotation span generated by `s` contiguous fine singletons `{0}, …, {s - 1}`,
one complementary coarse interval `{s, …, d - 1}`, and whole-cycle rotations. -/
def InContiguousCoarseFineSpan {F : Type*} [Field F] {d : ℕ} [NeZero d] {α : Type*}
    (s : ℕ) (M : α → Matrix (Fin d) (Fin d) F) : Prop :=
  ∀ a : α, M a ∈ Submodule.span F
    ({X | ∃ (r : Fin d) (_hr : r ∈ contiguousFineSet (d := d) s) (e : Fin d),
        X = intervalMaskRotMatrix F {r} e} ∪
     {X | ∃ e : Fin d,
        X = intervalMaskRotMatrix F (contiguousCoarseComplement (d := d) s) e} ∪
     {X | ∃ e : Fin d,
        X = intervalMaskRotMatrix F Finset.univ e})

end CoarseFineDefs

/-! ### Statement Specifications for Result 3 -/

/-- **`Theorem 3` (Characteristic-Free Two-Sided Coarse–Fine Bound on `Problem 9.3`).**
Over **every** field `F` of **every** characteristic, for every `d ≥ 1`, finite index type `α`,
matrix families `A B : α → Matrix (Fin d) (Fin d) F`, fine subsets `S_A, S_B ⊆ Fin d`, and coarse
interval counts `c_A, c_B : ℕ`:
Whenever `HasCoarseFineIntervalDecomposition S_A c_A A` and
`HasCoarseFineIntervalDecomposition S_B c_B B` hold, `finrank F (SwapRigidity.swapCode A B)` is
bounded by both the `(A, B)` formula and the `A ↔ B` symmetrized minimum (with `m_A, m_B` given
both by `cyclicRunEndpointCount` and by `cyclicRunCount`). -/
def Extension_Theorem3_TwoSidedCoarseFineSpec : Prop :=
  ∀ (F : Type*) [Field F] (d : ℕ) [NeZero d] (α : Type*) [Fintype α]
    (S_A S_B : Finset (Fin d)) (c_A c_B : ℕ)
    (A B : α → Matrix (Fin d) (Fin d) F),
    HasCoarseFineIntervalDecomposition S_A c_A A →
    HasCoarseFineIntervalDecomposition S_B c_B B →
      let sA := S_A.card
      let sB := S_B.card
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
        min
          (theorem3UnsymmetrizedBound d sA (cyclicRunEndpointCount S_A) c_A
            sB (cyclicRunEndpointCount S_B) c_B)
          (theorem3UnsymmetrizedBound d sB (cyclicRunEndpointCount S_B) c_B
            sA (cyclicRunEndpointCount S_A) c_A) ∧
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
        min
          (theorem3UnsymmetrizedBound d sA (cyclicRunCount S_A) c_A
            sB (cyclicRunCount S_B) c_B)
          (theorem3UnsymmetrizedBound d sB (cyclicRunCount S_B) c_B
            sA (cyclicRunCount S_A) c_A)

/-- **Concrete Win of `Theorem 3` Over One-Sided `Theorem TP` (`Problem 9.3`).**
1. **Strict asymptotic coefficient improvement for all `α, β ∈ (0, 1)`**:
   `1/2 + (1/4) min(β(1 + α), α(1 + β)) < 1/2 + (1/2) min(α, β)`;
2. **Contiguous `s_A`-singleton + `1`-coarse-interval realization (`c_A = c_B = m_A = m_B = 1`)**:
   For any `1 ≤ s_A < d` and `1 ≤ s_B < d`, `InContiguousCoarseFineSpan` satisfies
   `HasCoarseFineIntervalDecomposition` with `|S_A| = s_A`, `cyclicRunCount S_A = 1`, `c_A = 1`
   (and similarly on `B`), giving
   `dim_F swapCode(A, B) ≤ (1/2 + (1/4) min(β(1 + α), α(1 + β))) d^2 + (5/4) d`
   (where `α = s_A / d`, `β = s_B / d`);
3. **Half-fine benchmark (`α = β = 1/2`, `d = 2k`, `s_A = s_B = k`, `k ≥ 1`)**:
   `theorem3UnsymmetrizedBound (2 * k) k 1 1 k 1 1 = (11 / 16) * (2 * k)^2 + (2 * k)`
   (with `11 / 16 = 0.6875 < 3 / 4`), so every `A, B` in `InContiguousCoarseFineSpan k` satisfies
   `finrank F (SwapRigidity.swapCode A B) ≤ (11 / 16) * d^2 + d`, which is strictly below
   `(3 / 4) * d^2` for all `d = 2k ≥ 18` (`k ≥ 9`, and `< (3/4) d^2` for every real `d > 16`). -/
def Extension_Theorem3_ConcreteWinOverTPSpec : Prop :=
  (∀ α β : ℝ, 0 < α → α < 1 → 0 < β → β < 1 →
    (1 / 2 : ℝ) + (1 / 4 : ℝ) * min (β * (1 + α)) (α * (1 + β)) <
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * min α β) ∧
  (∀ (F : Type*) [Field F] (d : ℕ) [NeZero d] (α : Type*) [Fintype α]
      (s_A s_B : ℕ) (_hsA : 1 ≤ s_A ∧ s_A < d) (_hsB : 1 ≤ s_B ∧ s_B < d)
      (A B : α → Matrix (Fin d) (Fin d) F),
    InContiguousCoarseFineSpan s_A A →
    InContiguousCoarseFineSpan s_B B →
      let αr : ℝ := (s_A : ℝ) / (d : ℝ)
      let βr : ℝ := (s_B : ℝ) / (d : ℝ)
      HasCoarseFineIntervalDecomposition (contiguousFineSet (d := d) s_A) 1 A ∧
      HasCoarseFineIntervalDecomposition (contiguousFineSet (d := d) s_B) 1 B ∧
      (contiguousFineSet (d := d) s_A).card = s_A ∧
      cyclicRunCount (contiguousFineSet (d := d) s_A) = 1 ∧
      (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
        ((1 / 2 : ℝ) + (1 / 4 : ℝ) * min (βr * (1 + αr)) (αr * (1 + βr))) * (d : ℝ) ^ 2 +
          (5 / 4 : ℝ) * (d : ℝ)) ∧
  ((11 / 16 : ℚ) < 3 / 4 ∧
    ∀ (k : ℕ) [NeZero k],
      let d := 2 * k
      haveI : NeZero d := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne k)⟩
      theorem3UnsymmetrizedBound d k 1 1 k 1 1 = (11 / 16 : ℝ) * (d : ℝ) ^ 2 + (d : ℝ) ∧
      (9 ≤ k → (11 / 16 : ℝ) * (d : ℝ) ^ 2 + (d : ℝ) < (3 / 4 : ℝ) * (d : ℝ) ^ 2) ∧
      (∀ (F : Type*) [Field F] (α : Type*) [Fintype α]
          (A B : α → Matrix (Fin d) (Fin d) F),
        InContiguousCoarseFineSpan k A →
        InContiguousCoarseFineSpan k B →
          (finrank F (SwapRigidity.swapCode A B) : ℝ) ≤
            (11 / 16 : ℝ) * (d : ℝ) ^ 2 + (d : ℝ)))

end BoundedArityDecoders
