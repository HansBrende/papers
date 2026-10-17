import Transpose.Tape.PlainRobust.CESyndrome
import Transpose.Tape.PlainRobust.CEConcat
import Transpose.Tape.PlainRobust.CENonlin
import Transpose.Tape.PlainRobust.CEDecomp
import Transpose.Tape.PlainRobust.CEColCover

/-!
# Partial results towards "plain implies robust" for the Tape Coding Conjecture

The Tape Coding Conjecture, in its no-code form `RobustNoCode_TM`, rules out codes for complete
exchange on every set of inputs of co-entropy `≤ C n w` (the robust form). Its plain form
`NoCode_TM` rules out codes that are correct on all inputs. Whether the plain form implies the
robust form is open; this file collects partial results.

Every statement below assumes `NoCode_TM` and rules out codes on a special class of sets, or codes of
a special shape:
* sets covered by an additive or network-computed hint with `O(1)` candidate shifts, and affine sets
  (prefix sweep: `CEPrefix`; selection: `CESelectNet`, `CESelect`; concatenation: `CEConcatNet`,
  `CEConcat`);
* sets missing few inputs (voting: `CEVote`);
* linear codes, codes linear outside few bits or with few correction patterns (`CELinear`,
  `CENonlin`);
* zero sets of bounded-degree functions (`CEDegree`), sets containing every input supported on one
  class of an `O(1)`-colouring (`CEDecomp`), sets covered by `O(1)` column-keeping row maps, e.g. the
  zero sets of uniform column aggregates (duplication: `CEColCover`);
* codes within capacity whose error vectors take few values, e.g. `O(n)` wrong entries
  (syndrome correction: `CESyndrome`).

Each statement is proved by the `Impl` theorem of the same name, in the proof files named above
(`Transpose/Tape/PlainRobust/`, namespace `Transpose.Tape.Impl`); the statements are in the
namespace `Transpose.Tape.PlainRobust`. The definitions (`NoCode_TM`, `RobustNoCode_TM`,
`TSDiagram`, `NetCode`, `profileCap`) are in `DefsCE.lean`. The forms of the conjecture (including
its hint and co-entropy forms) and its consequences for linear-time transposition are in
`Statements/Coding.lean`.
-/

namespace Transpose.Tape.PlainRobust

open Transpose TSDiagram

/-! ### Affine sets, voting, linear codes, selection, degree and decomposition -/

/-- **Plain ⟹ no code on any set that an additive hint covers.** Under `NoCode_TM`, for all
constants and all large `n`: no code solves complete exchange at the profile capacities on a set `F`
for which a row-additive hint `Σ_i g_i(row i)` of `s ≤ C n w` bits and a shift table `z` put every
input into `F`. (Prepend an input sweep that computes the hint along the spine; the original part
runs the code shifted by `z(hint)`.) -/
theorem noCode_additive_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2))
        (z : (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool)),
        (∀ x, Impl.xorVec x (z (Impl.rowSum n (entryBits n) g x)) ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_additive_of_noCode h k G c C hG

/-- **Plain ⟹ no code on affine sets.** Under `NoCode_TM`, for all constants and all large `n`: no
code solves complete exchange at the profile capacities on a nonempty affine set
`{x | Σ_i g_i(row i of x) = b}` of codimension `s ≤ C n w` (additive row maps; every affine subspace
of codimension `≤ C n w` has this form). This is `RobustNoCode_TM` for affine `F`. -/
theorem noCode_affine_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)),
        (∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) →
      ∀ (b : Fin s → ZMod 2),
        (∃ x₀ : Fin (n * n * entryBits n) → Bool, Impl.rowSum n (entryBits n) g x₀ = b) →
      ∀ code : NetCode,
        ¬ D.Solves n G (D.profileCap n G) {x | Impl.rowSum n (entryBits n) g x = b} code :=
  Impl.noCode_affine_of_noCode h k G c C hG

/-- **Plain ⟹ no code on any set containing a nonempty affine set of codimension `≤ C n w`.** -/
theorem noCode_of_affine_subset (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)),
        (∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) →
      ∀ (b : Fin s → ZMod 2),
        (∃ x₀ : Fin (n * n * entryBits n) → Bool, Impl.rowSum n (entryBits n) g x₀ = b) →
        {x | Impl.rowSum n (entryBits n) g x = b} ⊆ F →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_of_affine_subset h k G c C hG

/-- **Plain ⟹ no code that fails on fewer than about `2^{L/2}` inputs.** Under `NoCode_TM`, for all
constants and all large `n`: no code solves complete exchange at the profile capacities on a set `F`
whose complement satisfies `2 |F^c|² < 2^L`. (Three shifted copies with shifts `0, z₁, z₂`,
`z_i ⊕ z_j ∉ F^c ⊕ F^c`, run side by side on tripled walks; every output is a majority vote.) -/
theorem noCode_cosmall_of_noCode (h : NoCode_TM) (k G c : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)), 2 * (Fᶜ).ncard ^ 2 < 2 ^ (n * n * entryBits n) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_cosmall_of_noCode h k G c hG

/-- **Plain ⟹ no code on an affine set with sparse exceptions.** Under `NoCode_TM`, for all constants
and all large `n`: no code solves complete exchange at the profile capacities on a set `F` containing
a nonempty affine set `A` of codimension `s ≤ C n w`, except for a set `E` with
`2^s · 2 |E|² < 2^L`. (Voting with three shifts in the kernel gives a code on all of `A`.) -/
theorem noCode_affine_exc_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2)),
        (∀ i (u v : ℕ → Bool), g i (fun d => xor (u d) (v d)) = g i u + g i v) →
      ∀ (b : Fin s → ZMod 2),
        (∃ x₀ : Fin (n * n * entryBits n) → Bool, Impl.rowSum n (entryBits n) g x₀ = b) →
      ∀ (E : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ s * (2 * E.ncard ^ 2) < 2 ^ (n * n * entryBits n) →
        {x | Impl.rowSum n (entryBits n) g x = b} \ E ⊆ F →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_affine_exc_of_noCode h k G c C hG

/-- **Plain ⟹ robust for linear codes.** Under `NoCode_TM`, for all constants and all large `n`: no
`F₂`-linear code (`NetCode.IsLinear`: XOR-ing inputs XORs all values) solves complete exchange at the
profile capacities on any set `F` of co-entropy `≤ C n w`. Its correctness set is closed under XOR,
so it is the kernel of an additive syndrome map of `≤ C n w` bits; then `noCode_affine_of_noCode`.
So any counterexample to plain ⟹ robust uses a nonlinear code. -/
theorem noCode_linear_of_noCode (h : NoCode_TM) (k G c C : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ code : NetCode, code.IsLinear → ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_linear_of_noCode h k G c C hG

/-- **Plain ⟹ robust for codes that are linear outside `O(n w)` bits.** Under `NoCode_TM`, for all
constants and all large `n`: no code that is linear outside a set `E_N` of edges of total profile
capacity `≤ H n w` (`NetCode.IsLinearExcept`: every decoder and the encoder of every other edge is
XOR-linear) solves complete exchange at the profile capacities on a set `F` of co-entropy `≤ C n w`.
(The values on `E_N` are an internally computed hint of `≤ H n w` bits. By pigeonhole, a
`2^{-H n w}` fraction of `F` shares them; XOR-ing these inputs with one of them gives inputs on which
the code with `0` on `E_N`, masked to the capacities, is correct; that code is linear, so
`noCode_linear_of_noCode` applies.) -/
theorem noCode_linearExcept_of_noCode (h : NoCode_TM) (k G c C H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ (code : NetCode) (EN : Finset (ℕ × ℕ)), code.IsLinearExcept EN →
        ∑ e ∈ EN, D.profileCap n G e ≤ H * n * entryBits n →
        ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_linearExcept_of_noCode h k G c C H hG

/-- **Plain ⟹ no linear code with `O(n w)` nonlinear correction bits.** Under `NoCode_TM`, for all
constants and all large `n`: no code that is linear plus corrections (`NetCode.IsLinearPlus code nl`:
`enc ⊕ nl` is XOR-linear on every edge, and every decoder is XOR-linear) with `nl e < 2^{b e}` on every
edge and `Σ_e b e ≤ H n w` over the edges of the diagram solves complete exchange at the profile
capacities on a set of co-entropy `≤ C n w`. The corrections may sit on every edge, for example `O(w)`
nonlinear bits per node. (They are an internally computed hint; pigeonhole, then
`noCode_linear_of_noCode`, as in `noCode_linearExcept_of_noCode`.) The corrections must occupy the
low `b e` bits of each value (by a fixed permutation of each edge's bits this is no restriction), and
the decoders must be exactly linear. -/
theorem noCode_linearPlus_of_noCode (h : NoCode_TM) (k G c C H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ (code : NetCode) (nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (b : ℕ × ℕ → ℕ),
        code.IsLinearPlus nl → (∀ e f v, nl e f v < 2 ^ b e) →
        ∑ e ∈ D.edges (blockSize G n), b e ≤ H * n * entryBits n →
        ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_linearPlus_of_noCode h k G c C H hG

/-- **Plain ⟹ no linear code whose corrections take few values.** Under `NoCode_TM`, for all
constants and all large `n`: no code that is linear plus corrections `nl` (`NetCode.IsLinearPlus`),
whose correction vector on the edges of the diagram takes values in a set `Tv` of at most `2^{H n w}`
vectors on `F`, solves complete exchange at the profile capacities on a set `F` of co-entropy
`≤ C n w`. The corrections may be wide, as long as they have few patterns on `F` (for example, any
functions of `O(1)` rows). This generalizes `noCode_linearPlus_of_noCode`. -/
theorem noCode_linearPlusImage_of_noCode (h : NoCode_TM) (k G c C H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        2 ^ (n * n * entryBits n) ≤ 2 ^ (C * n * entryBits n) * F.ncard →
      ∀ (code : NetCode) (nl : ℕ × ℕ → (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ),
        code.IsLinearPlus nl →
        ∀ (Tv : Finset (ℕ × ℕ → ℕ)), Tv.card ≤ 2 ^ (H * n * entryBits n) →
        (∀ x ∈ F, (fun e => if e ∈ D.edges (blockSize G n) then
            nl e (code.inVals (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x) e.1)
              (D.visible n (entryBits n) (blockSize G n) e.1 x) else 0) ∈ Tv) →
        ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_linearPlusImage_of_noCode h k G c C H hG

/-- **Plain ⟹ no code on any set containing the zero set of a bounded-degree function.** (Such zero
sets have co-entropy `≤ D`.) Under `NoCode_TM`, for every constant `D` and all large `n`: no code
solves complete exchange at the profile capacities on a set `F` containing `{x | f x = false}`, for
any `f` of degree `≤ D` over `F₂` (`Impl.DegLE f D`: every discrete derivative of order `D + 1`
vanishes) that is not identically `true`. (A top-order derivative is constant `1`, so the `2^D`
values on a cube of translates are not all `true`: the zero set is covered by `2^D` fixed
translates, and selection runs the `2^D` shifted codes.) -/
theorem noCode_lowDegree_of_noCode (h : NoCode_TM) (k G c D : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (Dg : TSDiagram k), Dg.Valid (n * n * entryBits n) → Dg.T ≤ c * (n * n * entryBits n) →
      ∀ (f : (Fin (n * n * entryBits n) → Bool) → Bool), Impl.DegLE f D → (∃ x, f x = false) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)), {x | f x = false} ⊆ F →
      ∀ code : NetCode, ¬ Dg.Solves n G (Dg.profileCap n G) F code :=
  Impl.noCode_lowDegree_of_noCode h k G c D hG

/-- **Plain ⟹ no code on the zero set of a quadratic form.** Under `NoCode_TM`, for all constants and
all large `n`: no code solves complete exchange at the profile capacities on a set containing
`{x | ⊕_{(p, q) ∈ Q} x_p x_q = 0}`, for any set `Q` of pairs of input positions. For example, with `Q`
the pairs of equal bits of transposed entries `(i, j)`, `(j, i)` with `i < j`, the zero set is
`Σ_{i<j} ⟨x_ij, x_ji⟩ = 0`, a constraint coupling `x` with `xᵀ`. -/
theorem noCode_quadForm_of_noCode (h : NoCode_TM) (k G c : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (Dg : TSDiagram k), Dg.Valid (n * n * entryBits n) → Dg.T ≤ c * (n * n * entryBits n) →
      ∀ (Q : Finset (Fin (n * n * entryBits n) × Fin (n * n * entryBits n)))
        (F : Set (Fin (n * n * entryBits n) → Bool)),
        {x | Q.fold xor false (fun pq => x pq.1 && x pq.2) = false} ⊆ F →
      ∀ code : NetCode, ¬ Dg.Solves n G (Dg.profileCap n G) F code :=
  Impl.noCode_quadForm_of_noCode h k G c hG

/-- **Plain ⟹ no code on a set containing every input supported on a single part.** Under
`NoCode_TM`, for every constant `K` and all large `n`: let `P` colour the input positions with colours
`< K`, and let `F` contain every input that vanishes outside one colour class. Then no code solves
complete exchange at the profile capacities on `F`. (The walks are taken `K` times, and copy `j` of the
code runs on the input masked to class `j`, which lies in `F`. Transposition is linear, so the XOR of
the copies' outputs is the transpose.) -/
theorem noCode_decomp_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (P : ℕ → ℕ), (∀ d < n * n * entryBits n, P d < K) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        (∀ j < K, ∀ x : Fin (n * n * entryBits n) → Bool,
          (∀ d : Fin (n * n * entryBits n), P d ≠ j → x d = false) → x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_decomp_of_noCode h k G c K hG hK

/-- **Plain ⟹ no code on the common zero set of quadratic forms whose monomials cross a fixed
partition.** Under `NoCode_TM`, for every constant `K` and all large `n`: let `P` colour the input
positions with `K` colours, and let every monomial `x_p x_q` of every form in a family `𝒬` join two
colours. Then no code solves complete exchange at the profile capacities on a set containing the
common zero set. Example, with `K = 2` and the colour classes "upper triangle with the diagonal" and
"strictly lower triangle": any family of constraints `Σ_{i<j} ⟨A_{k,ij} x_ij, x_ji⟩ = 0` with
pair-dependent matrices, so `Θ(n w)` independent ones, which couple `x` with `xᵀ`. (With one matrix
per constraint the family spans at most `w²` forms.) The sets in this and in `noCode_decomp_of_noCode`
are specially shaped; their co-entropy may be far above `C n w`, so these are not the `O(n w)` cases
of `RobustNoCode_TM` as such. -/
theorem noCode_crossQuad_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (P : ℕ → ℕ), (∀ d < n * n * entryBits n, P d < K) →
      ∀ (𝒬 : Finset (Finset (Fin (n * n * entryBits n) × Fin (n * n * entryBits n)))),
        (∀ Q ∈ 𝒬, ∀ pq ∈ Q, P pq.1 ≠ P pq.2) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        {x | ∀ Q ∈ 𝒬, Q.fold xor false (fun pq => x pq.1 && x pq.2) = false} ⊆ F →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_crossQuad_of_noCode h k G c K hG hK

/-- **Plain ⟹ no code with a constant-size oracle hint.** Under `NoCode_TM`, for every constant `s₀`:
for all constants and all large `n`, no family of codes indexed by an `s₀`-bit oracle hint (any
function of the whole input) solves complete exchange on every input at the profile capacities.
(*Selection*: the `2^{s₀}` candidate codes run side by side; for each pair, the spine records a
position where their outputs differ; an input sweep fetches the true bits there; a candidate that
never loses runs again and emits the output. A correct candidate never loses, and every incorrect
one loses against it.) -/
theorem noCode_hintConst_of_noCode (h : NoCode_TM) (s₀ : ℕ) : NoCode_TM_hintBits (fun _ => s₀) :=
  Impl.noCode_hintConst_of_noCode h s₀

/-- **A constant-size oracle hint does not change the plain form**: `NoCode_TM` is equivalent to
"no code even with an `s₀`-bit oracle hint", for every constant `s₀` (the converse takes the hint `0`).
So the hint ladder only becomes open at `ω(1)` hint bits. -/
theorem noCode_iff_hintConst (s₀ : ℕ) : NoCode_TM ↔ NoCode_TM_hintBits (fun _ => s₀) :=
  Impl.noCode_iff_hintConst s₀

/-- **Plain ⟹ no code on any set covered by an additive hint and `K` candidate shifts.** Under
`NoCode_TM`, for all constants and all large `n`: no code solves complete exchange at the profile
capacities on a set `F` for which a row-additive hint `Σ_i g_i(row i)` of `s ≤ C n w` bits and `K`
shift tables `z_0, …, z_{K-1}` put every input into `F` with at least one of the shifts. This
combines `noCode_additive_of_noCode` (`K = 1`) with selection. Examples (argued informally, not
formalized): with `s = 0`, the zero set of any polynomial of `F₂`-degree `d` (the `2^d` translates by
the subcube on the variables of a top-degree monomial; the `d`-th discrete derivative there is `1`);
with a syndrome hint, an affine set of codimension `≤ C n w` intersected with such a zero set. -/
theorem noCode_additiveCover_of_noCode (h : NoCode_TM) (k G c C K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)) (s : ℕ), s ≤ C * (n * entryBits n) →
      ∀ (g : ℕ → (ℕ → Bool) → (Fin s → ZMod 2))
        (z : ℕ → (Fin s → ZMod 2) → (Fin (n * n * entryBits n) → Bool)),
        (∀ x, ∃ j < K, Impl.xorVec x (z j (Impl.rowSum n (entryBits n) g x)) ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_additiveCover_of_noCode h k G c C K hG hK

/-- **Plain ⟹ no code on any set with a network-computable `O(1)`-candidate cover.** Under
`NoCode_TM`, for all constants and all large `n`: no code solves complete exchange at the profile
capacities on a set `F` for which some *hint computation* and `K` shift tables put every input into
`F` with one of the shifts. A hint computation is a diagram `Pre` on `k₁` tapes (walks from cell `0`
with unit steps, `1 ≤ T ≤ c₁ L`), a code `C₁` within `Pre`'s profile capacities on every input, and a
map `hx` reading an `s`-bit hint (`s ≤ C n w`) off the values into `Pre`'s last node and its visible
input. (`Pre` runs on its own tapes, the input head returns to cell `0`, the hint travels along the
spine, and the `K` hinted codes are the candidates of a selection.) This is the general form of the
hint method; `noCode_additiveCover_of_noCode` is, in spirit (not derived in Lean), the case of an
additive hint computed by a sweep. It does not contain `noCode_hintConst_of_noCode`, whose candidates
are arbitrary codes rather than shifts of one code. -/
theorem noCode_netCover_of_noCode (h : NoCode_TM) (k G c C K k₁ c₁ : ℕ) (hG : 1 ≤ G)
    (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (Pre : TSDiagram k₁),
        ((∀ t, Pre.work t 0 = 0 ∧ UnitSteps (Pre.work t)) ∧ Pre.inp 0 = 0 ∧ UnitSteps Pre.inp) →
        1 ≤ Pre.T → Pre.T ≤ c₁ * (n * n * entryBits n) →
      ∀ (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (s : ℕ), s ≤ C * (n * entryBits n) →
      (∀ (x : Fin (n * n * entryBits n) → Bool), ∀ e ∈ Pre.edges (blockSize G n),
        C₁.edgeVal (Pre.edges (blockSize G n))
          (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ Pre.profileCap n G e) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool))
        (z : ℕ → ℕ → (Fin (n * n * entryBits n) → Bool)),
        (∀ x, ∃ j < K, Impl.xorVec x (z j (hx (C₁.inVals (Pre.edges (blockSize G n))
          (fun y => Pre.visible n (entryBits n) (blockSize G n) y x)
            (Pre.nodes (blockSize G n) - 1))
          (Pre.visible n (entryBits n) (blockSize G n) (Pre.nodes (blockSize G n) - 1) x) %
            2 ^ s)) ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_netCover_of_noCode h k G c C K k₁ c₁ hG hK

/-- **Plain ⟹ network-computable hints are free.** Under `NoCode_TM`: for all constants and all
large `n`, no family of codes `codes h` (arbitrary, one per hint value) solves complete exchange on
every input at the profile capacities when input `x` uses the code indexed by a *network-computable*
hint of `s ≤ C n w` bits (a hint computation `Pre`, `C₁`, `hx` as in `noCode_netCover_of_noCode`).
With an *oracle* hint, any function of the whole input, the same statement is `RobustNoCode_TM`
(`robustNoCode_iff_hint`). So the difference between the plain and the robust form is exactly
"oracle hint versus network-computed hint". -/
theorem noCode_netHint_of_noCode (h : NoCode_TM) (k G c C k₁ c₁ : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (Pre : TSDiagram k₁),
        ((∀ t, Pre.work t 0 = 0 ∧ UnitSteps (Pre.work t)) ∧ Pre.inp 0 = 0 ∧ UnitSteps Pre.inp) →
        1 ≤ Pre.T → Pre.T ≤ c₁ * (n * n * entryBits n) →
      ∀ (C₁ : NetCode) (hx : (ℕ × ℕ → ℕ) → (ℕ → Bool) → ℕ) (s : ℕ), s ≤ C * (n * entryBits n) →
      (∀ (x : Fin (n * n * entryBits n) → Bool), ∀ e ∈ Pre.edges (blockSize G n),
        C₁.edgeVal (Pre.edges (blockSize G n))
          (fun y => Pre.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ Pre.profileCap n G e) →
      ∀ (codes : ℕ → NetCode),
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, D.Solves n G (D.profileCap n G) {x}
          (codes (hx (C₁.inVals (Pre.edges (blockSize G n))
            (fun y => Pre.visible n (entryBits n) (blockSize G n) y x)
              (Pre.nodes (blockSize G n) - 1))
            (Pre.visible n (entryBits n) (blockSize G n) (Pre.nodes (blockSize G n) - 1) x) %
              2 ^ s)) :=
  Impl.noCode_netHint_of_noCode h k G c C k₁ c₁ hG

/-! ### Plain ⟹ no code with few error patterns -/

/-- **Plain ⟹ every code within capacity has many error patterns.** Under `NoCode_TM`, for all
constants and all large `n`: let a code stay within the profile capacities of `D` on every input.
Then its *error vectors* take more than `2^{H n w}` values. (Bit `d` of the error vector of `x` is the
output bit at the transposed position `tpos d` XOR the input bit `d`.) This generalizes `NoCode_TM`,
which is the case of the single error vector `0`. *Syndrome correction*: run the code once and add
the syndromes of its output bits along the spine (`2 H n w + 1` parity checks, carried by `2 H + 1`
stationary tapes); an input sweep adds the syndrome of `x`, giving the syndrome of the error vector;
a second run XORs every output bit with the error vector decoded from it. A random check matrix
separates `2^{H n w}` vectors. -/
theorem noCode_fewErrors_of_noCode (h : NoCode_TM) (k G c H : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (code : NetCode),
        (∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          code.edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
      ∀ (V : Finset (Fin (n * n * entryBits n) → Bool)), V.card ≤ 2 ^ (H * n * entryBits n) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, (fun d : Fin (n * n * entryBits n) => xor
            (code.outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d))
            (x d)) ∈ V :=
  Impl.noCode_fewErrors_of_noCode h k G c H hG

/-- **Plain ⟹ transposition with `O(n)` wrong bits is as hard as exact.** Under `NoCode_TM`, for
all constants and all large `n`: no code within the profile capacities on every input gets all but
at most `A n` of the `n² w` output bits right on every input. ("Approximate" here means `O(n)` wrong
bits, not a constant fraction. Error vectors with at most `A n` ones number at most
`(L + 1)^{A n} ≤ 2^{4 A n w}`; then `noCode_fewErrors_of_noCode`.) -/
theorem noCode_sparseErrors_of_noCode (h : NoCode_TM) (k G c A : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (code : NetCode),
        (∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          code.edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, (Finset.univ.filter
            (fun d : Fin (n * n * entryBits n) =>
            code.outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) ≠
            x d)).card ≤ A * n :=
  Impl.noCode_sparseErrors_of_noCode h k G c A hG

/-- **Plain ⟹ transposition with `O(n)` wrong entries is as hard as exact.** Under `NoCode_TM`, for
all constants and all large `n`: no code within the profile capacities on every input gets all but
at most `A n` of the `n²` matrix entries right on every input. An entry counts as wrong if any of its
`w` bits is; the count is the number of distinct entries `d / w` over the wrong positions `d`. This
strengthens `noCode_sparseErrors_of_noCode` from `O(n)` wrong bits to `O(n)` wrong entries, i.e. up
to `O(n w)` wrong bits confined to `O(n)` entries. (There are at most
`(L + 1)^{A n} 2^{w A n} ≤ 2^{5 A n w}` such error vectors.) -/
theorem noCode_sparseEntryErrors_of_noCode (h : NoCode_TM) (k G c A : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (code : NetCode),
        (∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          code.edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, ((Finset.univ.filter
            (fun d : Fin (n * n * entryBits n) =>
            code.outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d) ≠
            x d)).image (fun d : Fin (n * n * entryBits n) => (d : ℕ) / entryBits n)).card ≤
          A * n :=
  Impl.noCode_sparseEntryErrors_of_noCode h k G c A hG

/-- **Plain ⟹ no `O(1)` codes with few error patterns cover the inputs.** Under `NoCode_TM`, for all
constants and all large `n`: let `K` codes stay within the profile capacities of `D` on every input,
and let `V` be a set of at most `2^{H n w}` vectors. Then some input has none of its `K` error vectors
in `V`. Which code serves which input may be any function of the input (a constant-size oracle hint).
This contains `noCode_fewErrors_of_noCode` (`K = 1`) and, for codes within capacity on every input,
the constant-hint result (`V = {0}`). Construction: the syndrome-corrected codes are the candidates
of a selection. -/
theorem noCode_fewErrorsCover_of_noCode (h : NoCode_TM) (k G c H K : ℕ) (hG : 1 ≤ G)
    (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (codes : ℕ → NetCode),
        (∀ j < K, ∀ x : Fin (n * n * entryBits n) → Bool, ∀ e ∈ D.edges (blockSize G n),
          (codes j).edgeVal (D.edges (blockSize G n))
            (fun y => D.visible n (entryBits n) (blockSize G n) y x) e < 2 ^ D.profileCap n G e) →
      ∀ (V : Finset (Fin (n * n * entryBits n) → Bool)), V.card ≤ 2 ^ (H * n * entryBits n) →
        ¬ ∀ x : Fin (n * n * entryBits n) → Bool, ∃ j < K,
          (fun d : Fin (n * n * entryBits n) => xor
            ((codes j).outVal (D.edges (blockSize G n))
              (fun y => D.visible n (entryBits n) (blockSize G n) y x)
              (D.outNode (blockSize G n) (tpos n (entryBits n) d)) (tpos n (entryBits n) d))
            (x d)) ∈ V :=
  Impl.noCode_fewErrorsCover_of_noCode h k G c H K hG hK

/-! ### Column covers and duplication -/

/-- **Plain ⟹ no code on a set covered by `K` locally computable column-keeping maps.** Under
`NoCode_TM`, for every constant `K` and all large `n`: let `cls` give each column a class `< K`, and
let input maps `Φ κ` be locally computable (`τ κ u` turns the visible input of node `u` on `x` into
that on `Φ κ x`) and keep the input columns of class `κ`. Then no code solves complete exchange at
the profile capacities on a set containing every `Φ κ x`. (`K` copies side by side; output column
`j` is read from copy `cls j`. This generalizes the column-respecting case of `noCode_decomp_of_noCode`;
with an arbitrary colouring of positions, that theorem XORs the outputs and is not a special case.) -/
theorem noCode_colCover_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cls : ℕ → ℕ), (∀ j < n, cls j < K) →
      ∀ (Φ : ℕ → (Fin (n * n * entryBits n) → Bool) → (Fin (n * n * entryBits n) → Bool))
        (τ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool),
        (∀ κ < K, ∀ x u, τ κ u (D.visible n (entryBits n) (blockSize G n) u x) =
          D.visible n (entryBits n) (blockSize G n) u (Φ κ x)) →
        (∀ x (d : Fin (n * n * entryBits n)), Φ (cls ((d : ℕ) / entryBits n % n)) x d = x d) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)), (∀ κ < K, ∀ x, Φ κ x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_colCover_of_noCode h k G c K hG hK

/-- **Plain ⟹ no code on a set covered by `K` column-keeping row maps.** As
`noCode_colCover_of_noCode`, with `Φ κ = applyRows (ψ κ)`: the row map `ψ κ` (applied to every row)
must keep, within each row, the positions of the columns of class `κ`. Row maps are automatically
locally computable, since a node sees whole rows. -/
theorem noCode_rowMapCover_of_noCode (h : NoCode_TM) (k G c K : ℕ) (hG : 1 ≤ G) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (cls : ℕ → ℕ), (∀ j < n, cls j < K) →
      ∀ (ψ : ℕ → ℕ → (ℕ → Bool) → ℕ → Bool),
        (∀ κ i (ρ : ℕ → Bool) p, p < n * entryBits n → cls (p / entryBits n) = κ →
          ψ κ i ρ p = ρ p) →
      ∀ (F : Set (Fin (n * n * entryBits n) → Bool)),
        (∀ κ < K, ∀ x, Impl.applyRows n (entryBits n) (ψ κ) x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_rowMapCover_of_noCode h k G c K hG hK

/-- **Plain ⟹ no code on the zero set of a uniform column aggregate (duplication).** Under
`NoCode_TM`, for all large even `n`: no code solves complete exchange at the profile capacities on a
set containing `{x : Σ_j v(column j of x) = 0}`, for any `v` (the same for every column) with values
in `GF(2)^m`, any `m`: any number of such constraints, of any degree. The inputs
`[x_left | x_left]` and `[x_right | x_right]` lie in the zero set, since each term appears twice,
and two copies, reading each output column from the copy that keeps it, transpose every input. Two
special cases also follow from other results of this file: a linear `v` gives an affine set
(`noCode_of_affine_subset`), and `O(1)` constraints of bounded degree fall to
`noCode_lowDegree_of_noCode`. Nonlinear, high-degree aggregates with many constraints are not
covered by those results. -/
theorem noCode_colAggregate_of_noCode (h : NoCode_TM) (k G c : ℕ) (hG : 1 ≤ G) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Even n →
      ∀ (D : TSDiagram k), D.Valid (n * n * entryBits n) → D.T ≤ c * (n * n * entryBits n) →
      ∀ (m : ℕ) (v : (ℕ → Bool) → (Fin m → ZMod 2)) (F : Set (Fin (n * n * entryBits n) → Bool)),
        (∀ x, ∑ j ∈ Finset.range n, v (Impl.colBits n (entryBits n) x j) = 0 → x ∈ F) →
      ∀ code : NetCode, ¬ D.Solves n G (D.profileCap n G) F code :=
  Impl.noCode_colAggregate_of_noCode h k G c hG

end Transpose.Tape.PlainRobust
