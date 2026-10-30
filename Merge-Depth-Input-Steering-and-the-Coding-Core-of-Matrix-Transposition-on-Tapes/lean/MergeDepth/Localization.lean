import MergeDepth.InputSteering
import MergeDepth.HCStarQ91

/-!
# Theorem L (localization), given binary [Q9.1]

Let `M` be a machine with `k` work tapes, `c > 0`, and let `𝒟` be a set of dimensions `d` at which
`M` transposes all `d × d` matrices with `b(d)`-bit entries within `c (L + 1)` steps (the frozen
`TransposesAt`), `L = d² b(d)`. Each part holds at all `d ∈ 𝒟` from a threshold that depends only on
the parameters named in it. (The paper takes `𝒟` infinite; the statements below hold for every
set `𝒟`, and are vacuous when it is finite.)

* `thm_L_a`: **(a) revisits**, from Corollary RV. For every `V ≥ 1`, on some input some cell of the
  input tape or of a work tape is entered more than `V` times before the halting time.
* `thm_L_b`: **(b) input steering**, from Corollary IS. For all `V, w ≥ 1` and `η > 0`: if on every
  input every work-tape cell is entered at most `V` times, then `H(σ^in_w(X)) > (1/2 - η) L`.
* `thm_L_c`: **(c) merge depth**, from Corollary HC* (`cor_HCstar_uniform_frozen`). For `V`, `s`,
  a depth bound `D`, `β ≥ β(M)` and `ε, η` with `ε + η < 1/2`: if `M` is oblivious at length `L`
  (`ObliviousOn`), then for every pruning of its field DAG, every cold genie at `(V, ε)` of depth
  `D` and every lineage assignment for it, more than `η L` output positions have a genie-free path
  from their output node with more than `s` deep merges.
-/

namespace MergeDepth

open Finset BoundedNesting Transpose

set_option autoImplicit false

open Classical in
/-- **Theorem L(a), revisits, given binary [Q9.1].** -/
theorem thm_L_a (hQ : Q91Binary) {M : TM} (hk : 1 ≤ M.k) {c : ℝ} (hc : 0 < c) (𝒟 : Set ℕ)
    (h𝒟 : ∀ d ∈ 𝒟, TransposesAt M d c) (V : ℕ) (hV : 1 ≤ V) :
    ∃ d₀ : ℕ, ∀ d ∈ 𝒟, d₀ ≤ d → ∃ (X : Fin (d * d * entryBits d) → Bool) (T : ℕ),
      Transpose.Tape.HaltsAt M (List.ofFn X) T ∧
        ((∃ cell, V < (entries (inPosW M X) cell (T - 1)).card) ∨
          ∃ j cell, V < (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card) := by
  obtain ⟨d₀, hd₀⟩ := cor_RV hQ hk hV hc
  refine ⟨d₀, fun d hd hdd => ?_⟩
  have htr := fun X => (h𝒟 d hd).transposesInput X
  by_contra hno
  push Not at hno
  exact hd₀ d hdd (entryBits d) (one_le_entryBits d) htr
    (fun X T hT cell => (hno X T hT).1 cell) (fun X T hT j cell => (hno X T hT).2 j cell)

open Classical in
/-- **Theorem L(b), input steering, given binary [Q9.1].** -/
theorem thm_L_b (hQ : Q91Binary) {M : TM} (hk : 1 ≤ M.k) {c : ℝ} (hc : 0 < c) (𝒟 : Set ℕ)
    (h𝒟 : ∀ d ∈ 𝒟, TransposesAt M d c) (V w : ℕ) (hV : 1 ≤ V) (hw : 1 ≤ w) {η : ℝ}
    (hη : 0 < η) :
    ∃ d₀ : ℕ, ∀ d ∈ 𝒟, d₀ ≤ d →
      (∀ (X : Fin (d * d * entryBits d) → Bool) (T : ℕ),
        Transpose.Tape.HaltsAt M (List.ofFn X) T →
        ∀ j cell, (entries (workWalk M (List.ofFn X) j) cell (T - 1)).card ≤ V) →
      (1 / 2 - η) * (d * d * entryBits d : ℕ) <
        entropy (inSkel w (haltT M) (inPosW M (L := d * d * entryBits d))) := by
  obtain ⟨d₀, hd₀⟩ := cor_IS hQ hk hV hw hc hη
  exact ⟨d₀, fun d hd hdd hentry => hd₀ d hdd (entryBits d) (one_le_entryBits d)
    (fun X => (h𝒟 d hd).transposesInput X) hentry⟩

open Classical in
/-- **Theorem L(c), merge depth, given binary [Q9.1].** For a depth bound `D` of the cold genies,
`β ≥ β(M)`, `V`, `s` and `ε, η` with `ε + η < 1/2` there is `d₀` such that at every `d ∈ 𝒟` with
`d ≥ d₀` at which `M` is oblivious at length `L` with halting time `T`: for every pruning of its
field DAG (along the trace of any input), every cold genie `ΓF` at `(V, ε)` of depth `D` and every
lineage assignment for it, more than `η L` output positions have a `ΓF`-free path from their output
node with more than `s` deep merges. -/
theorem thm_L_c (hQ : Q91Binary) {M : TM} {c : ℝ} (hc : 0 < c) (𝒟 : Set ℕ)
    (h𝒟 : ∀ d ∈ 𝒟, TransposesAt M d c) {V β D s : ℕ} (hβ : valueWidth M ≤ β) {ε η : ℝ}
    (hγ : 0 < 1 / 2 - ε - η) :
    ∃ d₀ : ℕ, ∀ d ∈ 𝒟, d₀ ≤ d → ∀ T : ℕ,
      Transpose.Tape.ObliviousOn M (Transpose.Tape.inputsOfLength (d * d * entryBits d)) T →
      ∀ (w₀ : Fin (d * d * entryBits d) → Bool)
        (Pr : Pruning M (d * d * entryBits d) (trace M (List.ofFn w₀)) T) (ΓF : Finset ℕ),
      IsColdGenie (L := d * d * entryBits d) (trace M (List.ofFn w₀)).work T V β ε D ΓF →
      ∀ lin : Forest,
      (∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ Pr.toFunDag.net.paths u →
        LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) (u :: v' :: π) →
        rCount (fun u v => DeepStep (trace M (List.ofFn w₀)).work T V (u / (M.k + 2))
          (v / (M.k + 2))) (u :: v' :: π) = 0) →
      η * (d * d * entryBits d : ℕ) < ((univ.filter fun ℓ : Fin (d * d * entryBits d) =>
        ∃ π ∈ Pr.toFunDag.net.paths (outputNodeOf (trace M (List.ofFn w₀)) T ℓ),
          LinNet.GFree (ΓF.biUnion (fieldNodesAt M.k)) π ∧
          s < dm lin (fun u v => DeepStep (trace M (List.ofFn w₀)).work T V (u / (M.k + 2))
            (v / (M.k + 2))) false π).card : ℝ) := by
  obtain ⟨d₀, hd₀⟩ := cor_HCstar_uniform_frozen hQ M hc (V := V) (D := D) (s := s) hβ hγ
  exact ⟨d₀, fun d hd hdd => hd₀ d hdd (entryBits d) (one_le_entryBits d) (h𝒟 d hd)⟩

end MergeDepth
