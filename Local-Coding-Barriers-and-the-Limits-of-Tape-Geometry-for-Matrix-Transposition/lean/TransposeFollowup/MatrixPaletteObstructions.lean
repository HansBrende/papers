import TransposeFollowup.MatrixPaletteLimits
import TransposeFollowup.IntegerMatrixGeometry
import TransposeFollowup.TernaryMatrixGeometry

/-! Source206(a,b): neither declared palette has a bounded-length word
family agreeing with raw transpose on sets of coentropy o(P). Operation
choices may depend arbitrarily on size. No native or geometric premises
are imposed on callers: all are supplied by the concrete palette proofs. -/
namespace TransposeFollowup.IntegerMatrixPalette
open Classical Set Filter Topology Transpose
set_option autoImplicit false

theorem no_high_entropy_transpose {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {K : ℕ} (ops : ℕ → List Operation) (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ A : Matrix,
      w=encode (ns i) (entryBits (ns i)) A ∧
      output (entryBits (ns i)) (ns i) (ops i) w=
        encode (ns i) (entryBits (ns i)) (transpose A)) : False :=
  MatrixPaletteLimits.no_high_entropy_transpose hns cost code value approximation correct cost_le
    (fun b d op A t _ hH => approximation_cover b d op A hH t)
    approximation_error ops hK hm hmL hcorr

end TransposeFollowup.IntegerMatrixPalette

namespace TransposeFollowup.TernaryMatrixPalette
open Classical Set Filter Topology Transpose
set_option autoImplicit false

theorem no_high_entropy_transpose {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {K : ℕ} (ops : ℕ → List Operation) (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ A : Matrix,
      w=encode (ns i) (entryBits (ns i)) A ∧
      output (entryBits (ns i)) (ns i) (ops i) w=
        encode (ns i) (entryBits (ns i)) (transpose A)) : False :=
  MatrixPaletteLimits.no_high_entropy_transpose hns cost code value approximation
    (fun b d _ _ => correct b d) cost_le
    (fun b d op A t _ hH => approximation_cover b d op A hH t)
    approximation_error ops hK hm hmL hcorr

end TransposeFollowup.TernaryMatrixPalette
