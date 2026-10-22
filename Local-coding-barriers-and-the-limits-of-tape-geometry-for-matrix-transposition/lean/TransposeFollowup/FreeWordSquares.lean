import TransposeFollowup.FreeWordPrefix

/-! Equal-length words with reduced squares and no inverse coincidences
have freely generating squares. The index set need not be finite. -/
namespace TransposeFollowup.FreeWordFamily
open Classical FreeGroup List
open scoped Pointwise
set_option autoImplicit false

universe u
variable {α : Type u} [DecidableEq α]

theorem square_prefix_update (w : List (α × Bool)) (hw : IsReduced (w ++ w)) :
    (mk w) ^ 2 • (prefixDomain (invRev w))ᶜ ⊆ prefixDomain w := by
  rintro _ ⟨x, hx, rfl⟩
  change w <+: ((mk w) ^ 2 * x).toWord
  simpa only [pow_two, mul_mk] using prefix_survives w w x hw hx

theorem inverse_square_prefix_update (w : List (α × Bool)) (hw : IsReduced (w ++ w)) :
    ((mk w) ^ 2)⁻¹ • (prefixDomain w)ᶜ ⊆ prefixDomain (invRev w) := by
  have he : ((mk w) ^ 2)⁻¹ = (mk (invRev w)) ^ 2 := by
    rw [pow_two, mul_inv_rev, inv_mk, pow_two]
  rw [he]
  simpa only [invRev_invRev] using
    square_prefix_update (invRev w) (reduced_double_inverse hw)

theorem squares_free {ι : Type u} [Nontrivial ι] (w : ι → List (α × Bool))
    (hw : ∀ i, IsReduced (w i ++ w i))
    (hlen : ∀ i j, (w i).length = (w j).length)
    (hinj : Function.Injective w) (hinv : ∀ i j, w i ≠ invRev (w j)) :
    Function.Injective (FreeGroup.lift (fun i => (mk (w i)) ^ 2)) := by
  apply FreeGroup.injective_lift_of_ping_pong (fun i => (mk (w i)) ^ 2)
    (fun i => prefixDomain (w i)) (fun i => prefixDomain (invRev (w i)))
  · intro i
    exact prefixDomain_nonempty ((hw i).infix ⟨[], w i, by simp⟩)
  · intro i j hij
    exact prefixDomain_disjoint (hlen i j) (fun he => hij (hinj he))
  · intro i j hij
    exact prefixDomain_disjoint (by simpa only [invRev_length] using hlen i j)
      (fun he => hij (hinj (invRev_injective he)))
  · intro i j
    exact prefixDomain_disjoint (by simpa only [invRev_length] using hlen i j) (hinv i j)
  · exact fun i => square_prefix_update (w i) (hw i)
  · exact fun i => inverse_square_prefix_update (w i) (hw i)

theorem mapped_squares_free {ι : Type u} {G : Type*} [Nontrivial ι] [Group G]
    (φ : FreeGroup α →* G) (hφ : Function.Injective φ) (w : ι → List (α × Bool))
    (hw : ∀ i, IsReduced (w i ++ w i))
    (hlen : ∀ i j, (w i).length = (w j).length)
    (hinj : Function.Injective w) (hinv : ∀ i j, w i ≠ invRev (w j)) :
    Function.Injective (FreeGroup.lift (fun i => (φ (mk (w i))) ^ 2)) := by
  have he : FreeGroup.lift (fun i => (φ (mk (w i))) ^ 2) =
      φ.comp (FreeGroup.lift (fun i => (mk (w i)) ^ 2)) := by
    ext i
    simp only [FreeGroup.lift_apply_of, MonoidHom.comp_apply, map_pow]
  rw [he]
  exact hφ.comp (squares_free w hw hlen hinj hinv)

end TransposeFollowup.FreeWordFamily
