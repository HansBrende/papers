import MergeDepth.Lineage

/-!
# Hop charging: the rank decomposition

`rigidity_finrank` is the eighth paper's per-machine rigidity with the rank of the revealed linear
map in place of its value count: if every output of a transposing linear network has linear depth
at most `D` for a genie `Γ`, then `P_tpos = R + S` with `rank R` at most the rank of the revealed
map `w ↦ (vlin_s(w))_{s ∈ Γ}` and row `ℓ` of `S` supported in `I^D_Γ(ℓ)`.

`hop_charging` combines it with `paths_short`: for a network whose `Γ₀`-free paths from the output
vertices of every position outside a set `X` have at most `s` deep merges, `P_tpos = R + S` with
`rank R ≤ rank(E_{Γ₀}) + m |Q| + |X|`, `τ |Q| ≤ |M|`, and row `ℓ` of `S` zero for `ℓ ∈ X` and
otherwise supported in the balls of radius `(s + 1) τ D` around the output vertices of `ℓ`.
-/

namespace MergeDepth

open Finset Matrix Module BoundedNesting BoundedNesting.LinNet

variable {F : Type*} [Field F] {L m : ℕ}

/-- The revealed linear map of a genie: `w ↦ (vlin_s(w))_{s ∈ Γ}`. -/
def revealed (net : LinNet F L m) (Γ : Finset ℕ) : (Fin L → F) →ₗ[F] (Γ → Fin m → F) :=
  LinearMap.pi fun s => net.vlinMap s.1

/-- If every `Γ`-free path from `t` has at most `D + 1` vertices, the path sums of `t` vanish
outside `I^D_Γ(t)`. -/
theorem C_eq_zero_of_short (net : LinNet F L m) (Γ : Finset ℕ) (D t : ℕ)
    (hshort : ∀ π, π ∈ net.paths t → LinNet.GFree Γ π → π.length ≤ D + 1) (j : Fin L)
    (hj : j ∉ net.reach Γ D t) : net.C Γ t j = 0 := by
  classical
  unfold LinNet.C
  refine sum_eq_zero fun π hπ => ?_
  obtain ⟨hπ, hfree, hrd⟩ := mem_filter.mp hπ
  exact absurd (mem_filter.mpr ⟨mem_univ _, π, hπ, hfree, hshort π hπ hfree, hrd⟩) hj

open Classical in
/-- **Rigidity, rank form.** Let the network transpose on binary inputs, output `ℓ` being the affine
functional `φc ℓ + ∑_{u ∈ tout ℓ} φ ℓ u ⬝ᵥ ·` of the values at the output vertices `tout ℓ`. Then
`P_tpos = R₀ + S₀`, where row `ℓ` of `S₀` collects the path sums of the output vertices of `ℓ` and
`rank R₀` is at most the rank of the revealed map of `Γ`. -/
theorem rigidity_core (net : LinNet F L m) (tout : Fin L → Finset ℕ)
    (φ : Fin L → ℕ → Fin m → F) (φc : Fin L → F) (tpos : Fin L → Fin L) (Γ : Finset ℕ)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ,
      φc ℓ + ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.val w u = w (tpos ℓ)) :
    ∃ R : Matrix (Fin L) (Fin L) F,
      Pmat tpos = R + Matrix.of (fun ℓ j => ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.C Γ u j) ∧
      R.rank ≤ finrank F (LinearMap.range (revealed net Γ)) := by
  let E := revealed net Γ
  let G : (Γ → Fin m → F) →ₗ[F] (Fin L → F) :=
    { toFun := fun e ℓ => ∑ u ∈ tout ℓ, ∑ s : Γ, φ ℓ u ⬝ᵥ (net.Tm Γ s u *ᵥ e s)
      map_add' := fun e e' => by
        funext ℓ
        simp only [Pi.add_apply, Matrix.mulVec_add, dotProduct_add, Finset.sum_add_distrib]
      map_smul' := fun c e => by
        funext ℓ
        simp only [Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum] }
  let R : Matrix (Fin L) (Fin L) F := LinearMap.toMatrix' (G ∘ₗ E)
  refine ⟨R, ?_, ?_⟩
  · ext ℓ j
    have hb : ∀ w : Fin L → F, (∀ i, w i = 0 ∨ w i = 1) → w ∈ binVecs L F := fun w hw =>
      Fintype.mem_piFinset.mpr fun i => by rcases hw i with h | h <;> simp [h]
    have h0 := htrans 0 (hb 0 fun _ => Or.inl rfl) ℓ
    have hj := htrans (Pi.single j 1) (hb _ fun i => by
      by_cases h : i = j
      · subst h; simp
      · simp [h]) ℓ
    have hexp : ∀ u, φ ℓ u ⬝ᵥ net.val (Pi.single j 1) u = φ ℓ u ⬝ᵥ net.val 0 u +
        ((∑ s : Γ, φ ℓ u ⬝ᵥ (net.Tm Γ s u *ᵥ net.vlin (Pi.single j 1) s)) +
          φ ℓ u ⬝ᵥ net.C Γ u j) := by
      intro u
      rw [net.val_eq_add (Pi.single j 1) u, dotProduct_add, net.vlin_expand Γ (Pi.single j 1) u,
        dotProduct_add, dotProduct_sum, dotProduct_sum]
      congr 2
      · exact (Finset.sum_coe_sort Γ
          fun s => φ ℓ u ⬝ᵥ (net.Tm Γ s u *ᵥ net.vlin (Pi.single j 1) s)).symm
      · rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj'])
          (fun h => absurd (Finset.mem_univ j) h)]
        simp
    simp only [hexp, Finset.sum_add_distrib] at hj
    have hRj : R ℓ j = ∑ u ∈ tout ℓ, ∑ s : Γ, φ ℓ u ⬝ᵥ (net.Tm Γ s u *ᵥ net.vlin (Pi.single j 1) s) :=
      rfl
    have hP : Pmat (F := F) tpos ℓ j = (Pi.single j 1 : Fin L → F) (tpos ℓ) := by
      simp [Pmat, Pi.single_apply, eq_comm]
    rw [Matrix.add_apply, hRj, Matrix.of_apply, hP]
    have : φc ℓ + ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.val 0 u = 0 := by simpa using h0
    linear_combination this - hj
  · have hR : R.mulVecLin = G ∘ₗ E := by
      rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    change finrank F (LinearMap.range R.mulVecLin) ≤ _
    rw [hR, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _

/-- Rank is subadditive. -/
theorem rank_add_le' (A B : Matrix (Fin L) (Fin L) F) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc finrank F (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank F (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule F _) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- A matrix whose nonzero rows lie in `X` has rank at most `|X|`. -/
theorem rank_le_card_rows (A : Matrix (Fin L) (Fin L) F) (X : Finset (Fin L))
    (h : ∀ ℓ j, A ℓ j ≠ 0 → ℓ ∈ X) : A.rank ≤ X.card := by
  classical
  unfold Matrix.rank
  have hsub : LinearMap.range A.mulVecLin ≤ Submodule.span F
      ((X.image fun ℓ => (Pi.single ℓ 1 : Fin L → F)) : Set (Fin L → F)) := by
    rintro _ ⟨v, rfl⟩
    have hv : A.mulVecLin v = ∑ ℓ ∈ X, (A *ᵥ v) ℓ • (Pi.single ℓ 1 : Fin L → F) := by
      funext i
      simp only [Matrix.mulVecLin_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
      by_cases hi : i ∈ X
      · simp [hi]
      · simp only [hi, ↓reduceIte]
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_eq_zero fun j _ => by
          by_cases hA : A i j = 0
          · simp [hA]
          · exact absurd (h i j hA) hi
    rw [hv]
    exact Submodule.sum_mem _ fun ℓ hℓ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (by simpa using ⟨ℓ, hℓ, rfl⟩))
  calc finrank F (LinearMap.range A.mulVecLin)
      ≤ finrank F (Submodule.span F
          ((X.image fun ℓ => (Pi.single ℓ 1 : Fin L → F)) : Set (Fin L → F))) :=
        Submodule.finrank_mono hsub
    _ ≤ (X.image fun ℓ => (Pi.single ℓ 1 : Fin L → F)).card := finrank_span_finset_le_card _
    _ ≤ X.card := card_image_le

open Classical in
/-- **Rigidity with exceptional outputs.** Let the network transpose on binary inputs, and let every
output vertex of every position outside `X` have linear depth at most `D` for `Γ`. Then
`P_tpos = R + S` with `rank R` at most the rank of the revealed map of `Γ` plus `|X|`, and row `ℓ`
of `S` zero for `ℓ ∈ X` and otherwise supported in `⋃_{u ∈ tout ℓ} I^D_Γ(u)`. -/
theorem rigidity_finrank (net : LinNet F L m) (tout : Fin L → Finset ℕ)
    (φ : Fin L → ℕ → Fin m → F) (φc : Fin L → F) (tpos : Fin L → Fin L) (Γ : Finset ℕ) (D : ℕ)
    (X : Finset (Fin L))
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ,
      φc ℓ + ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.val w u = w (tpos ℓ))
    (hdepth : ∀ ℓ ∉ X, ∀ u ∈ tout ℓ, ∀ j ∉ net.reach Γ D u, φ ℓ u ⬝ᵥ net.C Γ u j = 0) :
    ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧
      R.rank ≤ finrank F (LinearMap.range (revealed net Γ)) + X.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → ℓ ∉ X ∧ ∃ u ∈ tout ℓ, j ∈ net.reach Γ D u := by
  obtain ⟨R₀, hP, hR₀⟩ := rigidity_core net tout φ φc tpos Γ htrans
  set S₀ : Matrix (Fin L) (Fin L) F := Matrix.of (fun ℓ j => ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.C Γ u j)
  let S : Matrix (Fin L) (Fin L) F := Matrix.of fun ℓ j => if ℓ ∈ X then 0 else S₀ ℓ j
  let Δ : Matrix (Fin L) (Fin L) F := Matrix.of fun ℓ j => if ℓ ∈ X then S₀ ℓ j else 0
  refine ⟨R₀ + Δ, S, ?_, ?_, ?_⟩
  · rw [hP]
    ext ℓ j
    simp only [Matrix.add_apply, S, Δ, Matrix.of_apply]
    split_ifs <;> ring
  · calc (R₀ + Δ).rank ≤ R₀.rank + Δ.rank := rank_add_le' _ _
      _ ≤ _ := Nat.add_le_add hR₀ (rank_le_card_rows Δ X fun ℓ j h => by
          by_contra hX
          simp [Δ, hX] at h)
  · intro ℓ j hS
    have hX : ℓ ∉ X := fun hX => hS (by simp [S, hX])
    refine ⟨hX, ?_⟩
    by_contra hj
    push Not at hj
    apply hS
    simp only [S, Matrix.of_apply, hX, ↓reduceIte, S₀]
    exact Finset.sum_eq_zero fun u hu => hdepth ℓ hX u hu j (hj u hu)

/-- The revealed map of a union has rank at most the sum of the ranks. -/
theorem finrank_revealed_union_le (net : LinNet F L m) (A B : Finset ℕ) :
    finrank F (LinearMap.range (revealed net (A ∪ B))) ≤
      finrank F (LinearMap.range (revealed net A)) + finrank F (LinearMap.range (revealed net B)) := by
  classical
  have hker : LinearMap.ker (revealed net A) ⊓ LinearMap.ker (revealed net B) ≤
      LinearMap.ker (revealed net (A ∪ B)) := by
    intro w hw
    obtain ⟨hA, hB⟩ := Submodule.mem_inf.mp hw
    rw [LinearMap.mem_ker] at hA hB ⊢
    funext s
    rcases mem_union.mp s.2 with hs | hs
    · have := congr_fun hA ⟨s.1, hs⟩
      simpa [revealed] using this
    · have := congr_fun hB ⟨s.1, hs⟩
      simpa [revealed] using this
  have h1 := LinearMap.finrank_range_add_finrank_ker (revealed net (A ∪ B))
  have h2 := LinearMap.finrank_range_add_finrank_ker (revealed net A)
  have h3 := LinearMap.finrank_range_add_finrank_ker (revealed net B)
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (revealed net A))
    (LinearMap.ker (revealed net B))
  have h5 := Submodule.finrank_mono hker
  have h6 := Submodule.finrank_le (LinearMap.ker (revealed net A) ⊔ LinearMap.ker (revealed net B))
  omega

/-- A genie of `q` vertices reveals a map of rank at most `m q`. -/
theorem finrank_revealed_le (net : LinNet F L m) (Q : Finset ℕ) :
    finrank F (LinearMap.range (revealed net Q)) ≤ m * Q.card := by
  calc finrank F (LinearMap.range (revealed net Q)) ≤ finrank F (Q → Fin m → F) :=
        Submodule.finrank_le _
    _ = m * Q.card := by rw [Module.finrank_pi_fintype]; simp [mul_comm]

/-- **Hop charging.** Let a linear network transpose on binary inputs, output `ℓ` being an affine
functional of the values at the output vertices `tout ℓ`. Let every `Γ₀`-free path without deep edges
have at most `D` vertices, let the other out-edges of continuations be dead, let `M` contain the
tails of the deep lineage edges, let `τ ≥ 1`, and let every `Γ₀`-free path from an output vertex of a
position outside `X` have at most `s` deep merges. Then there is a set `Q` with `τ |Q| ≤ |M|` such
that `P_tpos = R + S` with `rank R ≤ rank(E_{Γ₀}) + m |Q| + |X|` and row `ℓ` of `S` zero for
`ℓ ∈ X` and otherwise supported in the balls of radius `(s + 1) τ D` around the output vertices of
`ℓ`. -/
theorem hop_charging (net : LinNet F L m) (Rr : ℕ → ℕ → Prop) [DecidableRel Rr] (lin : Forest)
    (Γ₀ : Finset ℕ) (D : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree Γ₀ π → rCount Rr π = 0 → π.length ≤ D)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ net.paths u →
      LinNet.GFree Γ₀ (u :: v' :: π) → rCount Rr (u :: v' :: π) = 0)
    (M : Finset ℕ) (hM : ∀ u v, lin.nxt u = some v → Rr u v → u ∈ M) {τ : ℕ} (hτ : 1 ≤ τ)
    (s : ℕ) (tout : Fin L → Finset ℕ) (φ : Fin L → ℕ → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L) (X : Finset (Fin L))
    (hround : ∀ ℓ ∉ X, ∀ u ∈ tout ℓ, ∀ π, π ∈ net.paths u → LinNet.GFree Γ₀ π →
      dm lin Rr false π ≤ s)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ,
      φc ℓ + ∑ u ∈ tout ℓ, φ ℓ u ⬝ᵥ net.val w u = w (tpos ℓ)) :
    ∃ (Q : Finset ℕ) (R S : Matrix (Fin L) (Fin L) F), τ * Q.card ≤ M.card ∧
      Pmat tpos = R + S ∧
      R.rank ≤ finrank F (LinearMap.range (revealed net Γ₀)) + m * Q.card + X.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → ℓ ∉ X ∧ ∃ u ∈ tout ℓ, j ∈ net.reach ∅ ((s + 1) * τ * D) u := by
  obtain ⟨Q, hQ, hshort⟩ := paths_short net Rr lin Γ₀ D hcold hside M hM hτ
  obtain ⟨R, S, hPRS, hrank, hsupp⟩ := rigidity_finrank net tout φ φc tpos (Γ₀ ∪ Q)
    ((s + 1) * τ * D) X htrans (fun ℓ hℓ u hu j hj => by
      rw [C_eq_zero_of_short net (Γ₀ ∪ Q) _ u (fun π hπ hfree =>
        (hshort u s (hround ℓ hℓ u hu) π hπ hfree).trans (Nat.le_succ _)) j hj]
      simp)
  refine ⟨Q, R, S, hQ, hPRS, ?_, fun ℓ j h => ?_⟩
  · calc R.rank ≤ finrank F (LinearMap.range (revealed net (Γ₀ ∪ Q))) + X.card := hrank
      _ ≤ _ := Nat.add_le_add_right (finrank_revealed_union_le net Γ₀ Q) _
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_left (finrank_revealed_le net Q) _) _
  · obtain ⟨hX, u, hu, hj⟩ := hsupp ℓ j h
    exact ⟨hX, u, hu, net.reach_subset _ _ _ hj⟩

end MergeDepth
