import MergeDepth.Coordinates

/-!
# Hop charging for a linear data path

The step-level form of hop charging (Theorem HC′ of the paper). The data path is a linear network
`net` of width `m` on the dependency DAG; deep hops form a relation `RH` on steps, supported on a
finite set `Rset` of pairs; `ΓF` is a whole-step genie each of whose steps takes at most `2^β` values
on binary inputs, and every `ΓF`-free path of the dependency DAG without deep hops has at most `D`
vertices (the cold depth). The lineage structure lives on the coordinate network: `lin` is a lineage
forest on it whose other out-edges are dead (`hside`).

`hop_charging_steps`: if every `ΓF`-free coordinate path from an output coordinate of a position
outside `X` has at most `s` deep merges, then `P_tpos = R + S` with
`rank R ≤ β |ΓF| + q + |X|`, `τ q ≤ m |Rset|`, and row `ℓ` of `S` zero for `ℓ ∈ X` and otherwise
supported in the ball of radius `(s + 1) τ D` around the output step `tout ℓ`.
-/

namespace MergeDepth

open Finset Matrix Module BoundedNesting BoundedNesting.LinNet

variable {F : Type*} [Field F] {L m : ℕ}

/-- A map whose kernel contains the kernel of `f` has rank at most that of `f`. -/
theorem finrank_range_le_of_ker_le {W₁ W₂ : Type*} [AddCommGroup W₁] [Module F W₁]
    [AddCommGroup W₂] [Module F W₂] (f : (Fin L → F) →ₗ[F] W₁) (g : (Fin L → F) →ₗ[F] W₂)
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    finrank F (LinearMap.range g) ≤ finrank F (LinearMap.range f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 := Submodule.finrank_mono h
  omega

theorem coord_vlin (net : LinNet F L m) (hm : 0 < m) (w : Fin L → F) (u : ℕ) :
    (coordNet net hm).vlin w u 0 = net.vlin w (u / m) (crd hm u) := by
  have h1 := congr_fun ((coordNet net hm).val_eq_add w u) 0
  have h2 := congr_fun (net.val_eq_add w (u / m)) (crd hm u)
  rw [Pi.add_apply, coord_val, coord_val] at h1
  rw [Pi.add_apply] at h2
  linear_combination h2 - h1

/-- The coordinate genie of `ΓF` reveals no more than `ΓF`. -/
theorem finrank_revealed_coord_le (net : LinNet F L m) (hm : 0 < m) (Γ : Finset ℕ) :
    finrank F (LinearMap.range (revealed (coordNet net hm) (coordGenie m Γ))) ≤
      finrank F (LinearMap.range (revealed net Γ)) := by
  refine finrank_range_le_of_ker_le _ _ fun w hw => ?_
  rw [LinearMap.mem_ker] at hw ⊢
  funext u i
  have hu := (mem_coordGenie hm).mp u.2
  have := congr_fun (congr_fun hw ⟨u.1 / m, hu⟩) (crd hm u.1)
  simp only [revealed, LinearMap.pi_apply, vlinMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply] at this ⊢
  rw [Fin.fin_one_eq_zero i, coord_vlin net hm w u.1]
  exact this

open Classical in
/-- The eighth paper's value count: a genie whose steps take at most `2^β` values on binary inputs
reveals a map of rank at most `β |Γ|`. -/
theorem finrank_revealed_le_of_values (net : LinNet F L m) (Γ : Finset ℕ) (β : ℕ)
    (hval : ∀ s ∈ Γ, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β) :
    finrank F (LinearMap.range (revealed net Γ)) ≤ β * Γ.card := by
  classical
  have h2 := two_pow_finrank_le (revealed net Γ)
  have h3 : ((binVecs L F).image (revealed net Γ)).card ≤ 2 ^ (β * Γ.card) := by
    calc ((binVecs L F).image (revealed net Γ)).card
        ≤ (Fintype.piFinset fun s : Γ => (binVecs L F).image fun w => net.vlin w s.1).card := by
          refine card_le_card fun x hx => ?_
          obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
          exact Fintype.mem_piFinset.mpr fun s => mem_image.mpr ⟨w, hw, rfl⟩
      _ = ∏ s : Γ, ((binVecs L F).image fun w => net.vlin w s.1).card := Fintype.card_piFinset _
      _ ≤ ∏ _s : Γ, 2 ^ β := by
          refine Finset.prod_le_prod fun s _ => ?_
          have : (binVecs L F).image (fun w => net.vlin w s.1) =
              ((binVecs L F).image fun w => net.val w s.1).image (· - net.val 0 s.1) := by
            rw [Finset.image_image]
            refine Finset.image_congr fun w _ => ?_
            simp only [Function.comp_apply, net.val_eq_add w s.1, add_sub_cancel_left]
          rw [this]
          exact card_image_le.trans (hval s.1 s.2)
      _ = 2 ^ (β * Γ.card) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]
  have h4 : 2 ^ finrank F (LinearMap.range (revealed net Γ)) ≤ 2 ^ (β * Γ.card) := h2.trans h3
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4

open Classical in
/-- **Hop charging for a linear data path** (Theorem HC′(a)). -/
theorem hop_charging_steps (net : LinNet F L m) (hm : 0 < m) (RH : ℕ → ℕ → Prop) [DecidableRel RH]
    (Rset : Finset (ℕ × ℕ)) (hRset : ∀ t s, RH t s → (t, s) ∈ Rset)
    (ΓF : Finset ℕ) (D β : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree ΓF π → rCount RH π = 0 → π.length ≤ D)
    (hval : ∀ s ∈ ΓF, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ (coordNet net hm).paths u →
      LinNet.GFree (coordGenie m ΓF) (u :: v' :: π) →
      rCount (fun u v => RH (u / m) (v / m)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (s : ℕ) (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L) (X : Finset (Fin L))
    (hround : ∀ ℓ ∉ X, ∀ i : Fin m, φ ℓ i ≠ 0 → ∀ π, π ∈ (coordNet net hm).paths (tout ℓ * m + i) →
      LinNet.GFree (coordGenie m ΓF) π → dm lin (fun u v => RH (u / m) (v / m)) false π ≤ s)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ)) :
    ∃ (q : ℕ) (R S : Matrix (Fin L) (Fin L) F), τ * q ≤ m * Rset.card ∧ Pmat tpos = R + S ∧
      R.rank ≤ β * ΓF.card + q + X.card ∧
      ∀ ℓ j, S ℓ j ≠ 0 → ℓ ∉ X ∧ j ∈ net.reach ∅ ((s + 1) * τ * D) (tout ℓ) := by
  -- the output coordinates
  let tout' : Fin L → Finset ℕ := fun ℓ =>
    ((univ : Finset (Fin m)).filter fun i => φ ℓ i ≠ 0).image fun i : Fin m => tout ℓ * m + (i : ℕ)
  let φ' : Fin L → ℕ → Fin 1 → F := fun ℓ u _ => φ ℓ (crd hm u)
  have htrans' : ∀ w ∈ binVecs L F, ∀ ℓ,
      φc ℓ + ∑ u ∈ tout' ℓ, φ' ℓ u ⬝ᵥ (coordNet net hm).val w u = w (tpos ℓ) := by
    intro w hw ℓ
    rw [← htrans w hw ℓ]
    congr 1
    rw [sum_image (fun i _ j _ h => Fin.ext (by simpa using h)), sum_filter]
    simp only [dotProduct, Fin.sum_univ_one, φ']
    refine sum_congr rfl fun i _ => ?_
    rw [coord_val, enc_div hm, crd_enc hm]
    split_ifs with h
    · rfl
    · push Not at h
      rw [h, zero_mul]
  -- the marked set: all coordinates of tails of deep hops
  let M : Finset ℕ := coordGenie m (Rset.image Prod.fst)
  have hM : ∀ u v, lin.nxt u = some v → RH (u / m) (v / m) → u ∈ M := fun u v _ hR =>
    (mem_coordGenie hm).mpr (mem_image.mpr ⟨_, hRset _ _ hR, rfl⟩)
  have hMcard : M.card ≤ m * Rset.card :=
    (card_coordGenie_le _).trans (Nat.mul_le_mul_left _ card_image_le)
  -- the cold depth of the coordinate network
  have hcold' : ∀ t π, π ∈ (coordNet net hm).paths t → LinNet.GFree (coordGenie m ΓF) π →
      rCount (fun u v => RH (u / m) (v / m)) π = 0 → π.length ≤ D := by
    intro t π hπ hfree hR
    have := hcold (t / m) (π.map (· / m)) (coord_paths net hm π t hπ) ((gfree_coord hm).mp hfree)
      (by rw [← rCount_coord]; exact hR)
    simpa using this
  have hround' : ∀ ℓ ∉ X, ∀ u ∈ tout' ℓ, ∀ π, π ∈ (coordNet net hm).paths u →
      LinNet.GFree (coordGenie m ΓF) π → dm lin (fun u v => RH (u / m) (v / m)) false π ≤ s := by
    intro ℓ hℓ u hu π hπ hfree
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    exact hround ℓ hℓ i (mem_filter.mp hi).2 π hπ hfree
  obtain ⟨Q, R, S, hQ, hPRS, hrank, hsupp⟩ := hop_charging (coordNet net hm)
    (fun u v => RH (u / m) (v / m)) lin (coordGenie m ΓF) D hcold' hside M hM hτ s tout' φ' φc tpos
    X hround' htrans'
  refine ⟨Q.card, R, S, hQ.trans hMcard, hPRS, ?_, fun ℓ j h => ?_⟩
  · calc R.rank ≤ finrank F (LinearMap.range (revealed (coordNet net hm) (coordGenie m ΓF))) +
          1 * Q.card + X.card := hrank
      _ ≤ finrank F (LinearMap.range (revealed net ΓF)) + Q.card + X.card := by
          rw [one_mul]
          exact Nat.add_le_add_right (Nat.add_le_add_right (finrank_revealed_coord_le net hm ΓF) _) _
      _ ≤ β * ΓF.card + Q.card + X.card :=
          Nat.add_le_add_right
            (Nat.add_le_add_right (finrank_revealed_le_of_values net ΓF β hval) _) _
  · obtain ⟨hX, u, hu, hj⟩ := hsupp ℓ j h
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    have := coord_reach_subset net hm _ _ hj
    rw [enc_div hm] at this
    exact ⟨hX, this⟩

end MergeDepth
