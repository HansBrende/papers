import MergeDepth.MergeDag
import MergeDepth.HopMachine

/-!
# Proposition 3.20(a) for a linear data path

The step-level form of `merge_reduction`: for the coordinate network of a linear data path, with
the cold genie `ΓF` (whole steps) and the checkpoints `Q` of Lemma 3.9 (`τ |Q| ≤ m |Rset|`), every
cut `Z` of the merge DAG gives `P_tpos = R + S` with `rank R ≤ β |ΓF| + |Q| + |Z|` and row `ℓ` of `S`
supported in the ball of radius `(s + 1) τ D` around the output step `tout ℓ`. The merge DAG is
built from the paths that start at the output coordinates outside `coordGenie m ΓF ∪ Q`.

`merge_reduction_machine` is the form for a data path whose edges are dependency steps of the
work-head walks and a cold genie in the sense of `IsColdGenie`: the conclusion of
`hop_charging_machine` with `X = ∅` and the rank bound increased by `|Z|`.
-/

namespace MergeDepth

open Finset Matrix Module BoundedNesting BoundedNesting.LinNet

variable {F : Type*} [Field F] {L m k : ℕ}

open Classical in
/-- **Proposition 3.20(a)** for a linear data path. -/
theorem merge_reduction_steps (net : LinNet F L m) (hm : 0 < m) (RH : ℕ → ℕ → Prop)
    [DecidableRel RH] (Rset : Finset (ℕ × ℕ)) (hRset : ∀ t s, RH t s → (t, s) ∈ Rset)
    (ΓF : Finset ℕ) (D β : ℕ)
    (hcold : ∀ t π, π ∈ net.paths t → LinNet.GFree ΓF π → rCount RH π = 0 → π.length ≤ D)
    (hval : ∀ s ∈ ΓF, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ (coordNet net hm).paths u →
      LinNet.GFree (coordGenie m ΓF) (u :: v' :: π) →
      rCount (fun u v => RH (u / m) (v / m)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ)) :
    ∃ Q : Finset ℕ, τ * Q.card ≤ m * Rset.card ∧ ∀ (Z : Finset ℕ) (s : ℕ),
      MCut (coordNet net hm) (fun u v => RH (u / m) (v / m)) lin (coordGenie m ΓF ∪ Q)
        (((univ : Finset (Fin L)).biUnion fun ℓ =>
          ((univ : Finset (Fin m)).filter fun i => φ ℓ i ≠ 0).image
            fun i : Fin m => tout ℓ * m + (i : ℕ)).filter (· ∉ coordGenie m ΓF ∪ Q)) Z s →
      ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧
        R.rank ≤ β * ΓF.card + Q.card + Z.card ∧
        ∀ ℓ j, S ℓ j ≠ 0 → j ∈ net.reach ∅ ((s + 1) * τ * D) (tout ℓ) := by
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
  let M : Finset ℕ := coordGenie m (Rset.image Prod.fst)
  have hM : ∀ u v, lin.nxt u = some v → RH (u / m) (v / m) → u ∈ M := fun u v _ hR =>
    (mem_coordGenie hm).mpr (mem_image.mpr ⟨_, hRset _ _ hR, rfl⟩)
  have hMcard : M.card ≤ m * Rset.card :=
    (card_coordGenie_le _).trans (Nat.mul_le_mul_left _ card_image_le)
  have hcold' : ∀ t π, π ∈ (coordNet net hm).paths t → LinNet.GFree (coordGenie m ΓF) π →
      rCount (fun u v => RH (u / m) (v / m)) π = 0 → π.length ≤ D := by
    intro t π hπ hfree hR
    have := hcold (t / m) (π.map (· / m)) (coord_paths net hm π t hπ) ((gfree_coord hm).mp hfree)
      (by rw [← rCount_coord]; exact hR)
    simpa using this
  obtain ⟨Q, -, hQ, hcov⟩ := covering lin M hτ
  refine ⟨Q, hQ.trans hMcard, fun Z s hZ => ?_⟩
  have hsub : ∀ ℓ, ∀ u ∈ tout' ℓ, u ∉ coordGenie m ΓF ∪ Q →
      u ∈ ((univ : Finset (Fin L)).biUnion tout').filter (· ∉ coordGenie m ΓF ∪ Q) :=
    fun ℓ u hu hu' => mem_filter.mpr ⟨mem_biUnion.mpr ⟨ℓ, mem_univ _, hu⟩, hu'⟩
  obtain ⟨R, S, hPRS, hrank, hsupp⟩ := merge_reduction (coordNet net hm)
    (fun u v => RH (u / m) (v / m)) lin (coordGenie m ΓF) D hcold' hside M hM hτ Q hcov
    _ hZ tout' hsub φ' φc tpos htrans'
  refine ⟨R, S, hPRS, ?_, fun ℓ j h => ?_⟩
  · calc R.rank ≤ finrank F (LinearMap.range (revealed (coordNet net hm) (coordGenie m ΓF))) +
          1 * Q.card + 1 * Z.card := hrank
      _ ≤ finrank F (LinearMap.range (revealed net ΓF)) + Q.card + Z.card := by
          rw [one_mul, one_mul]
          exact Nat.add_le_add_right (Nat.add_le_add_right (finrank_revealed_coord_le net hm ΓF) _) _
      _ ≤ β * ΓF.card + Q.card + Z.card :=
          Nat.add_le_add_right
            (Nat.add_le_add_right (finrank_revealed_le_of_values net ΓF β hval) _) _
  · obtain ⟨u, hu, -, hj⟩ := hsupp ℓ j h
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    have := coord_reach_subset net hm _ _ hj
    rwa [enc_div hm] at this

open Classical in
/-- **Proposition 3.20(a)** for a machine: the conclusion of `hop_charging_machine` with `X = ∅`
and the rank bound increased by `|Z|`, for every cut `Z` of the merge DAG. -/
theorem merge_reduction_machine (net : LinNet F L m) (hm : 0 < m) (xs : Fin k → ℕ → ℤ)
    {T C V β : ℕ} (hT : T ≤ C * (L + 1)) {ε : ℝ} {D : ℕ} {ΓF : Finset ℕ}
    (hcold : IsColdGenie (L := L) xs T V β ε D ΓF)
    (hout : ∀ t, ∀ s ∈ net.out t, DepStep xs T t s)
    (hval : ∀ s ∈ ΓF, ((binVecs L F).image fun w => net.val w s).card ≤ 2 ^ β)
    (lin : Forest)
    (hside : ∀ u v v' π, lin.nxt u = some v → v' ≠ v → (u :: v' :: π) ∈ (coordNet net hm).paths u →
      LinNet.GFree (coordGenie m ΓF) (u :: v' :: π) →
      rCount (fun u v => DeepStep xs T V (u / m) (v / m)) (u :: v' :: π) = 0)
    {τ : ℕ} (hτ : 1 ≤ τ) (tout : Fin L → ℕ) (φ : Fin L → Fin m → F) (φc : Fin L → F)
    (tpos : Fin L → Fin L)
    (htrans : ∀ w ∈ binVecs L F, ∀ ℓ, φc ℓ + φ ℓ ⬝ᵥ net.val w (tout ℓ) = w (tpos ℓ)) :
    ∃ Q : Finset ℕ, (τ * Q.card : ℝ) ≤ m * k * C * (L + 1) ∧ ∀ (Z : Finset ℕ) (s : ℕ),
      MCut (coordNet net hm) (fun u v => DeepStep xs T V (u / m) (v / m)) lin (coordGenie m ΓF ∪ Q)
        (((univ : Finset (Fin L)).biUnion fun ℓ =>
          ((univ : Finset (Fin m)).filter fun i => φ ℓ i ≠ 0).image
            fun i : Fin m => tout ℓ * m + (i : ℕ)).filter (· ∉ coordGenie m ΓF ∪ Q)) Z s →
      ∃ R S : Matrix (Fin L) (Fin L) F, Pmat tpos = R + S ∧
        (R.rank : ℝ) ≤ ε * L + m * k * C * (L + 1) / τ + Z.card ∧
        ∀ ℓ j, S ℓ j ≠ 0 → j ∈ net.reach ∅ ((s + 1) * τ * D) (tout ℓ) := by
  -- the deep pairs `(end, start)` of the deep hops
  let Rset : Finset (ℕ × ℕ) := (allHops xs T \ lightHops xs T V).image fun η => (η.2.2, η.2.1)
  have hRset : ∀ a b, DeepStep xs T V a b → (a, b) ∈ Rset := by
    rintro a b ⟨η, hη, he, hl⟩
    refine mem_image.mpr ⟨η, mem_sdiff.mpr ⟨hη, hl⟩, ?_⟩
    rw [he]
  have hRcard : Rset.card ≤ k * T :=
    card_image_le.trans ((card_le_card sdiff_subset).trans (card_allHops_le xs T))
  have hcold' : ∀ t π, π ∈ net.paths t → LinNet.GFree ΓF π → rCount (DeepStep xs T V) π = 0 →
      π.length ≤ D := fun t π hπ hfree hR =>
    hcold.2 π (isDepPath_of_paths hout π t hπ) hfree hR
  obtain ⟨Q, hQ, hall⟩ := merge_reduction_steps net hm (DeepStep xs T V) Rset hRset ΓF D β hcold'
    hval lin hside hτ tout φ φc tpos htrans
  have hQ' : (τ * Q.card : ℝ) ≤ m * k * C * (L + 1) := by
    have h1 : τ * Q.card ≤ m * (k * T) := hQ.trans (Nat.mul_le_mul_left _ hRcard)
    have h2 : m * (k * T) ≤ m * (k * (C * (L + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT)
    have h3 : (τ * Q.card : ℝ) ≤ m * (k * (C * (L + 1))) := by exact_mod_cast h1.trans h2
    linarith
  refine ⟨Q, hQ', fun Z s hZ => ?_⟩
  obtain ⟨R, S, hPRS, hrank, hsupp⟩ := hall Z s hZ
  refine ⟨R, S, hPRS, ?_, hsupp⟩
  have hτ' : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hqr : (Q.card : ℝ) ≤ m * k * C * (L + 1) / τ := by
    rw [le_div_iff₀ hτ']; linarith
  have hr : (R.rank : ℝ) ≤ β * ΓF.card + Q.card + Z.card := by exact_mod_cast hrank
  linarith [hcold.1]

end MergeDepth
