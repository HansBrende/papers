import TransposeFollowup.ComponentDistance

/-! Counts of nearby row pairs and raw bit coordinates. These statements use
walk-defined nearness and hence retain the disconnected-graph convention. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

noncomputable def nearVertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) (ell : ℕ) (i : V) : Finset V :=
  Finset.univ.filter (GraphNear G ell i)

theorem mem_nearVertices {V : Type u} [Fintype V]
    (G : SimpleGraph V) (ell : ℕ) (i j : V) :
    j ∈ nearVertices G ell i ↔ GraphNear G ell i j := by simp [nearVertices]

/-- Ball counts are preserved as upper bounds under injective graph maps.
This permits arbitrary vertex relabeling in the path/cycle applications. -/
theorem nearVertices_card_le_of_embedding {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    (ell : ℕ) (i : V) :
    (nearVertices G ell i).card ≤ (nearVertices H ell (f i)).card := by
  have hsub : (nearVertices G ell i).image f ⊆ nearVertices H ell (f i) := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨p, hp⟩ := (mem_nearVertices G ell i x).mp hx
    apply (mem_nearVertices H ell (f i) (f x)).mpr
    exact ⟨p.map f, by simpa using hp⟩
  rw [← Finset.card_image_of_injective (nearVertices G ell i) hf]
  exact Finset.card_le_card hsub

noncomputable def nearPairs {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) :
    Finset (Fin n × Fin n) := Finset.univ.filter (fun p => GraphNear G ell p.1 p.2)

theorem mem_nearPairs {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) (i j : Fin n) :
    (i,j) ∈ nearPairs G ell ↔ GraphNear G ell i j := by simp [nearPairs]

noncomputable def nearPairsEquiv {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) :
    nearPairs G ell ≃ Σ i : Fin n, nearVertices G ell i where
  toFun p := ⟨p.val.1, ⟨p.val.2, (mem_nearVertices G ell _ _).mpr
    ((mem_nearPairs G ell _ _).mp p.property)⟩⟩
  invFun p := ⟨(p.1,p.2.val), (mem_nearPairs G ell _ _).mpr
    ((mem_nearVertices G ell _ _).mp p.2.property)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

theorem card_nearPairs {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) :
    (nearPairs G ell).card = ∑ i, (nearVertices G ell i).card := by
  simpa only [Fintype.card_coe, Fintype.card_sigma] using Fintype.card_congr (nearPairsEquiv G ell)

noncomputable def nearBitsEquiv {n b : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) :
    RecodedXorCode.nearBits (b := b) G ell ≃ (nearPairs G ell) × Fin b where
  toFun v := ⟨⟨(v.val.1,v.val.2.1), (mem_nearPairs G ell _ _).mpr
    (Finset.mem_filter.mp v.property).2⟩, v.val.2.2⟩
  invFun p := ⟨(p.1.val.1, (p.1.val.2,p.2)), Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (mem_nearPairs G ell _ _).mp p.1.property⟩⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

theorem card_nearBits {n b : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) :
    (RecodedXorCode.nearBits (b := b) G ell).card = b * (nearPairs G ell).card := by
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
    Fintype.card_congr (nearBitsEquiv (b := b) G ell)

theorem card_nearBits_le_of_balls {n b : ℕ} (G : SimpleGraph (Fin n)) (ell K : ℕ)
    (hK : ∀ i, (nearVertices G ell i).card ≤ K) :
    (RecodedXorCode.nearBits (b := b) G ell).card ≤ b * n * K := by
  rw [card_nearBits, card_nearPairs]
  calc
    _ ≤ b * ∑ _i : Fin n, K := Nat.mul_le_mul_left _ (Finset.sum_le_sum fun i _ => hK i)
    _ = _ := by simp [Nat.mul_assoc]

theorem nearVertices_succ_subset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ell : ℕ) (i : V) :
    nearVertices G (ell + 1) i ⊆
      insert i ((G.neighborFinset i).biUnion (nearVertices G ell)) := by
  intro j hj
  obtain ⟨p, hp⟩ := (mem_nearVertices G (ell+1) i j).mp hj
  cases p with
  | nil => exact Finset.mem_insert_self _ _
  | @cons i k j hik p =>
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨k, (G.mem_neighborFinset i k).mpr hik, ?_⟩
    apply (mem_nearVertices G ell k j).mpr
    exact ⟨p, by simpa only [SimpleGraph.Walk.length_cons, Nat.add_lt_add_iff_right] using hp⟩

/-- Uniform maximum degree bounds the radius-(ell-1) balls by the geometric
sum of walk counts. No connectedness or regularity assumption is needed. -/
theorem nearVertices_card_le_geometric {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Delta : ℕ)
    (hdegree : ∀ i, G.degree i ≤ Delta) (ell : ℕ) (i : V) :
    (nearVertices G ell i).card ≤ ∑ r ∈ Finset.range ell, Delta ^ r := by
  induction ell generalizing i with
  | zero =>
      have he : nearVertices G 0 i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        obtain ⟨p, hp⟩ := (mem_nearVertices G 0 i j).mp hj
        omega
      simp [he]
  | succ ell ih =>
      calc
        _ ≤ (insert i ((G.neighborFinset i).biUnion (nearVertices G ell))).card :=
          Finset.card_le_card (nearVertices_succ_subset G ell i)
        _ ≤ ((G.neighborFinset i).biUnion (nearVertices G ell)).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ (∑ j ∈ G.neighborFinset i, (nearVertices G ell j).card) + 1 :=
          Nat.add_le_add_right Finset.card_biUnion_le 1
        _ ≤ (∑ _j ∈ G.neighborFinset i, ∑ r ∈ Finset.range ell, Delta ^ r) + 1 :=
          Nat.add_le_add_right (Finset.sum_le_sum fun j _ => ih j) 1
        _ = G.degree i * (∑ r ∈ Finset.range ell, Delta ^ r) + 1 := by simp
        _ ≤ Delta * (∑ r ∈ Finset.range ell, Delta ^ r) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ (hdegree i)) 1
        _ = ∑ r ∈ Finset.range (ell + 1), Delta ^ r := by
          rw [Finset.sum_range_succ']
          simp [pow_succ', Finset.mul_sum]

theorem geometric_sum_le_twice_power (D k : ℕ) (hD : 2 ≤ D) :
    (∑ r ∈ Finset.range (k + 1), D ^ r) ≤ 2 * D ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        _ ≤ 2 * D ^ k + D ^ (k + 1) := Nat.add_le_add_right ih _
        _ ≤ D ^ (k + 1) + D ^ (k + 1) := by
          apply Nat.add_le_add_right
          simpa only [pow_succ'] using Nat.mul_le_mul_right (D ^ k) hD
        _ = _ := by omega

theorem nearVertices_card_le_power {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ i, G.degree i ≤ D) (k : ℕ) (i : V) :
    (nearVertices G (k + 1) i).card ≤ 2 * D ^ k :=
  (nearVertices_card_le_geometric G D hdegree (k + 1) i).trans
    (geometric_sum_le_twice_power D k hD)

end TransposeFollowup
