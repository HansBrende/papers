import SubcubicMemo.Schedules

/-! Single-use ambiguity costs and their zero-cost polymatroid corollary. -/

namespace SubcubicMemo

open Finset MotionDepthCodes
open scoped BigOperators

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

omit [Fintype V] in
/-- A row's marginal cost is an upper bound after its other members are known. -/
theorem marginal_le_of_erase_subset {h : Finset V → ℝ} (hh : IsPolymatroid h)
    {R K : Finset V} {x : V} (hx : x ∈ R) (hready : R.erase x ⊆ K) :
    h (insert x K) - h K ≤ h R - h (R.erase x) := by
  have hu : R ∪ K = insert x K := by
    rw [← insert_erase hx, insert_union, union_eq_right.mpr hready]
  have hi : R.erase x ⊆ R ∩ K := subset_inter (erase_subset _ _) hready
  have h1 := hh.submod R K
  rw [hu] at h1
  have h2 := hh.mono hi
  linarith

/-- The sharp schedule ledger charges the actual used directions. -/
theorem Schedule.polymatroid_directions {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) :
    h W ≤ h K + (l.map (fun e =>
      h (insert e.1 (recSet M e.1) ∩ W) -
      h ((insert e.1 (recSet M e.1) ∩ W).erase e.2))).sum := by
  induction hl with
  | nil hWK => simpa using hh.mono hWK
  | cons _ hx _ hready _ ih =>
    have hstep := marginal_le_of_erase_subset hh hx hready
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- Replacing directional costs by row budgets charges each row at most once. -/
theorem Schedule.polymatroid_rows {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (κ : V → ℝ)
    (hκ : ∀ v ∈ W, ∀ x ∈ insert v (recSet M v) ∩ W,
      h (insert v (recSet M v) ∩ W) -
      h ((insert v (recSet M v) ∩ W).erase x) ≤ κ v) :
    h W ≤ h K + ∑ v ∈ (l.map Prod.fst).toFinset, κ v := by
  induction hl with
  | nil hWK => simpa using hh.mono hWK
  | @cons K v x l hv hx _ hready htail ih =>
    have hstep := marginal_le_of_erase_subset hh hx hready
    have hcost := hκ v hv x hx
    have hnot : v ∉ (l.map Prod.fst).toFinset := by
      simpa using htail.center_not_used (by
        intro y hy
        by_cases hyx : y = x
        · simp [hyx]
        · exact mem_insert_of_mem (hready (mem_erase.mpr ⟨hyx, hy⟩)))
    simp only [List.map_cons, List.toFinset_cons, sum_insert hnot]
    linarith

theorem Schedule.polymatroid_all_rows {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (κ : V → ℝ)
    (hκ0 : ∀ v ∈ W, 0 ≤ κ v)
    (hκ : ∀ v ∈ W, ∀ x ∈ insert v (recSet M v) ∩ W,
      h (insert v (recSet M v) ∩ W) -
      h ((insert v (recSet M v) ∩ W).erase x) ≤ κ v) :
    h W ≤ h K + ∑ v ∈ W, κ v := by
  have hsub : (l.map Prod.fst).toFinset ⊆ W := by
    intro v hv
    exact hl.centers_mem v (List.mem_toFinset.mp hv)
  exact (hl.polymatroid_rows hh κ hκ).trans
    (add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg hsub (fun v hv _ => hκ0 v hv)))

/-- Universal row-cost bound. No local reversibility is assumed of `h` here. -/
theorem paid_polymatroid_matching {M : Matrix V V F} {G : SimpleGraph V}
    (htri : RecTriangleFree M) (hstar : ∀ v, Star M v)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u)
    {h : Finset V → ℝ} (hh : IsPolymatroid h)
    (hsingle : ∀ v, h {v} ≤ 1) (κ : V → ℝ) (hκ0 : ∀ v, 0 ≤ κ v)
    (hκ : ∀ v x, x ∈ insert v (recSet M v) →
      h (insert v (recSet M v)) - h ((insert v (recSet M v)).erase x) ≤ κ v) :
    h univ ≤ G.matchingNumber + ∑ v, κ v := by
  obtain ⟨B, l, hcard, hl, _⟩ := exists_matching_schedule htri hstar hpat
  have hpaid := hl.polymatroid_all_rows hh κ (fun v _ => hκ0 v) (by
    simpa only [inter_univ, mem_univ, true_implies] using hκ)
  have hB : h B ≤ B.card := by
    calc h B ≤ ∑ v ∈ B, h {v} := hh.le_sum_singleton B
      _ ≤ ∑ _v ∈ B, (1 : ℝ) := sum_le_sum (fun v _ => hsingle v)
      _ = B.card := by simp
  have hc : (B.card : ℝ) ≤ G.matchingNumber := by exact_mod_cast hcard
  linarith

/-- Exact reversible rules have zero ambiguity cost; no integral rank or
global matroid exchange hypothesis is needed. -/
theorem reversible_polymatroid_matching {M : Matrix V V F} {G : SimpleGraph V}
    (htri : RecTriangleFree M) (hstar : ∀ v, Star M v)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) (hsingle : ∀ v, h {v} ≤ 1)
    (hrev : ∀ v x, x ∈ insert v (recSet M v) →
      h (insert v (recSet M v)) = h ((insert v (recSet M v)).erase x)) :
    h univ ≤ G.matchingNumber := by
  simpa using paid_polymatroid_matching htri hstar hpat hh hsingle (fun _ => 0)
    (fun _ => le_rfl) (fun v x hx => by rw [hrev v x hx]; simp)

end SubcubicMemo
