import SubcubicMemo.ReversibleRules

/-! Productive derivations use every center at most once. -/

namespace SubcubicMemo

open Finset MotionDepthCodes

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F] [DecidableEq F]

/-- A productive schedule. At the end every vertex of `W` is known. -/
inductive Schedule (M : Matrix V V F) (W : Finset V) : Finset V → List (V × V) → Prop
  | nil {K} : W ⊆ K → Schedule M W K []
  | cons {K v x l} : v ∈ W → x ∈ insert v (recSet M v) ∩ W → x ∉ K →
      (insert v (recSet M v) ∩ W).erase x ⊆ K →
      Schedule M W (insert x K) l → Schedule M W K ((v, x) :: l)

/-- A derivable but still unknown vertex exposes a productive rule. -/
theorem Derivable.exists_ready {M : Matrix V V F} {W B K : Finset V}
    (hBK : B ⊆ K) {x : V} (hx : Derivable M W B x) (hxK : x ∉ K) :
    ∃ v y, v ∈ W ∧ y ∈ insert v (recSet M v) ∩ W ∧ y ∉ K ∧
      (insert v (recSet M v) ∩ W).erase y ⊆ K := by
  induction hx with
  | seed hx => exact False.elim (hxK (hBK hx))
  | @rule v x hv hx _ ih =>
    by_cases hp : (insert v (recSet M v) ∩ W).erase x ⊆ K
    · exact ⟨v, x, hv, hx, hxK, hp⟩
    · obtain ⟨y, hy, hyK⟩ := not_subset.mp hp
      obtain ⟨hyx, hyr⟩ := mem_erase.mp hy
      exact ih y hyr hyx hyK

theorem Generates.exists_schedule {M : Matrix V V F} {W B : Finset V}
    (hB : Generates M W B) : ∃ l, Schedule M W B l := by
  have build : ∀ n, ∀ K : Finset V, B ⊆ K → K ⊆ W → W.card - K.card = n →
      ∃ l, Schedule M W K l := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hBK hKW hn
      by_cases hWK : W ⊆ K
      · exact ⟨[], .nil hWK⟩
      · obtain ⟨x, hxW, hxK⟩ := not_subset.mp hWK
        obtain ⟨v, y, hv, hyr, hyK, hready⟩ :=
          (hB.2 x hxW).exists_ready hBK hxK
        have hyW := (mem_inter.mp hyr).2
        have hKW' : insert y K ⊆ W := insert_subset hyW hKW
        have hcount := card_insert_of_notMem hyK
        have hbound := card_le_card hKW'
        obtain ⟨l, hl⟩ := ih (W.card - (insert y K).card) (by omega) (insert y K)
          (hBK.trans (subset_insert _ _)) hKW' rfl
        exact ⟨(v, y) :: l, .cons hv hyr hyK hready hl⟩
  exact build _ B (subset_refl _) hB.1 rfl

/-- Once all members of a row are known, that center can never be productive. -/
theorem Schedule.center_not_used {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l) {v : V}
    (hv : insert v (recSet M v) ∩ W ⊆ K) : v ∉ l.map Prod.fst := by
  induction hl with
  | nil => simp
  | @cons K u x l hu hx hxK _ _ ih =>
    simp only [List.map_cons, List.mem_cons, not_or]
    refine ⟨?_, ih (hv.trans (subset_insert _ _))⟩
    intro h
    subst u
    exact hxK (hv hx)

/-- No center occurs twice, in any productive schedule, with no graph premise. -/
theorem Schedule.centers_nodup {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l) : (l.map Prod.fst).Nodup := by
  induction hl with
  | nil => simp
  | @cons K v x l _ hx _ hready htail ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨htail.center_not_used ?_, ih⟩
    intro y hy
    by_cases hyx : y = x
    · simp [hyx]
    · exact mem_insert_of_mem (hready (mem_erase.mpr ⟨hyx, hy⟩))

theorem Schedule.centers_mem {M : Matrix V V F} {W K : Finset V}
    {l : List (V × V)} (hl : Schedule M W K l) : ∀ v ∈ l.map Prod.fst, v ∈ W := by
  induction hl with
  | nil => simp
  | cons hv _ _ _ _ ih =>
    intro v hvlist
    simp only [List.map_cons, List.mem_cons] at hvlist
    rcases hvlist with rfl | hvlist
    · exact hv
    · exact ih v hvlist

/-- A single-use schedule chosen from the supports before observing a codeword. -/
theorem exists_matching_schedule {M : Matrix V V F} {G : SimpleGraph V}
    (htri : RecTriangleFree M) (hstar : ∀ v, Star M v)
    (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u) :
    ∃ B : Finset V, ∃ l : List (V × V), B.card ≤ G.matchingNumber ∧
      Schedule M univ B l ∧ (l.map Prod.fst).Nodup := by
  obtain ⟨B, hB, hcard⟩ := exists_generators_matching htri hstar hpat
  obtain ⟨l, hl⟩ := hB.exists_schedule
  exact ⟨B, l, hcard, hl, hl.centers_nodup⟩

end SubcubicMemo
