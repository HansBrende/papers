import DirectedReciprocity.ClassS
import HalfRate.Limits

/-!
# Sharpness constructions: `X₁₅`'s minimum core and the `Class S` digraph `G₂₁` (`Proposition G21`)

1. **`X₁₅` minimum-core obstruction (`x15_hexagon_no_pieceCert`)**: Combining `HalfRate.x15_cores`
   (whose unique minimum nonempty core is `{0, 1, 2, 3, 4, 5}`) with `stride3_no_pieceCert`
   certifies over **unbounded** record counts `m` that `X₁₅`'s unique minimum nonempty core admits
   no `PieceCert`, formally closing the unbounded-`m` numerical claim of Open Problem 6 of
   *Nested Elimination and Half-Rate Bounds for Storage Codes*.
2. **Proposition G21 (`g21Rel`)**: An explicit `21`-vertex strongly connected triangle-free
   recovery relation in `Class S` (`IsClassS g21Rel`) built from three disjoint digon `6`-cycles
   `hexA = {0..5}`, `hexB = {6..11}`, `hexC = {12..17}` coupled to three in-degree-`2` hubs
   `18, 19, 20` via `6` digons and `12` one-way stride-`3` arcs:
   * Every vertex has in-degree `2` or `3`, and `W = {18, 19, 20}` is an independent set
     (`IsAcyclicIn g21Rel W`), so Theorem T's low-in-degree and `W`-cycle rules cannot apply.
   * Every shortest cycle of `digonGraph g21Rel` has length `6` and is one of `hexA`, `hexB`, or
     `hexC` (`g21_shortest_digon_cycles`), and **none** of `hexA`, `hexB`, `hexC` admits a
     `PieceCert` over any record count `m` (`g21_hex_no_pieceCert`), so Theorem N3's
     shortest-digon-cycle rule also stalls.
   * Nevertheless, Theorem S\* (`rateBound_classS`) decomposes `g21Rel` (via the `7`-vertex
     hub-augmented piece `{18, 0, 1, 2, 3, 4, 5}`) and proves `RateBound g21Rel (1 / 2)`.
-/

namespace DirectedReciprocity

open Finset HalfRate MotionDepthCodes SimpleGraph

section X15Core

/-- The unique minimum nonempty core `{0, 1, 2, 3, 4, 5}` of `HalfRate.x15` admits **no**
`PieceCert` over **any** number of records `m : ℕ`. -/
theorem x15_hexagon_no_pieceCert :
    ¬ Nonempty (PieceCert x15 ∅ ({0, 1, 2, 3, 4, 5} : Finset (Fin 15))) := by
  let f : Fin (3 * 2) → Fin 15 := ![0, 1, 2, 3, 4, 5]
  let w : Fin 3 → Fin 15 := ![6, 7, 8]
  refine stride3_no_pieceCert (N := x15) (U := ∅) (H := {0, 1, 2, 3, 4, 5})
    (disjoint_empty_left _) (by decide) f (by decide) (by decide) w (by decide)
    (by decide) (by decide)

end X15Core

section G21

/-- The `21`-vertex strongly connected triangle-free `Class S` recovery relation `G₂₁`. -/
def g21Rel : Fin 21 → Finset (Fin 21) :=
  ![ -- `hexA = {0..5}`
    {5, 1, 18}, {0, 2, 19}, {1, 3, 20}, {2, 4, 18}, {3, 5, 19}, {4, 0, 20},
     -- `hexB = {6..11}`
    {11, 7, 18}, {6, 8, 19}, {7, 9, 20}, {8, 10, 18}, {9, 11, 19}, {10, 6, 20},
     -- `hexC = {12..17}`
    {17, 13, 18}, {12, 14, 19}, {13, 15, 20}, {14, 16, 18}, {15, 17, 19}, {16, 12, 20},
     -- hubs `18, 19, 20`
    {0, 15}, {1, 7}, {8, 14} ]

def hexA : Finset (Fin 21) := {0, 1, 2, 3, 4, 5}
def hexB : Finset (Fin 21) := {6, 7, 8, 9, 10, 11}
def hexC : Finset (Fin 21) := {12, 13, 14, 15, 16, 17}

/-- `G₂₁` belongs to `Class S`. -/
theorem g21_isClassS : IsClassS g21Rel := by
  decide

private def g21HasAnyTriangleBool : Bool :=
  (List.finRange 21).any fun x =>
    (List.finRange 21).any fun y =>
      (List.finRange 21).any fun z =>
        !(x == y) && !(y == z) && !(x == z) &&
          (decide (x ∈ g21Rel y) || decide (y ∈ g21Rel x)) &&
          (decide (y ∈ g21Rel z) || decide (z ∈ g21Rel y)) &&
          (decide (x ∈ g21Rel z) || decide (z ∈ g21Rel x))

private theorem g21HasAnyTriangleBool_false : g21HasAnyTriangleBool = false := by
  decide +kernel

/-- The underlying undirected support of `G₂₁` is completely triangle-free (no three distinct
vertices have arcs between all three pairs in any orientation). -/
theorem g21_no_any_triangle :
    ∀ x y z : Fin 21, x ≠ y → y ≠ z → x ≠ z →
      (x ∈ g21Rel y ∨ y ∈ g21Rel x) →
      (y ∈ g21Rel z ∨ z ∈ g21Rel y) →
      (x ∈ g21Rel z ∨ z ∈ g21Rel x) → False := by
  intro x y z hxy hyz hxz h1 h2 h3
  have ht : g21HasAnyTriangleBool = true := by
    unfold g21HasAnyTriangleBool
    simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq]
    exact ⟨x, y, z, ⟨⟨⟨⟨⟨by simp [hxy], by simp [hyz]⟩, by simp [hxz]⟩, h1⟩, h2⟩, h3⟩⟩
  rw [g21HasAnyTriangleBool_false] at ht
  cases ht

/-- Every vertex of `G₂₁` has in-degree at least `2`, and the in-degree-`2` set `{18, 19, 20}`
has no internal arcs (hence is `g21Rel`-acyclic). -/
theorem g21_min_indeg_and_acyclic_W :
    (∀ v : Fin 21, 2 ≤ (g21Rel v).card) ∧
    IsAcyclicIn g21Rel (univ.filter (fun v : Fin 21 => (g21Rel v).card = 2)) := by
  refine ⟨by decide, ?_⟩
  have hW : univ.filter (fun v : Fin 21 => (g21Rel v).card = 2) = {18, 19, 20} := by decide
  rw [hW]
  intro T hT hne
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, hv, fun u hu huT => ?_⟩
  have hvW := hT hv
  have huW := hT huT
  revert v u hvW huW hu
  decide +revert

/-- `G₂₁` is strongly connected (`∀ u v, Reaches g21Rel u v`). -/
theorem g21_stronglyConnected : ∀ u v : Fin 21, Reaches g21Rel u v := by
  let w : Fin 32 → Fin 21 :=
    ![0, 1, 2, 3, 4, 5, 0, 18, 6, 7, 8, 9, 10, 11, 6, 7, 19, 1, 0, 18, 15, 16, 17, 12, 13, 14,
      20, 8, 7, 19, 1, 0]
  have hw_step : ∀ i : Fin 31, w ⟨i.val, by omega⟩ ∈ g21Rel (w ⟨i.val + 1, by omega⟩) := by
    decide
  have hw_surj : ∀ v : Fin 21, ∃ i : Fin 32, w i = v := by decide
  have hw_reach : ∀ (i j : ℕ) (hij : i ≤ j) (hj : j < 32),
      Reaches g21Rel (w ⟨i, by omega⟩) (w ⟨j, hj⟩) := by
    intro i j hij hj
    induction j with
    | zero =>
      have hi0 : i = 0 := by omega
      subst hi0; exact Relation.ReflTransGen.refl
    | succ j ih =>
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact Relation.ReflTransGen.refl
      · exact (ih (by omega) (by omega)).tail (hw_step ⟨j, by omega⟩)
  intro u v
  obtain ⟨iu, rfl⟩ := hw_surj u
  obtain ⟨iv, rfl⟩ := hw_surj v
  have hu_end : Reaches g21Rel (w iu) (w ⟨31, by decide⟩) :=
    hw_reach iu.val 31 (by omega) (by decide)
  have hstart_v : Reaches g21Rel (w ⟨0, by decide⟩) (w iv) :=
    hw_reach 0 iv.val (Nat.zero_le _) iv.isLt
  have hend_eq : w ⟨31, by decide⟩ = w ⟨0, by decide⟩ := by decide
  rw [hend_eq] at hu_end
  exact hu_end.trans hstart_v

/-- None of the three `6`-cycle cores `hexA`, `hexB`, `hexC` of `G₂₁` admits a `PieceCert` over
any number of records `m : ℕ`. -/
theorem g21_hex_no_pieceCert :
    ¬ Nonempty (PieceCert g21Rel ∅ hexA) ∧
    ¬ Nonempty (PieceCert g21Rel ∅ hexB) ∧
    ¬ Nonempty (PieceCert g21Rel ∅ hexC) := by
  let w : Fin 3 → Fin 21 := ![18, 19, 20]
  refine ⟨?_, ?_, ?_⟩
  · let fA : Fin (3 * 2) → Fin 21 := ![0, 1, 2, 3, 4, 5]
    exact stride3_no_pieceCert (N := g21Rel) (U := ∅) (H := hexA)
      (disjoint_empty_left _) (by decide) fA
      (by decide) (by decide) w (by decide) (by decide) (by decide)
  · let fB : Fin (3 * 2) → Fin 21 := ![6, 7, 8, 9, 10, 11]
    exact stride3_no_pieceCert (N := g21Rel) (U := ∅) (H := hexB)
      (disjoint_empty_left _) (by decide) fB
      (by decide) (by decide) w (by decide) (by decide) (by decide)
  · let fC : Fin (3 * 2) → Fin 21 := ![12, 13, 14, 15, 16, 17]
    exact stride3_no_pieceCert (N := g21Rel) (U := ∅) (H := hexC)
      (disjoint_empty_left _) (by decide) fC
      (by decide) (by decide) w (by decide) (by decide) (by decide)

private def g21CompOf (v : Fin 21) : Fin 4 :=
  if v.val < 6 then 0
  else if v.val < 12 then 1
  else if v.val < 18 then 2
  else 3

private def g21DigAdjBool (u v : Fin 21) : Bool :=
  decide ((digonGraph g21Rel).Adj u v)

/-- Pure `Bool` BFS step avoiding `forbid`: tests whether `dst` is reachable from `frontier` in
at most `steps` edges of `digonGraph g21Rel` without visiting `forbid`. -/
private def reachAvoidAux (forbid dst : Fin 21) : ℕ → List (Fin 21) → Bool
  | 0, frontier => frontier.contains dst
  | k + 1, frontier =>
    frontier.contains dst ||
      let next := (List.finRange 21).filter fun z =>
        !(z == forbid) && frontier.any (fun x => g21DigAdjBool x z)
      reachAvoidAux forbid dst k next

private theorem reachAvoidAux_mono {forbid dst : Fin 21} :
    ∀ (k : ℕ) {f₁ f₂ : List (Fin 21)}, (∀ x ∈ f₁, x ∈ f₂) →
      reachAvoidAux forbid dst k f₁ = true → reachAvoidAux forbid dst k f₂ = true
  | 0, f₁, f₂, hsub, h => by
    simp only [reachAvoidAux, List.contains_iff_mem] at h ⊢
    exact hsub _ h
  | k + 1, f₁, f₂, hsub, h => by
    unfold reachAvoidAux at h ⊢
    rw [Bool.or_eq_true] at h ⊢
    rcases h with h1 | h2
    · left
      simp only [List.contains_iff_mem] at h1 ⊢
      exact hsub _ h1
    · right
      refine reachAvoidAux_mono k ?_ h2
      intro z hz
      simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
        List.any_eq_true] at hz ⊢
      obtain ⟨hneq, x, hx1, hadj⟩ := hz
      exact ⟨hneq, x, hsub x hx1, hadj⟩

private theorem reachAvoidAux_walk {forbid : Fin 21} :
    ∀ {m : ℕ} (p : ℕ → Fin 21),
      (∀ t ≤ m, p t ≠ forbid) →
      (∀ t < m, (digonGraph g21Rel).Adj (p t) (p (t + 1))) →
      reachAvoidAux forbid (p m) m [p 0] = true
  | 0, p, _, _ => by simp [reachAvoidAux]
  | m + 1, p, hforb, hadj => by
    unfold reachAvoidAux
    rw [Bool.or_eq_true]; right
    have hp1 : p 1 ∈ (List.finRange 21).filter (fun z =>
        !(z == forbid) && [p 0].any (fun x => g21DigAdjBool x z)) := by
      simp [g21DigAdjBool, hforb 1 (by omega), hadj 0 (by omega)]
    exact reachAvoidAux_mono m (fun z hz => by
      rw [List.mem_singleton.mp hz]; exact hp1)
      (reachAvoidAux_walk (fun t => p (t + 1))
        (fun t ht => hforb (t + 1) (by omega))
        (fun t ht => hadj (t + 1) (by omega)))

private def g21HubBypassCheck : Bool :=
  (List.finRange 21).all fun w =>
    !(g21CompOf w == 3) ||
      (List.finRange 21).all fun u =>
        (List.finRange 21).all fun v =>
          !(g21DigAdjBool w u) || !(g21DigAdjBool w v) || (u == v) ||
            !(reachAvoidAux w u 4 [v])

private theorem g21HubBypassCheck_true : g21HubBypassCheck = true := by
  decide +kernel

private theorem g21_hub_no_short_bypass :
    ∀ w u v : Fin 21, g21CompOf w = 3 →
      g21DigAdjBool w u = true → g21DigAdjBool w v = true → !(u == v) = true →
      reachAvoidAux w u 4 [v] = false := by
  intro w u v hw hu hv huv
  have hc := g21HubBypassCheck_true
  unfold g21HubBypassCheck at hc
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at hc
  have h1 := hc w
  simp only [hw, BEq.rfl, Bool.not_true, Bool.false_or, List.all_eq_true,
    List.mem_finRange, forall_const] at h1
  have h2 := h1 u v
  have huv_f : (u == v) = false := by revert huv; cases (u == v) <;> simp
  simp [hu, hv, huv_f] at h2
  exact h2

private theorem g21_digon_comp_step :
    ∀ u v : Fin 21, (digonGraph g21Rel).Adj u v →
      (g21CompOf u = g21CompOf v ∧ g21CompOf u ≠ 3) ∨
      (g21CompOf u = 3 ∧ g21CompOf v ≠ 3) ∨
      (g21CompOf u ≠ 3 ∧ g21CompOf v = 3) := by
  decide

private theorem g21_hex_local_adj :
    ∀ (comp : Fin 4), comp ≠ 3 →
      ∀ u v : Fin 21, g21CompOf u = comp → g21CompOf v ≠ 3 → (digonGraph g21Rel).Adj u v →
        g21CompOf v = comp ∧
        ((u.val % 6 + 1) % 6 = v.val % 6 ∨ (v.val % 6 + 1) % 6 = u.val % 6) := by
  decide

/-- Every cycle of `digonGraph g21Rel` of length `g ≤ 6` (`g ≥ 3`) has length `6` and vertex set
equal to `hexA`, `hexB`, or `hexC` (so every shortest digon cycle of `G₂₁` fails `PieceCert`). -/
theorem g21_shortest_digon_cycles {g : ℕ} (hg3 : 3 ≤ g) (hg6 : g ≤ 6)
    (c : CycIn (digonGraph g21Rel) univ g) :
    g = 6 ∧ (univ.image c.f = hexA ∨ univ.image c.f = hexB ∨ univ.image c.f = hexC) := by
  have hg0 : 0 < g := by omega
  have hno_hub : ∀ i : Fin g, g21CompOf (c.f i) ≠ 3 := by
    intro i hi3
    let prev : Fin g := idx hg0 (i.val + g - 1)
    let next : Fin g := idx hg0 (i.val + 1)
    have hprev_adj : (digonGraph g21Rel).Adj (c.f i) (c.f prev) := by
      have h := c.arc_adj hg3 (i.val + g - 1)
      have hidx : idx hg0 (i.val + g - 1 + 1) = i := by
        apply Fin.ext; simp only [idx_val, show i.val + g - 1 + 1 = g + i.val by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
      rw [hidx] at h
      exact h.symm
    have hnext_adj : (digonGraph g21Rel).Adj (c.f i) (c.f next) := by
      have h := c.arc_adj hg3 i.val
      rwa [idx_self] at h
    have hpn_ne : c.f prev ≠ c.f next := by
      intro e
      have hev := congrArg Fin.val (c.inj e)
      simp only [prev, next, idx_val] at hev
      have hi := i.isLt
      by_cases hi0 : i.val = 0
      · rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hev
        omega
      · rw [show i.val + g - 1 = g + (i.val - 1) by omega, Nat.add_mod_left] at hev
        rw [Nat.mod_eq_of_lt (by omega)] at hev
        by_cases hil : i.val + 1 = g
        · rw [hil, Nat.mod_self] at hev; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hev; omega
    let p : ℕ → Fin 21 := fun t => c.f (idx hg0 (i.val + 1 + t))
    have hp_forb : ∀ t ≤ g - 2, p t ≠ c.f i := by
      intro t ht e
      have hev := c.arc_inj hg0 (a := i.val) (s := 1 + t) (t := 0) (d := g - 1)
        (by omega) (by omega) (by omega)
        (by simpa [p, Nat.add_assoc, idx_self] using e)
      omega
    have hp_adj : ∀ t < g - 2, (digonGraph g21Rel).Adj (p t) (p (t + 1)) := by
      intro t _
      simpa [p, Nat.add_assoc] using c.arc_adj hg3 (i.val + 1 + t)
    have hwalk : reachAvoidAux (c.f i) (c.f prev) (g - 2) [c.f next] = true := by
      have hw := reachAvoidAux_walk p hp_forb hp_adj
      have hp0 : p 0 = c.f next := rfl
      have hpend : p (g - 2) = c.f prev := by
        simp only [p, prev]
        congr 1; apply Fin.ext; simp only [idx_val]
        rw [show i.val + 1 + (g - 2) = i.val + g - 1 by omega]
      rwa [hp0, hpend] at hw
    -- Lift `reachAvoidAux ... (g - 2)` (`g - 2 ≤ 4`) to `4`!
    have hle4 : ∀ k ≤ 4, ∀ fr, reachAvoidAux (c.f i) (c.f prev) k fr = true →
        reachAvoidAux (c.f i) (c.f prev) 4 fr = true := by
      intro k hk fr hr
      -- If `reachAvoidAux w dst k fr = true` then `reachAvoidAux w dst (k + 1) fr = true`!
      have hup : ∀ m fr', reachAvoidAux (c.f i) (c.f prev) m fr' = true →
          reachAvoidAux (c.f i) (c.f prev) (m + 1) fr' = true := by
        intro m
        induction m with
        | zero => intro fr' h0; simp [reachAvoidAux] at h0; simp [reachAvoidAux, h0]
        | succ m ih =>
          intro fr' hm
          unfold reachAvoidAux at hm ⊢
          rw [Bool.or_eq_true] at hm ⊢
          rcases hm with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (ih _ h2)
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · exact hup 3 _ (hup 2 _ (hup 1 _ (hup 0 _ hr)))
      · exact hup 3 _ (hup 2 _ (hup 1 _ hr))
      · exact hup 3 _ (hup 2 _ hr)
      · exact hup 3 _ hr
      · exact hr
    have htrue4 := hle4 (g - 2) (by omega) [c.f next] hwalk
    have hfalse4 := g21_hub_no_short_bypass (c.f i) (c.f prev) (c.f next) hi3
      (decide_eq_true hprev_adj) (decide_eq_true hnext_adj) (by simp [hpn_ne])
    rw [hfalse4] at htrue4
    cases htrue4
  have hcomp_const : ∀ t : ℕ, g21CompOf (c.f (idx hg0 t)) = g21CompOf (c.f ⟨0, hg0⟩) := by
    intro t
    induction t with
    | zero => simp [idx_of_lt hg0 hg0]
    | succ t ih =>
      have hadj := c.arc_adj hg3 t
      rcases g21_digon_comp_step _ _ hadj with ⟨heq, -⟩ | ⟨h3, -⟩ | ⟨-, h3⟩
      · exact heq.symm.trans ih
      · exact absurd h3 (hno_hub _)
      · exact absurd h3 (hno_hub _)
  have hall_comp : ∀ i : Fin g, g21CompOf (c.f i) = g21CompOf (c.f ⟨0, hg0⟩) := by
    intro i; simpa [idx_self] using hcomp_const i.val
  -- Map `c` into the `6`-cycle on `Fin 6` via `v ↦ v.val % 6`: injective on each hexagon component!
  have hinj_mod6 : ∀ u v : Fin 21, g21CompOf u = g21CompOf v → g21CompOf u ≠ 3 →
      u.val % 6 = v.val % 6 → u = v := by
    decide
  have hmod_step : ∀ i : Fin g,
      ((c.f i).val % 6 + 1) % 6 = (c.f (idx hg0 (i.val + 1))).val % 6 ∨
      ((c.f (idx hg0 (i.val + 1))).val % 6 + 1) % 6 = (c.f i).val % 6 := by
    intro i
    have hadj := c.arc_adj hg3 i.val
    rw [idx_self] at hadj
    exact (g21_hex_local_adj _ (hno_hub ⟨0, hg0⟩) _ _ (hall_comp i) (hno_hub _) hadj).2
  -- An injective closed walk on `C_6` (`g ≥ 3`, `g ≤ 6`) MUST have `g = 6`:
  -- Parity rules out `g = 3` and `g = 5`; and on `Z_6`, any 4-cycle `a0 - a1 - a2 - a3 - a0`
  -- with step `±1 mod 6` has two opposite vertices equal (`a0 = a2` or `a1 = a3`), contradicting `c.inj`!
  have hg_eq6 : g = 6 := by
    rcases (show g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 by omega) with rfl | rfl | rfl | rfl
    · exfalso
      have s0 := hmod_step 0; have s1 := hmod_step 1; have s2 := hmod_step 2
      change ((c.f 0).val % 6 + 1) % 6 = (c.f 1).val % 6 ∨ ((c.f 1).val % 6 + 1) % 6 = (c.f 0).val % 6 at s0
      change ((c.f 1).val % 6 + 1) % 6 = (c.f 2).val % 6 ∨ ((c.f 2).val % 6 + 1) % 6 = (c.f 1).val % 6 at s1
      change ((c.f 2).val % 6 + 1) % 6 = (c.f 0).val % 6 ∨ ((c.f 0).val % 6 + 1) % 6 = (c.f 2).val % 6 at s2
      omega
    · exfalso
      have s0 := hmod_step 0; have s1 := hmod_step 1; have s2 := hmod_step 2; have s3 := hmod_step 3
      change ((c.f 0).val % 6 + 1) % 6 = (c.f 1).val % 6 ∨ ((c.f 1).val % 6 + 1) % 6 = (c.f 0).val % 6 at s0
      change ((c.f 1).val % 6 + 1) % 6 = (c.f 2).val % 6 ∨ ((c.f 2).val % 6 + 1) % 6 = (c.f 1).val % 6 at s1
      change ((c.f 2).val % 6 + 1) % 6 = (c.f 3).val % 6 ∨ ((c.f 3).val % 6 + 1) % 6 = (c.f 2).val % 6 at s2
      change ((c.f 3).val % 6 + 1) % 6 = (c.f 0).val % 6 ∨ ((c.f 0).val % 6 + 1) % 6 = (c.f 3).val % 6 at s3
      have hne02 : (c.f 0).val % 6 ≠ (c.f 2).val % 6 := fun e => by
        have := c.inj (hinj_mod6 _ _ ((hall_comp 0).trans (hall_comp 2).symm)
          (by rw [hall_comp 0]; exact hno_hub 0) e)
        revert this; decide
      have hne13 : (c.f 1).val % 6 ≠ (c.f 3).val % 6 := fun e => by
        have := c.inj (hinj_mod6 _ _ ((hall_comp 1).trans (hall_comp 3).symm)
          (by rw [hall_comp 1]; exact hno_hub 0) e)
        revert this; decide
      omega
    · exfalso
      have s0 := hmod_step 0; have s1 := hmod_step 1; have s2 := hmod_step 2
      have s3 := hmod_step 3; have s4 := hmod_step 4
      change ((c.f 0).val % 6 + 1) % 6 = (c.f 1).val % 6 ∨ ((c.f 1).val % 6 + 1) % 6 = (c.f 0).val % 6 at s0
      change ((c.f 1).val % 6 + 1) % 6 = (c.f 2).val % 6 ∨ ((c.f 2).val % 6 + 1) % 6 = (c.f 1).val % 6 at s1
      change ((c.f 2).val % 6 + 1) % 6 = (c.f 3).val % 6 ∨ ((c.f 3).val % 6 + 1) % 6 = (c.f 2).val % 6 at s2
      change ((c.f 3).val % 6 + 1) % 6 = (c.f 4).val % 6 ∨ ((c.f 4).val % 6 + 1) % 6 = (c.f 3).val % 6 at s3
      change ((c.f 4).val % 6 + 1) % 6 = (c.f 0).val % 6 ∨ ((c.f 0).val % 6 + 1) % 6 = (c.f 4).val % 6 at s4
      omega
    · rfl
  subst hg_eq6
  refine ⟨rfl, ?_⟩
  have hcard_img : (univ.image c.f).card = 6 := by
    rw [card_image_of_injective _ c.inj, card_univ, Fintype.card_fin]
  have hcomp_cases : g21CompOf (c.f 0) = 0 ∨ g21CompOf (c.f 0) = 1 ∨ g21CompOf (c.f 0) = 2 := by
    have hne3 := hno_hub 0
    generalize g21CompOf (c.f 0) = k at hne3 ⊢
    revert k hne3; decide
  rcases hcomp_cases with h0 | h1 | h2
  · left
    have hsub : univ.image c.f ⊆ hexA := by
      intro v hv
      obtain ⟨i, -, rfl⟩ := mem_image.mp hv
      have hc := (hall_comp i).trans h0
      revert hc; generalize c.f i = x; revert x; decide
    exact eq_of_subset_of_card_le hsub (by rw [hcard_img]; decide)
  · right; left
    have hsub : univ.image c.f ⊆ hexB := by
      intro v hv
      obtain ⟨i, -, rfl⟩ := mem_image.mp hv
      have hc := (hall_comp i).trans h1
      revert hc; generalize c.f i = x; revert x; decide
    exact eq_of_subset_of_card_le hsub (by rw [hcard_img]; decide)
  · right; right
    have hsub : univ.image c.f ⊆ hexC := by
      intro v hv
      obtain ⟨i, -, rfl⟩ := mem_image.mp hv
      have hc := (hall_comp i).trans h2
      revert hc; generalize c.f i = x; revert x; decide
    exact eq_of_subset_of_card_le hsub (by rw [hcard_img]; decide)

/-- **Proposition G21 (half-rate bound and sharpness of shortest-digon-cycle rules on `Class S`).**
`g21Rel` belongs to `Class S`, is strongly connected and triangle-free, has no shortest digon cycle
that is a certified piece, and yet satisfies `RateBound g21Rel (1 / 2)` by Theorem S\*. -/
theorem rateBound_g21 : RateBound g21Rel (1 / 2) :=
  rateBound_classS g21_isClassS

end G21

end DirectedReciprocity
