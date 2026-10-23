import TransposeFollowup.AdaptiveForestPaths
import Mathlib.Data.Nat.ModEq
import Mathlib.Combinatorics.Pigeonhole

/-! Public depth-residue cuts and their bounded-height ancestor labels. -/

namespace TransposeFollowup.AdaptiveForest

open Classical
set_option autoImplicit false

/-- The last cut depth, or zero before the first cut. -/
def cutIndex (R r t : ℕ) : ℕ := t - ((t + R - r) % R)

theorem cutIndex_le (R r t : ℕ) : cutIndex R r t ≤ t := Nat.sub_le _ _

theorem cutIndex_remainder_lt {R : ℕ} (hR : 0 < R) (r t : ℕ) :
    t - cutIndex R r t < R := by
  have hm := Nat.mod_lt (t + R - r) hR
  unfold cutIndex
  omega

theorem shifted_residue_zero_iff {R r : ℕ} (hr : r < R) (t : ℕ) :
    (t + R - r) % R = 0 ↔ t % R = r := by
  constructor
  · intro h
    have hz : Nat.ModEq R (t + R - r) 0 := h
    have ha := hz.add_right r
    change (t + R - r + r) % R = (0 + r) % R at ha
    rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right,
      Nat.zero_add, Nat.mod_eq_of_lt hr] at ha
    exact ha
  · intro h
    have hz : Nat.ModEq R t r := by
      change t % R = r % R
      rwa [Nat.mod_eq_of_lt hr]
    have ha := hz.add_right (R - r)
    change (t + (R - r)) % R = (r + (R - r)) % R at ha
    rw [Nat.add_sub_of_le hr.le, Nat.mod_self] at ha
    simpa [Nat.add_sub_assoc hr.le] using ha

theorem cutIndex_succ_of_not_cut {R r : ℕ} (hR : 0 < R) (hr : r < R)
    (t : ℕ) (hn : (t + 1) % R ≠ r) :
    cutIndex R r (t + 1) = cutIndex R r t := by
  have hz : (t + 1 + R - r) % R ≠ 0 :=
    mt (shifted_residue_zero_iff hr (t + 1)).mp hn
  have hR2 : 1 < R := by
    by_contra h
    have he : R = 1 := by omega
    apply hz
    rw [he]
    exact Nat.mod_one _
  have hmod := Nat.mod_lt (t + R - r) hR
  have he : t + 1 + R - r = (t + R - r) + 1 := by omega
  have hlo : (t + R - r) % R + 1 < R := by
    by_contra h
    have hh : (t + R - r) % R + 1 = R := by omega
    have hh' : ((t + R - r) + 1) % R = 0 := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt hR2, hh, Nat.mod_self]
    exact hz (he ▸ hh')
  have hs : (t + 1 + R - r) % R = (t + R - r) % R + 1 := by
    rw [he]
    simpa [Nat.mod_eq_of_lt hR2] using
      (Nat.add_mod_of_add_mod_lt (a := t + R - r) (b := 1) (c := R)
        (by simpa [Nat.mod_eq_of_lt hR2] using hlo))
  simp only [cutIndex, hs, Nat.add_sub_add_right]

variable {V : Type*} (G : SimpleGraph V)

noncomputable def ancestor (R r : ℕ) (v : V) : V :=
  (path G v).getVert (cutIndex R r (depth G v))

theorem ancestor_near (R r : ℕ) (hR : 0 < R) (v : V) :
    GraphNear G R (ancestor G R r v) v := by
  dsimp only [ancestor]
  refine ⟨(path G v).drop (cutIndex R r (depth G v)), ?_⟩
  rw [SimpleGraph.Walk.drop_length]
  exact cutIndex_remainder_lt hR r (depth G v)

theorem ancestor_eq_of_support_extend {R r : ℕ} (hR : 0 < R) (hr : r < R)
    {v w : V} (he : (path G w).support = (path G v).support ++ [w])
    (hn : depth G w % R ≠ r) : ancestor G R r v = ancestor G R r w := by
  have hd : depth G w = depth G v + 1 := by
    have hl := congrArg List.length he
    simp only [SimpleGraph.Walk.length_support, List.length_append,
      List.length_singleton] at hl
    dsimp [depth]
    omega
  have hc : cutIndex R r (depth G w) = cutIndex R r (depth G v) := by
    rw [hd]
    exact cutIndex_succ_of_not_cut hR hr _ (hd ▸ hn)
  have hv := cutIndex_le R r (depth G v)
  have hw : cutIndex R r (depth G v) ≤ (path G w).length := by
    change cutIndex R r (depth G v) ≤ depth G w
    omega
  unfold ancestor
  rw [hc]
  apply Option.some.inj
  rw [(path G v).getVert_eq_support_getElem? hv,
    (path G w).getVert_eq_support_getElem? hw, he,
    List.getElem?_append_left (by rw [SimpleGraph.Walk.length_support]; exact Nat.lt_add_one_of_le hv)]

noncomputable def pins [Fintype V] (R r : ℕ) : Finset V :=
  Finset.univ.filter (fun v => 0 < depth G v ∧ depth G v % R = r)

@[simp] theorem mem_pins [Fintype V] (R r : ℕ) (v : V) :
    v ∈ pins G R r ↔ 0 < depth G v ∧ depth G v % R = r := by
  simp [pins]

theorem ancestor_eq_of_adj_not_pinned [Fintype V]
    (hG : G.IsAcyclic) {R r : ℕ} (hR : 0 < R) (hr : r < R)
    {v w : V} (hv : v ∉ pins G R r) (hw : w ∉ pins G R r)
    (hvw : G.Adj v w) : ancestor G R r v = ancestor G R r w := by
  rcases support_extend_of_adj G hG hvw with he | he
  · apply ancestor_eq_of_support_extend G hR hr he
    intro hc
    apply hw
    apply (mem_pins G R r w).mpr
    refine ⟨?_, hc⟩
    have hl := congrArg List.length he
    simp only [SimpleGraph.Walk.length_support, List.length_append,
      List.length_singleton] at hl
    dsimp [depth]
    omega
  · symm
    apply ancestor_eq_of_support_extend G hR hr he
    intro hc
    apply hv
    apply (mem_pins G R r v).mpr
    refine ⟨?_, hc⟩
    have hl := congrArg List.length he
    simp only [SimpleGraph.Walk.length_support, List.length_append,
      List.length_singleton] at hl
    dsimp [depth]
    omega

theorem same_ancestor_near {R r : ℕ} (hR : 0 < R) {v w : V}
    (h : ancestor G R r v = ancestor G R r w) : GraphNear G (2 * R - 1) v w := by
  obtain ⟨p, hp⟩ := ancestor_near G R r hR v
  have hw := ancestor_near G R r hR w
  rw [← h] at hw
  obtain ⟨q, hq⟩ := hw
  refine ⟨p.reverse.append q, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

theorem forest_along_ancestor [Fintype V]
    (p : PublicProtocol V (fun _ => Bool)) (m : List Bool)
    (hG : (p.interactionGraph m).IsAcyclic) {R r : ℕ} (hR : 0 < R) (hr : r < R) :
    p.Along (PublicProtocol.Separated (pins (p.interactionGraph m) R r)
      (ancestor (p.interactionGraph m) R r)) m := by
  exact p.along_separated_of_graph_compatible m _ _
    (fun _ hv _ hw ha => ancestor_eq_of_adj_not_pinned _ hG hR hr hv hw ha)

end TransposeFollowup.AdaptiveForest
