import TransposeFollowup.RationalPageColor
import TransposeFollowup.BipartitePageEvents

/-! Compute one page record using only the bounded outgoing or incoming
neighbor list. The vertex order is A_0,...,A_(n-1),B_(n-1),...,B_0. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

def rationalOutgoingOn {c n : ℕ} (F : Fin c → RationalMobius) (i : Fin n)
    (p : Fin (rationalPageCount F)) : Bool :=
  decide (((rationalFamilyNeighbors F i).filter (fun j => rationalColor F i j = some p)).Nonempty)

def rationalIncomingOn {c n : ℕ} (F : Fin c → RationalMobius) (j : Fin n)
    (p : Fin (rationalPageCount F)) : Bool :=
  decide (((rationalFamilyIncoming F j).filter (fun i => rationalColor F i j = some p)).Nonempty)

theorem rationalOutgoingOn_spec {c n : ℕ} (F : Fin c → RationalMobius) (i : Fin n)
    (p : Fin (rationalPageCount F)) : rationalOutgoingOn F i p = true ↔
      (overlapPages (rationalFamilyMaps F) n).SourceEvent (OrderedBipartite.left i) p := by
  classical
  change decide _ = true ↔ (overlapColoring (rationalFamilyMaps F) n).nestedPages.SourceEvent _ _
  rw [decide_eq_true_eq, (overlapColoring (rationalFamilyMaps F) n).sourceEvent_left]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨_, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨he, hp⟩ := (rationalColor_some_iff F i j p).mp hc
    exact ⟨⟨(i, j), he⟩, rfl, hp⟩
  · rintro ⟨⟨⟨i', j⟩, he⟩, hi, hp⟩
    dsimp at hi hp
    subst i'
    refine ⟨j, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_rationalFamilyNeighbors F i j).mpr ((mem_overlapEdges _ _).mp he)
    · exact (rationalColor_eq_some F i j he).trans (congrArg some hp)

theorem rationalIncomingOn_spec {c n : ℕ} (F : Fin c → RationalMobius) (j : Fin n)
    (p : Fin (rationalPageCount F)) : rationalIncomingOn F j p = true ↔
      (overlapPages (rationalFamilyMaps F) n).TargetEvent (OrderedBipartite.right j) p := by
  classical
  change decide _ = true ↔ (overlapColoring (rationalFamilyMaps F) n).nestedPages.TargetEvent _ _
  rw [decide_eq_true_eq, (overlapColoring (rationalFamilyMaps F) n).targetEvent_right]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨_, hc⟩ := Finset.mem_filter.mp hi
    obtain ⟨he, hp⟩ := (rationalColor_some_iff F i j p).mp hc
    exact ⟨⟨(i, j), he⟩, rfl, hp⟩
  · rintro ⟨⟨⟨i, j'⟩, he⟩, hj, hp⟩
    dsimp at hj hp
    subst j'
    refine ⟨i, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_rationalFamilyIncoming F i j).mpr ((mem_overlapEdges _ _).mp he)
    · exact (rationalColor_eq_some F i j he).trans (congrArg some hp)

def rationalPageOpcode {c n : ℕ} (F : Fin c → RationalMobius) (u : Fin (2 * n))
    (p : Fin (rationalPageCount F)) : PageOpcode :=
  if hu : u.val < n then
    if rationalOutgoingOn F (⟨u.val, hu⟩ : Fin n) p then .openEdge else .idle
  else
    if rationalIncomingOn F (⟨2 * n - 1 - u.val, by have := u.isLt; omega⟩ : Fin n) p
      then .closeEdge else .idle

theorem rationalPageOpcode_left {c n : ℕ} (F : Fin c → RationalMobius) (i : Fin n)
    (p : Fin (rationalPageCount F)) :
    rationalPageOpcode F (OrderedBipartite.left i) p =
      if rationalOutgoingOn F i p then .openEdge else .idle := by
  unfold rationalPageOpcode
  have hi : (OrderedBipartite.left i).val < n := i.isLt
  rw [dite_eq_left hi]
  rfl

theorem rationalPageOpcode_right {c n : ℕ} (F : Fin c → RationalMobius) (j : Fin n)
    (p : Fin (rationalPageCount F)) :
    rationalPageOpcode F (OrderedBipartite.right j) p =
      if rationalIncomingOn F j p then .closeEdge else .idle := by
  have hj := j.isLt
  have hnot : ¬(OrderedBipartite.right j).val < n := by dsimp [OrderedBipartite.right]; omega
  unfold rationalPageOpcode
  rw [dite_eq_right hnot]
  have hv : 2 * n - 1 - (OrderedBipartite.right j).val = j.val := by
    dsimp [OrderedBipartite.right]
    omega
  simp only [hv]

theorem rationalPageOpcode_eq {c n : ℕ} (F : Fin c → RationalMobius) (u : Fin (2 * n))
    (p : Fin (rationalPageCount F)) : rationalPageOpcode F u p =
      (overlapPages (rationalFamilyMaps F) n).opcode u p := by
  classical
  rcases OrderedBipartite.left_or_right u with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [rationalPageOpcode_left]
    by_cases h : rationalOutgoingOn F i p = true
    · rw [ite_eq_left h]
      exact ((overlapPages (rationalFamilyMaps F) n).opcode_open_iff _ _).mpr
        ((rationalOutgoingOn_spec F i p).mp h) |>.symm
    · rw [ite_eq_right h]
      apply Eq.symm
      apply ((overlapPages (rationalFamilyMaps F) n).opcode_idle_iff _ _).mpr
      exact ⟨fun he => h ((rationalOutgoingOn_spec F i p).mpr he),
        (overlapColoring (rationalFamilyMaps F) n).not_targetEvent_left i p⟩
  · rw [rationalPageOpcode_right]
    by_cases h : rationalIncomingOn F j p = true
    · rw [ite_eq_left h]
      exact ((overlapPages (rationalFamilyMaps F) n).opcode_close_iff _ _).mpr
        ((rationalIncomingOn_spec F j p).mp h) |>.symm
    · rw [ite_eq_right h]
      apply Eq.symm
      apply ((overlapPages (rationalFamilyMaps F) n).opcode_idle_iff _ _).mpr
      exact ⟨(overlapColoring (rationalFamilyMaps F) n).not_sourceEvent_right j p,
        fun he => h ((rationalIncomingOn_spec F j p).mpr he)⟩

end TransposeFollowup
