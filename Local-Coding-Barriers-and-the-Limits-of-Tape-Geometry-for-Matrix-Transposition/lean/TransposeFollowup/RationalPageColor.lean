import TransposeFollowup.RationalSymmetricGraph

/-! Executable least-witness tags and residue page colors. Only the fixed
finite map family is searched, using the verified rational overlap test. -/

namespace TransposeFollowup

set_option autoImplicit false

def rationalWitnessTags {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) : Finset (Fin c) :=
  Finset.univ.filter (fun p => (F p).overlapTest i j = true)

def rationalTag {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) : Option (Fin c) :=
  if h : (rationalWitnessTags F i j).Nonempty then
    some ((rationalWitnessTags F i j).min' h) else none

theorem rationalWitnessTags_eq {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    rationalWitnessTags F i j = overlapTags (rationalFamilyMaps F) (i, j) := by
  classical
  ext p
  simp only [rationalWitnessTags, overlapTags, Finset.mem_filter, Finset.mem_univ, true_and,
    RationalMobius.overlapTest_spec, rationalFamilyMaps, BoundedMonotoneMap.widen_overlap]

theorem rationalWitnessTags_nonempty_iff {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    (rationalWitnessTags F i j).Nonempty ↔ (i, j) ∈ overlapEdges (rationalFamilyMaps F) n := by
  classical
  rw [rationalWitnessTags_eq, mem_overlapEdges]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩

theorem rationalTag_eq_some {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n)
    (he : (i, j) ∈ overlapEdges (rationalFamilyMaps F) n) :
    rationalTag F i j = some (overlapTag (rationalFamilyMaps F) ⟨(i, j), he⟩) := by
  classical
  have hn := (rationalWitnessTags_nonempty_iff F i j).mpr he
  rw [rationalTag, dite_eq_left hn]
  congr 1
  unfold overlapTag
  simp only [rationalWitnessTags_eq]

theorem rationalTag_none_iff {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    rationalTag F i j = none ↔ (i, j) ∉ overlapEdges (rationalFamilyMaps F) n := by
  classical
  rw [← rationalWitnessTags_nonempty_iff]
  unfold rationalTag
  split_ifs <;> simp_all

abbrev rationalPageCount {c : ℕ} (F : Fin c → RationalMobius) : ℕ :=
  c * ((rationalFamilyBound F + 1) * (rationalFamilyBound F + 1))

def rationalResidueColor {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) (p : Fin c) :
    Fin (rationalPageCount F) :=
  finProdFinEquiv (p, finProdFinEquiv
    (⟨i.val % (rationalFamilyBound F + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩,
      ⟨j.val % (rationalFamilyBound F + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩))

def rationalColor {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    Option (Fin (rationalPageCount F)) := (rationalTag F i j).map (rationalResidueColor F i j)

theorem rationalColor_eq_some {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n)
    (he : (i, j) ∈ overlapEdges (rationalFamilyMaps F) n) :
    rationalColor F i j = some ((overlapColoring (rationalFamilyMaps F) n).color ⟨(i, j), he⟩) := by
  rw [rationalColor, rationalTag_eq_some F i j he]
  rfl

theorem rationalColor_none_iff {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n) :
    rationalColor F i j = none ↔ (i, j) ∉ overlapEdges (rationalFamilyMaps F) n := by
  rw [rationalColor, Option.map_eq_none_iff, rationalTag_none_iff]

theorem rationalColor_some_iff {c n : ℕ} (F : Fin c → RationalMobius) (i j : Fin n)
    (p : Fin (rationalPageCount F)) : rationalColor F i j = some p ↔
      ∃ he : (i, j) ∈ overlapEdges (rationalFamilyMaps F) n,
        (overlapColoring (rationalFamilyMaps F) n).color ⟨(i, j), he⟩ = p := by
  classical
  by_cases he : (i, j) ∈ overlapEdges (rationalFamilyMaps F) n
  · rw [rationalColor_eq_some F i j he]
    constructor
    · exact fun hp => ⟨he, Option.some.inj hp⟩
    · rintro ⟨_, hp⟩
      exact congrArg some hp
  · rw [(rationalColor_none_iff F i j).mpr he]
    simp [he]

end TransposeFollowup
