import BoundedStackDepth.FrameDynamics
import BoundedStackDepth.Display

/-!
# Entries, tops and windows

For a frame system `S` (the frames of one virtual head) and a grid offset `r`:
* `parent F`: the smallest frame strictly containing `F` (unique by laminarity, `parent_spec`);
* `IsEntry F`: `F` is a nonempty non-root frame whose *parent segment* (the segment of its parent
  current at its start) is innermost again at some time after `F` ends; every other frame is a restart
  drop;
* `entryTop F`: the group of the frozen band of the parent segment at the push;
* `entryBot F t`: the current maximum of the head's band group and of the tops of the entries stacked
  inside `F` at `t`.

`entry_candidate_unique`: along the stack of one head, the tops of inner entries are at most the bottoms
of outer ones, so for every value there is at most one candidate per head (`OneCandidate`, the only
structural fact Lemma D uses).
-/

namespace BoundedStackDepth

namespace FrameSystem

open Finset

variable (S : FrameSystem)

/-- The frames strictly containing `F`. -/
def above (F : ℕ × ℕ) : Finset (ℕ × ℕ) := S.frames.filter fun G => Within F G ∧ G ≠ F

theorem root_mem_above {F : ℕ × ℕ} (hF : F ∈ S.frames) (hne : F ≠ (0, S.T)) :
    (0, S.T) ∈ S.above F :=
  mem_filter.mpr ⟨S.root_mem, ⟨Nat.zero_le _, S.bounds F hF⟩, hne.symm⟩

/-- The parent of `F`: a shortest frame strictly containing it (the root if there is none). -/
noncomputable def parent (F : ℕ × ℕ) : ℕ × ℕ :=
  if h : (S.above F).Nonempty then Classical.choose (exists_min_image _ (fun G => G.2 - G.1) h)
  else (0, S.T)

variable {S}

theorem parent_spec {F : ℕ × ℕ} (hF : F ∈ S.frames) (hne : F ≠ (0, S.T)) :
    S.parent F ∈ S.above F ∧ ∀ G ∈ S.above F, (S.parent F).2 - (S.parent F).1 ≤ G.2 - G.1 := by
  have h : (S.above F).Nonempty := ⟨_, root_mem_above S hF hne⟩
  unfold parent
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (exists_min_image _ (fun G => G.2 - G.1) h)

/-- The parent of a nonempty frame lies inside every frame strictly containing it. -/
theorem parent_within {F G : ℕ × ℕ} (hF : F ∈ S.frames) (hne : F ≠ (0, S.T)) (hFne : F.1 < F.2)
    (hG : G ∈ S.above F) : Within (S.parent F) G := by
  obtain ⟨hP, hmin⟩ := parent_spec hF hne
  obtain ⟨hPm, hFP, -⟩ := mem_filter.mp hP
  obtain ⟨hGm, hFG, -⟩ := mem_filter.mp hG
  have hle := hmin G hG
  have hPt : Contains (S.parent F) F.1 := ⟨hFP.1, lt_of_lt_of_le hFne hFP.2⟩
  have hGt : Contains G F.1 := ⟨hFG.1, lt_of_lt_of_le hFne hFG.2⟩
  rcases nested_of_contains hPm hGm hPt hGt with h | h
  · exact h
  · unfold Within at h ⊢
    unfold Within at hFP hFG
    unfold Contains at hPt hGt
    omega

variable (S)

/-- **Entries.** A nonempty non-root frame whose parent segment is innermost again at some time
after it ends. -/
def IsEntry (F : ℕ × ℕ) : Prop :=
  F ∈ S.frames ∧ F ≠ (0, S.T) ∧ F.1 < F.2 ∧
    ∃ t', F.2 ≤ t' ∧ S.Own (S.parent F) t' ∧
      S.segStart (S.parent F) t' = S.segStart (S.parent F) F.1

variable (h₀ r : ℕ)

/-- The band group of the head at `t`. -/
noncomputable def headGroup (t : ℕ) : ℕ := grp h₀ r (S.beta t)

/-- **Tops.** The group of the frozen band of the parent segment at the push. -/
noncomputable def entryTop (F : ℕ × ℕ) : ℕ := grp h₀ r (band (S.runMax (S.parent F) F.1))

open Classical in
/-- The entries stacked strictly inside `F` at `t`. -/
noncomputable def innerEntries (F : ℕ × ℕ) (t : ℕ) : Finset (ℕ × ℕ) :=
  S.frames.filter fun F' => S.IsEntry F' ∧ Within F' F ∧ F' ≠ F ∧ Contains F' t

/-- **Window bottoms.** The current maximum of the head's band group and of the tops of the entries
stacked inside `F` at `t`. -/
noncomputable def entryBot (F : ℕ × ℕ) (t : ℕ) : ℕ :=
  max (S.headGroup h₀ r t) ((S.innerEntries F t).sup (S.entryTop h₀ r))

variable {S h₀ r}

/-- The top of an inner entry is at most the bottom of an outer one. -/
theorem entryTop_le_entryBot {F F' : ℕ × ℕ} {t : ℕ} (hF' : S.IsEntry F') (hw : Within F' F)
    (hne : F' ≠ F) (ht : Contains F' t) : S.entryTop h₀ r F' ≤ S.entryBot h₀ r F t := by
  classical
  refine le_max_of_le_right (le_sup (f := S.entryTop h₀ r) ?_)
  exact mem_filter.mpr ⟨hF'.1, hF', hw, hne, ht⟩

open Classical in
/-- **One candidate per head and value.** Among the entries of one head on the stack at `t`, at
most one has `bot ≤ y < top`. -/
theorem entry_candidate_unique {F F' : ℕ × ℕ} {t y : ℕ} (hF : S.IsEntry F) (hF' : S.IsEntry F')
    (ht : Contains F t) (ht' : Contains F' t) (h1 : S.entryBot h₀ r F t ≤ y)
    (h2 : y < S.entryTop h₀ r F) (h1' : S.entryBot h₀ r F' t ≤ y) (h2' : y < S.entryTop h₀ r F') :
    F = F' := by
  by_contra hne
  rcases nested_of_contains hF.1 hF'.1 ht ht' with hw | hw
  · have := entryTop_le_entryBot (h₀ := h₀) (r := r) hF hw hne ht
    omega
  · have := entryTop_le_entryBot (h₀ := h₀) (r := r) hF' hw (Ne.symm hne) ht'
    omega

end FrameSystem

end BoundedStackDepth
