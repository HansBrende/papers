import TransposeFollowup.FiniteStageLimits
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order

/-! Adaptive stage designations stabilize on a common subsequence. Finite
filtered interval families then reuse the existing endpoint-limit theorem. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology MeasureTheory
set_option autoImplicit false

theorem exists_stage_flag_subsequence {κ : Type*} [Countable κ] (good : ℕ → κ → Bool) :
    ∃ (g : κ → Bool) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ p, ∀ᶠ n in atTop, good (φ n) p=g p := by
  obtain ⟨g,φ,hφ,hg⟩ := CompactSpace.tendsto_subseq good
  refine ⟨g,φ,hφ,fun p => ?_⟩
  have hp : Tendsto (fun n => good (φ n) p) atTop (𝓝 (g p)) :=
    (continuous_apply p).continuousAt.tendsto.comp hg
  exact hp.eventually ((isOpen_discrete ({g p} : Set Bool)).mem_nhds (Set.mem_singleton _))

theorem finite_flag_filter_eventually_eq {κ : Type*} (Q : Finset κ)
    {good : ℕ → κ → Bool} {g : κ → Bool}
    (hg : ∀ p ∈ Q, ∀ᶠ n in atTop, good n p=g p) :
    ∀ᶠ n in atTop, Q.filter (fun p => good n p=true)=Q.filter (fun p => g p=true) := by
  filter_upwards [(eventually_all_finset Q).mpr hg] with n hn
  ext p
  by_cases hp : p ∈ Q
  · simp only [Finset.mem_filter,hp,true_and,hn p hp]
  · simp only [Finset.mem_filter,hp,false_and]

theorem finite_flagged_stage_omission_tendsto {κ : Type*} (Q : Finset κ)
    {ls rs : ℕ → κ → ℝ} {Hs : ℕ → ℝ} {l r : κ → ℝ} {H : ℝ}
    {good : ℕ → κ → Bool} {g : κ → Bool}
    (hl : ∀ p ∈ Q, Tendsto (fun n => ls n p) atTop (𝓝 (l p)))
    (hr : ∀ p ∈ Q, Tendsto (fun n => rs n p) atTop (𝓝 (r p)))
    (hH : Tendsto Hs atTop (𝓝 H))
    (hb : ∀ᶠ n in atTop, 0 ≤ Hs n ∧ ∀ p ∈ Q,
      0 ≤ ls n p ∧ ls n p ≤ rs n p ∧ rs n p ≤ Hs n)
    (hd : ∀ᶠ n in atTop,
      (Q : Set κ).PairwiseDisjoint (fun p => Ico (ls n p) (rs n p)))
    (hg : ∀ p ∈ Q, ∀ᶠ n in atTop, good n p=g p) :
    Tendsto (fun n => volume.real (Ico 0 (Hs n) \
      stageRegion (ls n) (rs n) (Q.filter (fun p => good n p=true) : Set κ)))
      atTop (𝓝 (volume.real (Ico 0 H \ stageRegion l r (Q.filter (fun p => g p=true) : Set κ)))) := by
  have hsub : ∀ p ∈ Q.filter (fun p => g p=true), p ∈ Q :=
    fun _ hp => (Finset.mem_filter.mp hp).1
  have hc := finite_stage_omission_tendsto (Q.filter (fun p => g p=true))
    (fun p hp => hl p (hsub p hp)) (fun p hp => hr p (hsub p hp)) hH
    (hb.mono (fun n hn => ⟨hn.1,fun p hp => hn.2 p (hsub p hp)⟩))
    (hd.mono (fun n hn p hp q hq hpq => hn (hsub p hp) (hsub q hq) hpq))
  apply hc.congr'
  filter_upwards [finite_flag_filter_eventually_eq Q hg] with n hn
  rw [hn]

end TransposeFollowup.RegularMotion
