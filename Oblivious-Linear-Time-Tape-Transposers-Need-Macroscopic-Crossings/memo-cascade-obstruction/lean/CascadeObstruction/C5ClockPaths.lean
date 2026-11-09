import CascadeObstruction.C5Clock
import CascadeObstruction.C5LocalPaths

/-! Every clock interval is the corresponding contiguous part of the actual
tick word. Empty addresses have a zero frozen displacement. -/

namespace CascadeObstruction.C5

open scoped BigOperators

set_option autoImplicit false

def activeStage (K b r : ℕ) (j : Fin 2) : List Block :=
  if r ≤ K then stage K b (r, j) else []

private def payloads (K b : ℕ) : List ((List (Fin 1) × Fin 2) × List Block) :=
  (keys K).map fun key => (clockKey key, stage K b key)

private theorem payload_lengths (K b : ℕ) :
    StageClockAssembly.chunksOfPayloads expand (payloads K b) = clockStages K b := by
  simp [StageClockAssembly.chunksOfPayloads, payloads, clockStages,
    List.map_map, Function.comp_def]

private theorem payload_trace (K b : ℕ) :
    (payloads K b).flatMap (fun x => expand x.2) = trace K b := by
  simp [payloads, trace, expand, programBlocks, List.flatMap_assoc, List.flatMap_map]

theorem activeStage_blocks_bound (K b r : ℕ) (j : Fin 2) :
    (activeStage K b r j).length ≤ 4 * 2 ^ r + 13 := by
  unfold activeStage
  split_ifs
  · exact stage_blocks_bound K b r j
  · simp

theorem activeStage_duration (K b : ℕ) (hb : 0 < b)
    (w : List (Fin 1)) (j : Fin 2) :
    blocksDuration (activeStage K b w.length j) =
      (clock K b hb).E w j - (clock K b hb).A w j := by
  rw [clock_duration]
  unfold activeStage
  split_ifs <;> rfl

theorem activeStage_budget (K b : ℕ) (hb : 0 < b)
    (w : List (Fin 1)) (j : Fin 2) :
    (blocksDuration (activeStage K b w.length j) : ℝ) ≤
      18 * (clock K b hb).V w := by
  rw [activeStage_duration K b hb w j]
  have hle : (clock K b hb).E w j - (clock K b hb).A w j ≤
      ∑ j' : Fin 2, ((clock K b hb).E w j' - (clock K b hb).A w j') :=
    Finset.single_le_sum
      (f := fun j' : Fin 2 => (clock K b hb).E w j' - (clock K b hb).A w j')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact (Nat.cast_le.mpr hle).trans ((clock K b hb).budget w)

theorem clock_volume_pos (K b : ℕ) (hb : 0 < b) (w : List (Fin 1)) :
    0 < (clock K b hb).V w := by
  rw [clock_volume]
  unfold volume
  have hp : (0 : ℝ) < inputLength K b := by exact_mod_cast inputLength_pos K hb
  positivity

theorem clock_stage_path (K b : ℕ) (hb : 0 < b) (w : List (Fin 1))
    (j : Fin 2) (h : Fin 3) (t : ℕ) :
    position (trace K b) h ((clock K b hb).A w j +
        min t ((clock K b hb).E w j - (clock K b hb).A w j)) -
      position (trace K b) h ((clock K b hb).A w j) =
        position (expand (activeStage K b w.length j)) h t := by
  by_cases hr : w.length ≤ K
  · have hn : ((payloads K b).map Prod.fst).Nodup := by
      simpa [payloads, clockStages, List.map_map, Function.comp_def] using clockStages_nodup K b
    have hm : ((w, j), stage K b (w.length, j)) ∈ payloads K b := by
      apply List.mem_map.mpr
      exact ⟨(w.length, j), mem_keys_iff.mpr hr, by rw [clockKey_length]⟩
    obtain ⟨pre, post, he, hA, hlen⟩ :=
      StageClockAssembly.exists_payload_decomposition expand hn hm
    rw [payload_lengths] at hA hlen
    rw [payload_trace] at he
    rw [clock_start, clock_finish, hlen, hA, he]
    simpa [activeStage, hr] using position_segment pre
      (expand (stage K b (w.length, j))) post h t
  · rw [clock_duration]
    simp [activeStage, hr, expand]

end CascadeObstruction.C5
