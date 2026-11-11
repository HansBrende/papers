import AdaptiveTransfer.GeometryMenus
import AdaptiveTransfer.NativeReplayAdapters
import MergeDepth.Traces

/-! Actual sampled cut positions, move trits and full step payloads. The
position increments share one variation budget; the payload plus move fields
recover the actual instruction without paying its old state again. -/

namespace AdaptiveTransfer
open Transpose MergeDepth Finset BoundedNesting LeanMachine

noncomputable def cutSampleTimes (B : Finset ℕ) (i : Fin (B.card + 1)) : ℕ :=
  if hi : i.val = 0 then 0 else
    (B.orderEmbOfFin rfl) ⟨i.val - 1, by have := i.isLt; omega⟩

@[simp] theorem cutSampleTimes_zero (B : Finset ℕ) : cutSampleTimes B 0 = 0 := by
  simp [cutSampleTimes]

@[simp] theorem cutSampleTimes_succ (B : Finset ℕ) (i : Fin B.card) :
    cutSampleTimes B i.succ = (B.orderEmbOfFin rfl) i := by
  simp [cutSampleTimes]

theorem cutSampleTimes_mono (B : Finset ℕ) : Monotone (cutSampleTimes B) := by
  intro i j hij
  by_cases hi : i.val = 0
  · simp only [cutSampleTimes, dite_eq_left hi]
    exact Nat.zero_le _
  · have hj : j.val ≠ 0 := by have hh : i.val ≤ j.val := hij; omega
    simp only [cutSampleTimes, dite_eq_right hi, dite_eq_right hj]
    exact (B.orderEmbOfFin rfl).monotone (show i.val - 1 ≤ j.val - 1 from Nat.sub_le_sub_right hij 1)

theorem cutSampleTimes_le {B : Finset ℕ} {T : ℕ} (hBT : ∀ p ∈ B, p < T)
    (i : Fin (B.card + 1)) : cutSampleTimes B i ≤ T := by
  unfold cutSampleTimes
  split_ifs
  · exact Nat.zero_le _
  · exact (hBT _ (B.orderEmbOfFin_mem rfl _)).le

noncomputable def cutHeadDescription {B : Finset ℕ} {T : ℕ}
    (hBT : ∀ p ∈ B, p < T) (y : ℕ → ℤ) (hy : IsWalk y) (hy0 : y 0 = 0)
    (moves : Fin B.card → Fin 3) : HeadDescription B.card T :=
  headDescription (sampledWalk y hy hy0 (cutSampleTimes B) (cutSampleTimes_mono B)
    (cutSampleTimes_zero B) (cutSampleTimes_le hBT _), moves)

/-- Equal signed-increment/move records recover every actual old cut
coordinate and every move. No independent coordinate budget is supplied. -/
theorem cutHeadDescription_recovers {B : Finset ℕ} {T : ℕ}
    (hBT : ∀ p ∈ B, p < T) {y z : ℕ → ℤ} (hy : IsWalk y) (hz : IsWalk z)
    (hy0 : y 0 = 0) (hz0 : z 0 = 0) {moves moves' : Fin B.card → Fin 3}
    (he : cutHeadDescription hBT y hy hy0 moves = cutHeadDescription hBT z hz hz0 moves') :
    (∀ p ∈ B, y p = z p) ∧ moves = moves' := by
  have hh := headDescription_injective B.card T he
  refine ⟨?_, congrArg Prod.snd hh⟩
  intro p hp
  let i := (B.orderIsoOfFin rfl).symm ⟨p, hp⟩
  have heq : (B.orderEmbOfFin rfl) i = p :=
    congrArg Subtype.val ((B.orderIsoOfFin rfl).apply_symm_apply ⟨p, hp⟩)
  have hv := congrFun (congrArg (fun v => v.1.val) hh) i.succ
  simpa only [sampledWalk, sampleUnitPath, cutSampleTimes_succ, heq] using hv

def moveTrit : Dir → Fin 3
  | .left => 0
  | .stay => 1
  | .right => 2

theorem moveTrit_injective : Function.Injective moveTrit := by
  intro d e he
  cases d <;> cases e <;> simp_all [moveTrit]

abbrev NativeInstruction (M : TM) :=
  Fin (M.q + 1) × Dir × (Fin M.k → Fin (M.g + 1) × Dir) × Option Bool

def instructionPayload {M : TM} (v : NativeInstruction M) : Value M :=
  (v.1, fun h => (v.2.2.1 h).1, v.2.2.2)

def instructionMoves {M : TM} (v : NativeInstruction M) : Fin (M.k + 1) → Fin 3 :=
  Fin.cons (moveTrit v.2.1) (fun h => moveTrit (v.2.2.1 h).2)

theorem instruction_fields_injective (M : TM) :
    Function.Injective (fun v : NativeInstruction M => (instructionPayload v, instructionMoves v)) := by
  intro v w he
  have hp := congrArg Prod.fst he
  have hm := congrArg Prod.snd he
  apply Prod.ext
  · exact congrArg (fun p : Value M => p.1) hp
  · apply Prod.ext
    · exact moveTrit_injective (congrFun hm 0)
    · apply Prod.ext
      · funext h
        apply Prod.ext
        · exact congrFun (congrArg (fun p : Value M => p.2.1) hp) h
        · exact moveTrit_injective (congrFun hm h.succ)
      · exact congrArg (fun p : Value M => p.2.2) hp

namespace ExecutionPrefix

theorem exists_instruction {M : TM} {w : List Bool} {T t : ℕ}
    (E : ExecutionPrefix M w T) (ht : t < T) :
    ∃ v : NativeInstruction M, nativeInstruction M w (E.config t) = some v := by
  cases he : nativeInstruction M w (E.config t) with
  | none =>
    have hh := E.successful t ht
    simp only [nativeInstruction] at he
    simp [step, he] at hh
  | some v => exact ⟨v, rfl⟩

noncomputable def actualInstruction {M : TM} {w : List Bool} {T t : ℕ}
    (E : ExecutionPrefix M w T) (ht : t < T) : NativeInstruction M := (E.exists_instruction ht).choose

theorem actualInstruction_spec {M : TM} {w : List Bool} {T t : ℕ}
    (E : ExecutionPrefix M w T) (ht : t < T) :
    nativeInstruction M w (E.config t) = some (E.actualInstruction ht) :=
  (E.exists_instruction ht).choose_spec

end ExecutionPrefix

theorem payload_card_le (M : TM) (q a : ℕ) (hq : M.q + 1 ≤ 2 ^ q) (ha : M.g + 1 ≤ 2 ^ a) :
    Fintype.card (Value M) ≤ 2 ^ (q + M.k * a + 2) := by
  simp only [Value, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_option, Fintype.card_bool]
  calc
    _ ≤ 2 ^ q * ((2 ^ a) ^ M.k * 4) :=
      Nat.mul_le_mul hq (Nat.mul_le_mul (Nat.pow_le_pow_left ha _) (by norm_num))
    _ = _ := by rw [pow_add, pow_add, pow_mul]; ring

end AdaptiveTransfer
