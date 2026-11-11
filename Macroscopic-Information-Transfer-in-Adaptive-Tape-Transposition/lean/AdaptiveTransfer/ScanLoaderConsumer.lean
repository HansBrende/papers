import AdaptiveTransfer.ScanLoader

/-! The consumer branch preserves arbitrary native transitions and halting.
The producer therefore composes with an actual consumer without a linking step.
-/

namespace AdaptiveTransfer.ScanLoader

open Transpose

variable {r : ℕ} {S A : Fin r → Type*} {Q B : Type*}
variable (F : (j : Fin r) → S j → Bool → S j)
  (D : (j : Fin r) → S j → Bool → A j) (s₀ : ScanStates S) (q₀ : Q)
  (C : Consumer Q A B)

def embedConsumer (c : Config Q (Symbol A B) (r + 1)) :
    Config (Phase Q (ScanStates S)) (Symbol A B) (r + 1) :=
  ⟨consume c.state, c.inPos, c.work, c.workPos, c.outRev⟩

def consumerReady (w : List Bool) : Config Q (Symbol A B) (r + 1) :=
  ⟨q₀, 0, completedWork F D s₀ w, positions 0, []⟩

@[simp] theorem embed_consumerReady (w : List Bool) :
    embedConsumer (consumerReady (B := B) F D s₀ q₀ w) = readyConfig F D s₀ q₀ w := rfl

/-- Every arbitrary consumer instruction, including output and halt, is retained. -/
theorem consumer_next (w : List Bool) (c : Config Q (Symbol A B) (r + 1)) :
    next (table F D s₀ q₀ C) w (embedConsumer c) =
      (next C w c).map (embedConsumer (S := S)) := by
  simp only [next, embedConsumer, consume, table]
  cases h : C c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) with
  | none => rfl
  | some instruction => rcases instruction with ⟨q, move, acts, out⟩; rfl

theorem consumer_run (w : List Bool) (n : ℕ) (c : Config Q (Symbol A B) (r + 1)) :
    run (table F D s₀ q₀ C) w n (embedConsumer c) =
      (run C w n c).map (embedConsumer (S := S)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [run, consumer_next, run]
    cases h : next C w c with
    | none => rfl
    | some e => exact ih e

section Native
variable [Fintype Q] [∀ j, Fintype (S j)] [∀ j, Fintype (A j)] [Fintype B]

private theorem denote_injective {L Γ : Type*} [Fintype L] [Fintype Γ] {k : ℕ}
    (q : L) (blank : Γ) (δ : Table L Γ k) : Function.Injective (denote q blank δ) := by
  intro c e h
  apply Config.ext
  · exact (pointCode q).injective (congrArg Transpose.Config.state h)
  · exact congrArg Transpose.Config.inPos h
  · funext t z
    exact (pointCode blank).injective (congrArg (fun a => a.work t z) h)
  · exact congrArg Transpose.Config.workPos h
  · exact congrArg Transpose.Config.outRev h

/-- Actual native continuation of the consumer from every configuration, with
no transition overhead, and with all work positions/content/output preserved. -/
theorem native_consumer_run (w : List Bool) (n : ℕ)
    (c e : Config Q (Symbol A B) (r + 1))
    (h : Transpose.stepN (machine q₀ blank C) w n (denote q₀ blank C c) =
      some (denote q₀ blank C e)) :
    Transpose.stepN (nativeProducer F D s₀ q₀ C) w n
      (denote start blank (table F D s₀ q₀ C) (embedConsumer c)) =
      some (denote start blank (table F D s₀ q₀ C) (embedConsumer e)) := by
  rw [stepN_denote] at h
  have hr : run C w n c = some e :=
    Option.map_injective (denote_injective q₀ blank C) h
  unfold nativeProducer
  rw [stepN_denote, consumer_run, hr]
  rfl

/-- An actual native consumer execution after the exact paid preparation.
The only premise is the consumer's own native run, not a simulator certificate. -/
theorem native_prepare_then_consume (w : List Bool) (n : ℕ)
    (e : Config Q (Symbol A B) (r + 1))
    (h : Transpose.stepN (machine q₀ blank C) w n
      (denote q₀ blank C (consumerReady F D s₀ q₀ w)) = some (denote q₀ blank C e)) :
    Transpose.stepN (nativeProducer F D s₀ q₀ C) w (2 * w.length + 4 + n)
      (Transpose.init (nativeProducer F D s₀ q₀ C)) =
      some (denote start blank (table F D s₀ q₀ C) (embedConsumer e)) := by
  rw [stepN_denote] at h
  have hr : run C w n (consumerReady F D s₀ q₀ w) = some e :=
    Option.map_injective (denote_injective q₀ blank C) h
  have hc := consumer_run F D s₀ q₀ C w n (consumerReady F D s₀ q₀ w)
  rw [embed_consumerReady, hr] at hc
  have hall := run_trans _ _ (complete_run F D s₀ q₀ C w) hc
  unfold nativeProducer
  rw [← denote_initial, stepN_denote, hall]
  rfl

/-- The composed machine halts exactly when its consumer halts at the handoff
state or at any later consumer configuration. -/
theorem native_consumer_halt (w : List Bool) (c : Config Q (Symbol A B) (r + 1)) :
    Transpose.step (nativeProducer F D s₀ q₀ C) w
      (denote start blank (table F D s₀ q₀ C) (embedConsumer c)) = none ↔
    Transpose.step (machine q₀ blank C) w (denote q₀ blank C c) = none := by
  unfold nativeProducer
  rw [step_denote, consumer_next, step_denote]
  simp

end Native
end AdaptiveTransfer.ScanLoader
