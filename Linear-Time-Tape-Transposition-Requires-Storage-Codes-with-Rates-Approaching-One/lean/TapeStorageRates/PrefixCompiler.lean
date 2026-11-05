import TapeStorageRates.NativeWarmSeed
import TapeStorageRates.NativeResources
import TransposeFollowup.SequentialFiveRun

/-! # Switching from a direct prefix to aligned batches

The prefix machine uses the source transition itself for its first 2s successful steps and
then runs the aligned finite control from the current native configuration.
-/

namespace TapeStorageRates.Prefix

open Transpose Transpose.Tape Transpose.Tape.Impl Native

set_option autoImplicit false

private abbrev PC (M : TM) {s : ℕ} (hs : 0 < s) :=
  (Fin (2*s) × Fin (M.q+1)) ⊕ Fin ((Native.machine M hs).q + 1)

private def firstPC (M : TM) {s : ℕ} (hs : 0 < s) : PC M hs :=
  .inl (⟨0, by omega⟩, 0)

private noncomputable def number (M : TM) {s : ℕ} (hs : 0 < s) :
    PC M hs ≃ Fin (Fintype.card (PC M hs)-1+1) :=
  (TransposeFollowup.NativeMicrocode.initialEncoding (T := Fin M.k) (firstPC M hs)).label

private theorem number_first (M : TM) {s : ℕ} (hs : 0 < s) :
    number M hs (firstPC M hs) = 0 :=
  TransposeFollowup.NativeMicrocode.initialEncoding_start _

private noncomputable def seedState (M : TM) {s : ℕ} (hs : 0 < s) (q : Fin (M.q+1)) :
    Fin ((Native.machine M hs).q+1) :=
  Native.labelEquiv M hs (.left ⟨0,hs⟩, { Native.initialRegs M hs with q := q })

private noncomputable def after (M : TM) {s : ℕ} (hs : 0 < s) (i : Fin (2*s))
    (q : Fin (M.q+1)) : PC M hs :=
  if h : i.val+1 < 2*s then .inl (⟨i.val+1,h⟩,q) else .inr (seedState M hs q)

/-- A genuine finite-table machine with the original tape count and work alphabet. -/
noncomputable abbrev machine (M : TM) {s : ℕ} (hs : 0 < s) : TM where
  k := M.k
  g := M.g
  q := Fintype.card (PC M hs)-1
  δ := fun state input work => match (number M hs).symm state with
    | .inl (i,q) => (M.δ q input work).map (fun z => (number M hs (after M hs i z.1), z.2))
    | .inr q => ((Native.machine M hs).δ q input work).map (fun z => (number M hs (.inr z.1), z.2))

/-- Copy a configuration without changing the positions, tapes or printed bits. -/
private def withState {M N : TM} (hk : N.k = M.k) (hg : N.g = M.g)
    (q : Fin (N.q+1)) (c : Config M) : Config N where
  state := q
  inPos := c.inPos
  workPos := fun j => c.workPos (Fin.cast hk j)
  work := fun j i => Fin.cast (congrArg (·+1) hg.symm) (c.work (Fin.cast hk j) i)
  outRev := c.outRev

noncomputable def direct {M : TM} {s : ℕ} (hs : 0 < s) (i : Fin (2*s)) (c : Config M) :
    Config (machine M hs) := withState (M := M) (N := machine M hs) rfl rfl (number M hs (.inl (i,c.state))) c

noncomputable def core {M : TM} {s : ℕ} (hs : 0 < s) (c : Config (Native.machine M hs)) :
    Config (machine M hs) := withState (M := Native.machine M hs) (N := machine M hs) rfl rfl (number M hs (.inr c.state)) c

private noncomputable def afterConfig {M : TM} {s : ℕ} (hs : 0 < s) (i : Fin (2*s))
    (c : Config M) : Config (machine M hs) :=
  withState (M := M) (N := machine M hs) rfl rfl (number M hs (after M hs i c.state)) c

theorem step_direct {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool) (i : Fin (2*s))
    (c : Config M) :
    step (machine M hs) w (direct hs i c) = (step M w c).map (afterConfig hs i) := by
  simp only [step, direct, withState, machine, Equiv.symm_apply_apply, Fin.cast_refl, id_eq]
  cases h : M.δ c.state (readInput w c.inPos) (fun j => c.work j (c.workPos j)) with
  | none => rfl
  | some z => rcases z with ⟨q,d,a,o⟩; rfl

theorem step_core {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool)
    (c : Config (Native.machine M hs)) :
    step (machine M hs) w (core hs c) = (step (Native.machine M hs) w c).map (core hs) := by
  simp only [step, core, withState, machine, Equiv.symm_apply_apply, Fin.cast_refl, id_eq]
  cases h : Native.drive hs ((Native.labelEquiv M hs).symm c.state) (readInput w c.inPos)
      (fun j => c.work j (c.workPos j)) with
  | none => rfl
  | some z => rcases z with ⟨q,d,a,o⟩; rfl

/-- Every successful sequence of aligned steps is an equally long sequence in the wrapper. -/
theorem stepN_core {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool)
    (n : ℕ) (c : Config (Native.machine M hs)) :
    stepN (machine M hs) w n (core hs c) = (stepN (Native.machine M hs) w n c).map (core hs) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [stepN, step_core]
    cases h : step (Native.machine M hs) w c with
    | none => rfl
    | some c' => exact ih c'

private theorem init_direct (M : TM) {s : ℕ} (hs : 0 < s) :
    init (machine M hs) = direct hs ⟨0,by omega⟩ (init M) := by
  unfold init direct withState
  simp only [show (number M hs (.inl (⟨0,by omega⟩,0))) = 0 from number_first M hs]
  rfl

private theorem stepN_succ_last (M : TM) (w : List Bool) (n : ℕ) (c : Config M) :
    stepN M w (n+1) c = (stepN M w n c).bind (step M w) := by
  rw [TransposeFollowup.SequentialFive.stepN_add]
  congr 1
  funext a
  simp only [stepN]
  cases step M w a <;> rfl

/-- Direct steps are copied exactly. On the last tick of the fixed prefix the state changes
mode for free and the live work tapes become the aligned simulator's work tapes. -/
theorem direct_prefix {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool) {n : ℕ} {c : Config M}
    (hn : n ≤ 2*s) (h : stepN M w n (init M) = some c) :
    stepN (machine M hs) w n (init (machine M hs)) =
      some (if hlt : n < 2*s then direct hs ⟨n,hlt⟩ c else core hs (Native.warmSeed M hs c)) := by
  induction n generalizing c with
  | zero =>
    simp only [stepN] at h
    cases h
    simp [stepN, init_direct, hs]
  | succ n ih =>
    rw [stepN_succ_last] at h ⊢
    cases he : stepN M w n (init M) with
    | none => simp [he] at h
    | some a =>
      have hn' : n < 2*s := by omega
      have h' := ih hn'.le he
      simp [hn'] at h'
      rw [h']
      simp only [he, Option.bind_some] at h
      simp only [Option.bind_some, step_direct, h, Option.map_some]
      by_cases hh : n+1 < 2*s
      · simp [hh, afterConfig, after, direct]
      · simp [hh, afterConfig, after, core, Native.warmSeed, Native.warmRegs, seedState, withState]

/-- Once the machine is in the aligned phase, each transition has the same observable
directions and append flag as the corresponding aligned configuration. -/
theorem motion_core {M : TM} {s : ℕ} (hs : 0 < s) (w : List Bool)
    (c : Config (Native.machine M hs)) :
    (Native.lookup (machine M hs) (readInput w) (core hs c)).map
        (fun z => (z.2.1, fun j => (z.2.2.1 j).2, z.2.2.2.isSome)) =
      (Native.lookup (Native.machine M hs) (readInput w) c).map
        (fun z => (z.2.1, fun j => (z.2.2.1 j).2, z.2.2.2.isSome)) := by
  simp only [Native.lookup, core, withState, machine, Equiv.symm_apply_apply, Fin.cast_refl, id_eq,
    Option.map_map]
  rfl

/-- The direct prefix adds only a bounded counter and the old source state to the choice of
finite control modes. The combined control still takes O_M(s) bits. -/
theorem control_bits (M : TM) : ∃ K : ℕ, ∀ (s : ℕ) (hs : 0 < s),
    (machine M hs).q+1 ≤ 2^(K*s) := by
  obtain ⟨a, ha⟩ := Native.control_bits M
  obtain ⟨b, hb⟩ := ResourceBounds.exp_mul
    (ResourceBounds.exp_mul (ResourceBounds.exp_const 2) ResourceBounds.exp_self)
    (ResourceBounds.exp_const (M.q+1))
  refine ⟨max a b + 1, fun s hs => ?_⟩
  let W := 2 ^ (max a b * s)
  have h₁ : (Native.machine M hs).q+1 ≤ W := (ha s hs).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left _ _)))
  have h₂ : 2*s*(M.q+1) ≤ W := (hb s hs).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right _ _)))
  let : Nonempty (PC M hs) := ⟨firstPC M hs⟩
  change Fintype.card (PC M hs)-1+1 ≤ _
  rw [Nat.sub_add_cancel Fintype.card_pos]
  have pcCard : Fintype.card (PC M hs) = 2*s*(M.q+1)+((Native.machine M hs).q+1) := by
    simp only [PC, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [pcCard]
  calc
    2*s*(M.q+1)+((Native.machine M hs).q+1) ≤ W+W := Nat.add_le_add h₂ h₁
    _ ≤ W * 2^s := by
      have hh : 2^1 ≤ 2^s := Nat.pow_le_pow_right (by decide) hs
      have h := Nat.mul_le_mul_left W hh
      simpa only [pow_one, Nat.mul_two] using h
    _ = 2 ^ ((max a b+1)*s) := by simp [W, Nat.add_mul, pow_add]

end TapeStorageRates.Prefix
