import TapeStorageRates.NativeCompiler
import MergeDepth.BlockMachine

/-! # Whole-interval records from one local seed

The seed includes the complete finite control, not merely the simulated
source state. The existing native locality lemma supplies the replay.
-/

namespace TapeStorageRates.NativeBatchRecord

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth Native

set_option autoImplicit false

/-- The full control and the initial three-block windows. -/
abbrev Seed (M : TM) (s : ℕ) :=
  Fin (M.q+1) × Cells (Option Bool) s × (Fin M.k → Cells (Fin (M.g+1)) s)

def seed (M : TM) (s a : ℕ) (ai : ℤ) (aw : Fin M.k → ℤ) (w : List Bool) : Seed M s :=
  ((run M w a).state, capture s (readInput w) ai,
    fun j => capture s ((run M w a).work j) (aw j))

theorem read_eq_of_capture_eq {α : Type*} {s : ℕ} {f g : ℤ → α} {a p : ℤ}
    (blank : α) (h : capture s f a = capture s g a) (hp : Fits s 0 (p-a)) : f p = g p := by
  have hf := windowRead_capture f a (p-a) blank hp
  have hg := windowRead_capture g a (p-a) blank hp
  rw [h] at hf
  simpa using hf.symm.trans hg

/-- A scale-one record uses just the next control, written symbols and this
step's output. The previous output prefix need not agree. -/
theorem record_eq_of_live_transition {M : TM} {w w' : List Bool} {t : ℕ}
    (hs : (run M w t).state = (run M w' t).state)
    (hi : (run M w t).inPos = (run M w' t).inPos)
    (hw : (run M w t).workPos = (run M w' t).workPos)
    (ht : transAt M w t = transAt M w' t) (hlive : transAt M w t ≠ none) :
    blockVal M 1 w t = blockVal M 1 w' t := by
  obtain ⟨z,hz⟩ := Option.ne_none_iff_exists'.mp hlive
  have hz' : transAt M w' t = some z := ht.symm.trans hz
  have hn := stateHeads_succ hs hi hw ht
  refine BlockVal.ext hn.1 (funext fun j => funext fun i => ?_) ?_
    (funext fun j => ?_) ?_
  · have hzero : i = 0 := Fin.eq_zero i
    subst i
    simp only [blockVal, Nat.cast_one, Int.ediv_one, one_mul, Fin.val_zero,
      Nat.cast_zero, add_zero]
    rw [run_succ_work, run_succ_work]
    simp [writtenSym,hz,hz']
  · simp only [blockVal, Nat.cast_one, Int.ediv_one, one_mul]
    rw [hn.2.1,hi]
  · simp only [blockVal, Nat.cast_one, Int.ediv_one, one_mul]
    rw [hn.2.2,hw]
  · simp only [blockVal, Nat.div_one, one_mul, run_succ_outRev_reverse]
    simp [outBit,hz,hz']

/-- On a live interval, one entry seed determines all actual native records.
Only the first run's window bounds are required: locality propagates the
agreement to the second run, even for input-dependent head motions. -/
theorem record_eq_of_seed_eq {M : TM} {s a b : ℕ} {ai : ℤ} {aw : Fin M.k → ℤ}
    {w w' : List Bool}
    (hseed : seed M s a ai aw w = seed M s a ai aw w')
    (hip : (run M w a).inPos = (run M w' a).inPos)
    (hwp : (run M w a).workPos = (run M w' a).workPos)
    (hinput : ∀ t, a ≤ t → t < b → Fits s 0 ((run M w t).inPos-ai))
    (hwork : ∀ t, a ≤ t → t < b → ∀ j, Fits s 0 ((run M w t).workPos j-aw j))
    (hlive : ∀ t, a ≤ t → t < b → transAt M w t ≠ none) :
    ∀ t, a ≤ t → t < b → blockVal M 1 w t = blockVal M 1 w' t := by
  have hstate := congrArg Prod.fst hseed
  have hin := congrArg (fun z : Seed M s => z.2.1) hseed
  have hmem := congrArg (fun z : Seed M s => z.2.2) hseed
  have hloc := locality_interval (M := M) hstate hip hwp
    (fun t hta htb j => read_eq_of_capture_eq (0 : Fin (M.g+1))
      (congrFun hmem j) (hwork t hta htb j))
    (fun t hta htb => read_eq_of_capture_eq none hin (hinput t hta htb))
  intro t hta htb
  obtain ⟨hs,hi,hw,ht⟩ := hloc t hta htb.le
  exact record_eq_of_live_transition hs hi hw (ht htb) (hlive t hta htb)

/-- Actual image cardinality is bounded by any finite determining seed. -/
theorem card_image_le_of_seed {X Y Z : Type*} [DecidableEq Y] [Fintype Z]
    (S : Finset X) (f : X → Y) (g : X → Z)
    (h : ∀ x ∈ S, ∀ y ∈ S, g x = g y → f x = f y) :
    (S.image f).card ≤ Fintype.card Z := by
  classical
  let pick (z : S.image f) : X := (mem_image.mp z.property).choose
  have hp (z : S.image f) : pick z ∈ S ∧ f (pick z) = z :=
    (mem_image.mp z.property).choose_spec
  calc
    (S.image f).card = Fintype.card (S.image f) := (Fintype.card_coe _).symm
    _ ≤ Fintype.card Z := Fintype.card_le_of_injective (fun z => g (pick z)) (by
      intro z z' he
      apply Subtype.ext
      exact (hp z).2.symm.trans ((h _ (hp z).1 _ (hp z').1 he).trans (hp z').2))

/-- The seed alphabet is linear in the compiler's batch size in bits. -/
theorem seed_card_bound (M : TM) :
    ∃ A : ℕ, ∀ s (hs : 0<s), Fintype.card (Seed (machine M hs) s) ≤ 2^(A*s) := by
  obtain ⟨K,hK⟩ := control_bits M
  obtain ⟨J,hJ⟩ := ResourceBounds.exp_mul (ResourceBounds.exp_array 3 3)
    (ResourceBounds.exp_pow (ResourceBounds.exp_array (M.g+1) 3) M.k)
  refine ⟨K+J,fun s hs => ?_⟩
  have h := Nat.mul_le_mul (hK s hs) (hJ s hs)
  simpa only [Seed,Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,Cells,
    Fintype.card_option,Fintype.card_bool,machine_tapes,machine_alphabet,
    Nat.add_mul,pow_add] using h

/-- One positive coefficient works for all compiler batch sizes. -/
noncomputable def batchSeedBits (M : TM) : ℕ := (seed_card_bound M).choose + 1

theorem batchSeedBits_pos (M : TM) : 0 < batchSeedBits M := Nat.succ_pos _

theorem seed_card_le (M : TM) {s : ℕ} (hs : 0<s) :
    Fintype.card (Seed (machine M hs) s) ≤ 2^(batchSeedBits M*s) := by
  exact ((seed_card_bound M).choose_spec s hs).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right s (Nat.le_succ _)))

end TapeStorageRates.NativeBatchRecord
