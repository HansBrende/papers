import TapeStorageRates.BatchCoarseningGeometry
import TapeStorageRates.NativeBatchRecord
import TapeStorageRates.NativeTypicalDegree

/-! # A native cut charged by the joint support of full batch records -/

namespace TapeStorageRates

open Finset Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting
open BatchCoarsening NativeBatchRecord

set_option autoImplicit false
noncomputable section
open Classical

/-- The fixed reciprocal cut-budget coefficient pays for a batch seed and the coarse clock. -/
def jointCutCoefficient (M : TM) (C₀ : ℕ) : ℕ := 2 * batchSeedBits M * C₀

theorem jointCutCoefficient_pos (M : TM) {C₀ : ℕ} (hC : 0 < C₀) :
    0 < jointCutCoefficient M C₀ := by
  unfold jointCutCoefficient
  exact Nat.mul_pos (Nat.mul_pos (by decide) (batchSeedBits_pos M)) hC

/-- A dimension-independent coarse-clock coefficient for a source time bound. -/
def nativeJointClock (c : ℝ) : ℕ := 18 * ⌈max c 1⌉₊ + 10

/-- The fixed coefficient used by the native degree envelope. -/
def nativeJointCoefficient (M : TM) (c : ℝ) : ℕ :=
  jointCutCoefficient M (nativeJointClock c)

theorem nativeJointClock_pos (c : ℝ) : 0 < nativeJointClock c := by
  unfold nativeJointClock
  omega

theorem nativeJointCoefficient_pos (M : TM) (c : ℝ) :
    0 < nativeJointCoefficient M c := jointCutCoefficient_pos M (nativeJointClock_pos c)

/-- The compressed schedule length is linear in the source input length divided by s. -/
theorem native_joint_clock_bound {c : ℝ} (hc : 0 ≤ c) {s L t : ℕ}
    (hs : 0 < s) (hL : s ≤ L) (ht : (t : ℝ) ≤ c*((L:ℝ)+1)) :
    ((9*(t/s+1)+1 : ℕ) : ℝ) ≤ (nativeJointClock c : ℝ)*L/s := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hLs : (s : ℝ) ≤ L := by exact_mod_cast hL
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hs.trans_le hL
  have hdiv : ((t/s : ℕ):ℝ)*s ≤ t := by exact_mod_cast Nat.div_mul_le_self t s
  have hcceil : c ≤ (⌈max c 1⌉₊ : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have ht' : (t:ℝ) ≤ 2*c*L := ht.trans (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hL1)])
  have hcL := mul_le_mul_of_nonneg_right hcceil (Nat.cast_nonneg L (α := ℝ))
  apply (le_div_iff₀ hsR).mpr
  unfold nativeJointClock
  push_cast
  nlinarith

/-- Combine a chronological coarse representation with actual local batch windows.
The resulting genie contains full physical records; only their joint support is charged. -/
theorem exists_joint_cut_of_coarsening (M : TM) {s : ℕ} (hs : 0 < s)
    {X : Type*} (word : X → List Bool) (S : Finset X) (τ : Trace M.k)
    {T V C₀ L : ℕ} (hV : 0 < V) (hC : 0 < C₀)
    (ys : Fin M.k → ℕ → ℤ) (hy : ∀ h, IsWalk (ys h))
    (C : Coarsening τ.work T ys V (10*s+1))
    (hsize : (V : ℝ) ≤ C₀ * (L : ℝ) / s)
    (I : Finset ℕ) (lo hi : ℕ → ℕ)
    (howner : ∀ q < V, C.owner q ∈ I)
    (htrace : ∀ x ∈ S, trace (Native.machine M hs) (word x) = τ)
    (hwin : WindowIntervals τ s I lo hi)
    (hcover : ∀ t < T, lo (t/(10*s+1)) ≤ t ∧ t < hi (t/(10*s+1))) :
    ∃ Γ : Finset ℕ,
      ((S.image (fun x => fun t : Γ => blockVal (Native.machine M hs) 1 (word x) t)).card : ℝ) ≤
        (2:ℝ) ^ ((L:ℝ)/s) ∧
      ∀ π, IsDepPath τ.work T π → LinNet.GFree Γ π →
        π.length ≤ jointPhysicalDepth M.k (jointCutCoefficient M C₀) s + 1 := by
  let a := jointCutCoefficient M C₀
  let η : ℝ := 1 / ((a:ℝ)*s)
  have ha : 0 < a := jointCutCoefficient_pos M hC
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hCR : 0 < (C₀ : ℝ) := by exact_mod_cast hC
  have hKR : 0 < (batchSeedBits M : ℝ) := by exact_mod_cast batchSeedBits_pos M
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Γc, hΓV, hΓcost, hJcard, hpath⟩ := C.exists_cut_bounded hV hy hη
  let J := markedBatches C.owner Γc
  let Γ := wholeBatchCut T (10*s+1) C.owner Γc
  have hJI : J ⊆ I := by
    intro j hj
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hj
    exact howner q (mem_range.mp (hΓV hq))
  have hwinJ : WindowIntervals τ s J lo hi :=
    ⟨fun j hj => hwin.input j (hJI hj),
     fun j hj => hwin.work j (hJI hj),
     fun j hj => hwin.live j (hJI hj)⟩
  have hΓcover : ∀ t ∈ Γ, ∃ j ∈ J, lo j ≤ t ∧ t < hi j := by
    intro t ht
    obtain ⟨htT, hj⟩ := mem_wholeBatchCut.mp ht
    exact ⟨t/(10*s+1), hj, hcover t htT⟩
  have hjCost : (J.card : ℝ) ≤ η * V :=
    (Nat.cast_le.mpr hJcard).trans hΓcost
  have hbits : ((batchSeedBits M * s * J.card : ℕ) : ℝ) ≤ (L:ℝ)/s := by
    calc
      _ = (batchSeedBits M:ℝ)*s*J.card := by push_cast; rfl
      _ ≤ (batchSeedBits M:ℝ)*s*(η*V) :=
        mul_le_mul_of_nonneg_left hjCost (by positivity)
      _ = (V:ℝ)/(2*C₀) := by
        dsimp [η,a,jointCutCoefficient]
        push_cast
        field_simp
      _ ≤ ((C₀:ℝ)*L/s)/(2*C₀) := div_le_div_of_nonneg_right hsize (by positivity)
      _ = (L:ℝ)/(2*s) := by field_simp
      _ ≤ (L:ℝ)/s := div_le_div_of_nonneg_left (by positivity) hsR (by linarith)
  refine ⟨Γ, ?_, ?_⟩
  · calc
      _ ≤ ((2^(batchSeedBits M*s*J.card) : ℕ) : ℝ) := Nat.cast_le.mpr
        (compiler_joint_record_support M hs word S τ J lo hi htrace hwinJ Γ hΓcover)
      _ = (2:ℝ)^((batchSeedBits M*s*J.card : ℕ):ℝ) := by
        simp only [Nat.cast_pow,Nat.cast_ofNat,Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hbits
  · intro π hp hf
    have h := hpath π hp hf
    dsimp [η] at h
    rw [joint_genie_rescale] at h
    dsimp [a] at h
    apply h.trans
    simp only [jointPhysicalDepth,Nat.mul_add,Nat.mul_one]
    omega

end
end TapeStorageRates
