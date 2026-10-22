import TransposeFollowup.RawMaskedStrideRegularity
import TransposeFollowup.PhysicalAffineApproximationObstruction
import TransposeFollowup.LinearStateCount

/-! The complete raw masked-stride primitive cannot transpose a set of
coentropy o(P), even with arbitrary size-dependent public strides, masks
and prefix/difference choices. Every native-machine hypothesis is derived
from the paid executor, including its sublinear state-bit count. -/
namespace TransposeFollowup.RawMaskedStride
open Classical Set Filter Topology Transpose Transpose.Tape Transpose.Tape.Impl
open AffineMotion
set_option autoImplicit false

theorem cellBits_eq (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) :
    cellBits (machine isPrefix mask P S) = 3 := by
  unfold cellBits
  rw [(fixed_resources isPrefix mask P S).2.1]
  decide +kernel

theorem state_bits_vanish {ns S : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (hS : ∀ i, 0 < S i) (hSP : ∀ i, S i ≤ inputLength (ns i))
    (modes : ℕ → Bool) (masks : ℕ → ℕ → Bool) :
    Tendsto (fun i => (Nat.clog 2 ((machine (modes i) (masks i) (inputLength (ns i)) (S i)).q+1) : ℝ)
      / inputLength (ns i)) atTop (𝓝 0) := by
  let Q : ℕ → ℕ := fun i => (machine (modes i) (masks i) (inputLength (ns i)) (S i)).q+1
  have htime : ∀ᶠ i in atTop, (Q i : ℝ) ≤ 76*inputLength (ns i) := by
    apply Eventually.of_forall
    intro i
    have hp : 0 < inputLength (ns i) := lt_of_lt_of_le (hS i) (hSP i)
    have ht := ticks_le (inputLength (ns i)) (S i) (hSP i)
    have hq := (fixed_resources (modes i) (masks i) (inputLength (ns i)) (S i)).2.2
    have hbound : Q i ≤ 76*inputLength (ns i) := by dsimp [Q]; omega
    exact_mod_cast hbound
  exact state_bits_of_linear_count hns htime

theorem no_high_entropy_transpose {ns S : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (hS : ∀ i, 0 < S i) (hSP : ∀ i, S i ≤ inputLength (ns i))
    (modes : ℕ → Bool) (masks : ℕ → ℕ → Bool)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ A : Matrix,
      w = encode (ns i) (entryBits (ns i)) A ∧
      outputWord (modes i) (masks i) (inputLength (ns i)) (S i) w =
        encode (ns i) (entryBits (ns i)) (transpose A)) : False := by
  let Ms : ℕ → TM := fun i => machine (modes i) (masks i) (inputLength (ns i)) (S i)
  apply no_subsequential_physical_affine_fast_approximation (k:=2) (G:=3) (c:=18)
    hns (Ms:=Ms) (fun _ => rfl) (fun i => cellBits_eq _ _ _ _)
    (state_bits_vanish hns hS hSP modes masks) hm hmL
  · filter_upwards [hcorr] with i hi
    intro w hw
    obtain ⟨A,hA,hout⟩ := hi w hw
    obtain ⟨d,ht,hsteps,_,houtput,_⟩ :=
      native_correct (modes i) (masks i) (inputLength (ns i)) (hS i) (hSP i) w
    refine ⟨ticks (inputLength (ns i)) (S i),by exact_mod_cast ht,
      native_halts (modes i) (masks i) (inputLength (ns i)) (hS i) w,A,hA,?_⟩
    have hr := ((stepN_init_eq_some_iff _ _).mp hsteps).2
    change (run (machine (modes i) (masks i) (inputLength (ns i)) (S i)) w
      (ticks (inputLength (ns i)) (S i))).outRev.reverse = _
    rw [hr,houtput,List.reverse_reverse]
    exact hout
  · intro φ hφ ws _
    have hp (i : ℕ) : 0 < inputLength (ns (φ i)) := lt_of_lt_of_le (hS (φ i)) (hSP (φ i))
    obtain ⟨ψ,hψ,J,e,q,he,ha⟩ := full_affine_approximation_subsequence hp
      (fun i => hS (φ i)) (fun i => hSP (φ i))
      ((inputLength_tendsto hns).comp hφ.tendsto_atTop)
      (fun i => modes (φ i)) (fun i => masks (φ i)) (fun i => ws (φ i))
      (H:=((18 : ℝ)*3+1)/3) (by norm_num)
    refine ⟨ψ,hψ,J,e,fun i t => q i ((encoding (inputLength (ns (φ (ψ i)))) (S (φ (ψ i)))).port.symm t),he,?_⟩
    filter_upwards [ha] with i hi
    refine ⟨fun t => hi.1 _,?_⟩
    intro t x _
    have hx := hi.2 ((encoding (inputLength (ns (φ (ψ i)))) (S (φ (ψ i)))).port.symm t) x
    have hp := (encoding (inputLength (ns (φ (ψ i)))) (S (φ (ψ i)))).port.apply_symm_apply t
    rw [hp] at hx
    exact hx

end TransposeFollowup.RawMaskedStride
