import TransposeFollowup.RawSymbolWordApproximation
import TransposeFollowup.PhysicalAffineApproximationObstruction

/-! Transfer from proved primitive contracts to the high-entropy word
exclusion. Concrete palettes must supply their own semantics, cost and
geometry; this theorem does not assume that arbitrary primitives qualify. -/
namespace TransposeFollowup.RawSymbolWord
open Classical Set Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false
variable {O : Type*}

theorem no_high_entropy_transpose {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (cost : ℕ → O → ℕ)
    (code : ℕ → O → ℕ → NativeIO.Program (Fin 2) SharedRowBank.Mode)
    (value : ℕ → O → (ℕ → CopyMachine.Sym Bool) → ℕ → CopyMachine.Sym Bool)
    (ops : ℕ → List O) {C K J : ℕ} (hJ : 0<J)
    (hcorrect : ∀ᶠ i in atTop, Correct (inputLength (ns i)) (cost i) (code i) (value i))
    (hK : ∀ᶠ i in atTop, (ops i).length ≤ K)
    (hcost : ∀ᶠ i in atTop, ∀ op ∈ ops i, cost i op ≤ C*inputLength (ns i))
    (q : ℕ → O → ℕ → Fin 2 → ℝ → ℝ) (E : ℕ → ℝ)
    (hE : ∀ᶠ i in atTop, 0 ≤ E i)
    (hEL : Tendsto (fun i => E i/inputLength (ns i)) atTop (𝓝 0))
    (hcover : ∀ᶠ i in atTop, ∀ op ∈ ops i, ∀ A t H, 0 ≤ H →
      HasAffineIntervalCover J (q i op A t) H)
    (herror : ∀ᶠ i in atTop, ∀ op ∈ ops i, ∀ w A c x t,
      |((trajectory (code i op) w c (min (⌊x⌋₊-A) (cost i op))).work.pos t : ℝ)-
        c.work.pos t-q i op A t x| ≤ E i)
    {Ws : ℕ → Set (List Bool)} {ms : ℕ → ℕ}
    (hm : ∀ᶠ i in atTop, 2^inputLength (ns i) ≤ 2^ms i*(Ws i).ncard)
    (hmL : Tendsto (fun i => (ms i : ℝ)/inputLength (ns i)) atTop (𝓝 0))
    (hcorr : ∀ᶠ i in atTop, ∀ w ∈ Ws i, ∃ A : Matrix,
      w=encode (ns i) (entryBits (ns i)) A ∧
      output (inputLength (ns i)) (value i) (ops i) w=
        encode (ns i) (entryBits (ns i)) (transpose A)) : False := by
  let Ms : ℕ → TM := fun i => machine (inputLength (ns i)) (cost i) (code i) (ops i)
  apply no_subsequential_physical_affine_fast_approximation
    (k:=2) (G:=3) (c:=7+(C : ℝ)*K) hns (Ms:=Ms)
    (fun _ => rfl) (fun _ => by change max 1 (Nat.clog 2 5)=3; decide +kernel)
    (state_bits_vanish hns cost code ops hK hcost) hm hmL
  · filter_upwards [hcorr,hcorrect,hK,hcost] with i hi hci hki hti
    intro w hw
    obtain ⟨A,hA,hout⟩ := hi w hw
    have ht := (ticks_le (inputLength (ns i)) (cost i) (ops i) C hti).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left C hki) 7))
    obtain ⟨d,hs,_,ho,_⟩ := native_correct hci (ops i) w
    have hr := (stepN_init_eq_some_iff (ticks (inputLength (ns i)) (cost i) (ops i)) _).mp hs
    refine ⟨ticks (inputLength (ns i)) (cost i) (ops i),by exact_mod_cast ht,?_,A,hA,?_⟩
    · exact RawProgramShell.native_halts SharedRowBank.initialRowMode (inputLength (ns i))
        (ScheduledWord.ticks (cost i) (ops i)) (bodySchedule (cost i) (code i) (ops i))
        (body_active hci (ops i)) w
    · rw [hr.2,ho,List.reverse_reverse]
      exact hout
  · intro φ hφ ws _
    let H : ℝ := ((7+(C : ℝ)*K)*3+1)/3
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hpinf := (inputLength_tendsto hns).comp hφ.tendsto_atTop
    have hlim : Tendsto
        (fun i => (E (φ i)*(K : ℝ)+4)/(inputLength (ns (φ i)) : ℝ)) atTop (𝓝 0) := by
      have he := (hEL.comp hφ.tendsto_atTop).mul_const (K : ℝ)
      have hb : Tendsto (fun i => (4 : ℝ)/inputLength (ns (φ i))) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hpinf
      simpa only [zero_mul,add_zero,add_div,mul_div_right_comm,Function.comp_apply] using he.add hb
    refine ⟨id,strictMono_id,J^K*27,
      fun i => (E (φ i)*(K : ℝ)+4)/(inputLength (ns (φ i)) : ℝ),
      fun i t x => curve (inputLength (ns (φ i))) (cost (φ i)) (q (φ i)) (ops (φ i))
        ((RawProgramShell.encoding SharedRowBank.initialRowMode (inputLength (ns (φ i)))
          (ScheduledWord.ticks (cost (φ i)) (ops (φ i)))).port.symm t)
        ((inputLength (ns (φ i)) : ℝ)*x)/inputLength (ns (φ i)),hlim,?_⟩
    filter_upwards [hφ.tendsto_atTop.eventually hcorrect,hφ.tendsto_atTop.eventually hK,
      hφ.tendsto_atTop.eventually hE,hφ.tendsto_atTop.eventually hcover,
      hφ.tendsto_atTop.eventually herror,hpinf.eventually_gt_atTop 0] with i hci hki hei hqi hri hpi
    dsimp only [Function.comp_apply] at hpi
    have hp : 0 < inputLength (ns (φ i)) := by exact_mod_cast hpi
    have hrp : (0 : ℝ) < inputLength (ns (φ i)) := by exact_mod_cast hp
    have ha := scaled_approximation hp hci (q (φ i)) (ops (φ i)) hH (ws (φ i))
      (fun op hop A t => hqi op hop A t _ (mul_nonneg hrp.le hH))
      (fun op hop A c x t => hri op hop (ws (φ i)) A c x t)
    have hj : J^(ops (φ i)).length*27 ≤ J^K*27 :=
      Nat.mul_le_mul_right 27 (Nat.pow_le_pow_right hJ hki)
    refine ⟨fun t => (ha _).1.mono (by positivity) hj,?_⟩
    intro t x _
    have hx := (ha ((RawProgramShell.encoding SharedRowBank.initialRowMode
      (inputLength (ns (φ i))) (ScheduledWord.ticks (cost (φ i)) (ops (φ i)))).port.symm t)).2 x
    have hport := (RawProgramShell.encoding SharedRowBank.initialRowMode
      (inputLength (ns (φ i))) (ScheduledWord.ticks (cost (φ i)) (ops (φ i)))).port.apply_symm_apply t
    rw [hport] at hx
    have he : (E (φ i)*(ops (φ i)).length+4)/(inputLength (ns (φ i)) : ℝ) ≤
        (E (φ i)*(K : ℝ)+4)/(inputLength (ns (φ i)) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hrp.le
      have hlen : ((ops (φ i)).length : ℝ) ≤ K := by exact_mod_cast hki
      linarith [mul_le_mul_of_nonneg_left hlen hei]
    exact hx.trans he

end TransposeFollowup.RawSymbolWord
