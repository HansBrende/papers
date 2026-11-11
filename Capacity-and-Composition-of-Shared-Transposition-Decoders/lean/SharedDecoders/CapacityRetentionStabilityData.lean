import SharedDecoders.CapacityRetentionAverage
import Mathlib.Algebra.Order.Floor.Semifield
import LeanMachine.BoundedLiminf

/-! Actual source data and finite rate estimates for retention stability.
The field, lane space, dimension and class set may all vary with the sample. -/

namespace SharedDecoders.RetentionAverage

open Module Filter
open scoped BigOperators Topology

theorem meanGcd_ge_one {d : ℕ} [NeZero d] : 1 ≤ meanGcd d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  apply (le_div_iff₀ hd).mpr
  have hh : (∑ _s : ZMod d, (1 : ℝ)) ≤ ∑ s : ZMod d, (Nat.gcd d s.val : ℝ) := by
    apply Finset.sum_le_sum
    intro s _
    exact_mod_cast Nat.gcd_pos_of_pos_left s.val (NeZero.pos d)
  simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
    one_mul] using hh

/-- A complete shared-code sample. No numerical capacity estimate is a field
of this structure: every estimate below is derived from `shared`. -/
structure Sample where
  d : ℕ
  [dimensionNeZero : NeZero d]
  F : Type u
  A : Type v
  κ : Type w
  [field : Field F]
  [addGroup : AddCommGroup A]
  [module : Module F A]
  [finiteDimensional : FiniteDimensional F A]
  [classesFinite : Fintype κ]
  positiveWidth : 0 < finrank F A
  p : ZMod d → κ
  C : Submodule F (State d A)
  shared : IsSharedCode F p C

attribute [instance] Sample.dimensionNeZero Sample.field Sample.addGroup
  Sample.module Sample.finiteDimensional Sample.classesFinite

namespace Sample

noncomputable def volume (S : Sample) : ℝ := (finrank S.F S.A : ℝ)*(S.d : ℝ)^2
noncomputable def rate (S : Sample) : ℝ := (finrank S.F S.C : ℝ)/S.volume
noncomputable def loss (S : Sample) : ℝ :=
  ((finrank S.F (symmetricSpace (F := S.F) (A := S.A) (I := ZMod S.d)) : ℝ)-
    finrank S.F (S.C ⊓ symmetricSpace : Submodule S.F (State S.d S.A)))/S.volume
noncomputable def classes (S : Sample) : ℝ := Fintype.card S.κ
noncomputable def gcdCost (S : Sample) : ℝ := (meanGcd S.d-1)/(2*S.d)

theorem volume_pos (S : Sample) : 0 < S.volume := by
  have hd : (0 : ℝ) < S.d := by exact_mod_cast NeZero.pos S.d
  have hb : (0 : ℝ) < finrank S.F S.A := by exact_mod_cast S.positiveWidth
  dsimp [volume]
  positivity

theorem classes_ge_one (S : Sample) : 1 ≤ S.classes := by
  have hi : Nonempty S.κ := ⟨S.p 0⟩
  change (1 : ℝ) ≤ (Fintype.card S.κ : ℝ)
  exact_mod_cast (show 1 ≤ Fintype.card S.κ from Fintype.card_pos_iff.mpr hi)

theorem rate_bounds (S : Sample) : 0 ≤ S.rate ∧ S.rate ≤ 1 := by
  refine ⟨div_nonneg (Nat.cast_nonneg _) S.volume_pos.le, ?_⟩
  apply (div_le_one S.volume_pos).mpr
  have hh := (Submodule.finrank_le S.C).trans_eq (finrank_state (F := S.F) (A := S.A))
  have hc : (finrank S.F S.C : ℝ) ≤ (S.d : ℝ)*S.d*finrank S.F S.A := by exact_mod_cast hh
  dsimp [volume]
  nlinarith only [hc]

theorem loss_bounds (S : Sample) : 0 ≤ S.loss ∧ S.loss ≤ 1 := by
  have hle : (finrank S.F (S.C ⊓ symmetricSpace : Submodule S.F (State S.d S.A)) : ℝ) ≤
      finrank S.F (symmetricSpace (F := S.F) (A := S.A) (I := ZMod S.d)) := by
    exact_mod_cast Submodule.finrank_mono (inf_le_right :
      S.C ⊓ symmetricSpace ≤ (symmetricSpace : Submodule S.F (State S.d S.A)))
  refine ⟨div_nonneg (sub_nonneg.mpr hle) S.volume_pos.le, ?_⟩
  apply (div_le_one S.volume_pos).mpr
  have hh := (Submodule.finrank_le (symmetricSpace : Submodule S.F (State S.d S.A))).trans_eq
    (finrank_state (F := S.F) (A := S.A))
  have hc : (finrank S.F (symmetricSpace (F := S.F) (A := S.A) (I := ZMod S.d)) : ℝ) ≤
      (S.d : ℝ)*S.d*finrank S.F S.A := by exact_mod_cast hh
  have hn := Nat.cast_nonneg (α := ℝ)
    (finrank S.F (S.C ⊓ symmetricSpace : Submodule S.F (State S.d S.A)))
  dsimp [volume]
  nlinarith only [hc,hn]

theorem gcdCost_nonneg (S : Sample) : 0 ≤ S.gcdCost := by
  exact div_nonneg (sub_nonneg.mpr meanGcd_ge_one) (by positivity)

theorem normalized (S : Sample) (k : ℕ) :
    S.rate ≤ 1/2+1/(2*S.d)+(2*(k : ℝ)-1)*S.loss+
      (k : ℝ)*S.gcdCost+2*S.classes^2/(k+2)^2 := by
  have hh := S.shared.retention_normalized k S.positiveWidth
  dsimp only at hh
  change S.rate-((S.d : ℝ)+1)/(2*S.d) ≤
    (2*(k : ℝ)-1)*S.loss+(k : ℝ)*(meanGcd S.d-1)/(2*S.d)+
      2*S.classes^2/(k+2)^2 at hh
  have hd : (0 : ℝ) < S.d := by exact_mod_cast NeZero.pos S.d
  have he : ((S.d : ℝ)+1)/(2*S.d)=1/2+1/(2*S.d) := by field_simp
  rw [he] at hh
  dsimp [gcdCost]
  rw [← mul_div_assoc]
  linarith

/-- A free real tuning parameter eliminates the varying integer shift count. -/
theorem tradeoff (S : Sample) (t : ℝ) (ht : 1 ≤ t) :
    S.rate ≤ 1/2+1/(2*S.d)+4*t*(S.classes*(S.loss+S.gcdCost))+2/t^2 := by
  let k : ℕ := ⌈S.classes*t⌉₊
  have hM := S.classes_ge_one
  have ht0 : 0 < t := by linarith
  have hMt : 1 ≤ S.classes*t := by nlinarith
  have hklo : S.classes*t ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ 2*S.classes*t := by
    have hh : (k : ℝ) < S.classes*t+1 := Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hh := S.normalized k
  have hloss := mul_le_mul_of_nonneg_right
    (show 2*(k : ℝ)-1 ≤ 4*S.classes*t by linarith) S.loss_bounds.1
  have hgcd := mul_le_mul_of_nonneg_right hkhi S.gcdCost_nonneg
  have htail : 2*S.classes^2/((k : ℝ)+2)^2 ≤ 2/t^2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hsq : (S.classes*t)^2 ≤ ((k : ℝ)+2)^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith only [hsq]
  have hnonneg := mul_nonneg (show 0 ≤ S.classes*t by positivity) S.gcdCost_nonneg
  nlinarith only [hh,hloss,hgcd,htail,hnonneg]

end Sample
end SharedDecoders.RetentionAverage
