import SharedDecoders.CapacityMaskGraphQuotient
import SharedDecoders.CapacityMaskMethods

/-! # The actual direct numerical certificate under shifts and small cardinalities -/

namespace SharedDecoders.CapacityMask

open Module CapacityRuns
open scoped BigOperators

variable {d : ℕ} [NeZero d] {κ : Type*}

omit [NeZero d] in
theorem link_translate_iff (p : ZMod d → κ) (Δ : Finset (ZMod d)) (t x y : ZMod d) :
    Link p (Δ.image (fun s => s+t)) x y ↔ Link p Δ x y := by
  constructor
  · rintro ⟨hp,u,hu,v,hv,he⟩
    obtain ⟨u0,hu0,heu⟩ := Finset.mem_image.mp hu
    obtain ⟨v0,hv0,hev⟩ := Finset.mem_image.mp hv
    rw [← heu,← hev] at he
    exact ⟨hp,u0,hu0,v0,hv0,by linear_combination he⟩
  · rintro ⟨hp,u,hu,v,hv,he⟩
    exact ⟨hp,u+t,Finset.mem_image_of_mem _ hu,v+t,Finset.mem_image_of_mem _ hv,
      by linear_combination he⟩

theorem componentCount_translate (p : ZMod d → κ) (Δ : Finset (ZMod d)) (t : ZMod d) :
    componentCount p (Δ.image (fun s => s+t))=componentCount p Δ := by
  have he : Link p (Δ.image (fun s => s+t))=Link p Δ := by
    funext x y
    exact propext (link_translate_iff p Δ t x y)
  simp only [componentCount,LinkComponent,he]

theorem componentCount_singleton (p : ZMod d → κ) (a : ZMod d) :
    componentCount p {a}=d := by
  have hh := componentCount_translate p {0} a
  simpa only [Finset.image_singleton,zero_add,componentCount_zero] using hh

theorem componentCount_pair (p : ZMod d → κ) (a b : ZMod d) :
    componentCount p {a,b}=componentCount p (extendShifts {0} (b-a)) := by
  have hh := componentCount_translate p {a,b} (-a)
  simpa only [Finset.image_insert,Finset.image_singleton,add_neg_cancel,
    ← sub_eq_add_neg,sub_self,extendShifts,zero_add,Finset.singleton_union] using hh.symm

noncomputable def directCertificate (p : ZMod d → κ) (b : ℕ) (Δ : Finset (ZMod d)) : ℝ :=
  (((Δ.card-1 : ℕ) : ℝ)*(b : ℝ)*d^2+(b : ℝ)*d*componentCount p Δ)/(Δ.card : ℝ)

theorem directCertificate_eq_gain (p : ZMod d → κ) (b : ℕ) (Δ : Finset (ZMod d))
    (hΔ : Δ.Nonempty) : directCertificate p b Δ=(b : ℝ)*d^2*(1-directGain p Δ) := by
  have hcard : 1≤Δ.card := hΔ.card_pos
  have hc : (Δ.card : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hΔ.card_pos
  have hd : (d : ℝ)≠0 := by exact_mod_cast NeZero.ne d
  rw [directCertificate,directGain,Nat.cast_sub hcard,Nat.cast_one]
  field_simp
  ring

theorem directCertificate_singleton (p : ZMod d → κ) (b : ℕ) (a : ZMod d) :
    directCertificate p b {a}=(b : ℝ)*d^2 := by
  simp only [directCertificate,Finset.card_singleton,Nat.sub_self,Nat.cast_zero,
    componentCount_singleton,Nat.cast_one,zero_mul,zero_add,div_one]
  ring

theorem directCertificate_large (p : ZMod d → κ) (b : ℕ) (Δ : Finset (ZMod d))
    (hΔ : 3≤Δ.card) : (2/3)*(b : ℝ)*d^2≤directCertificate p b Δ := by
  have hcard : 1≤Δ.card := by omega
  have hc : (0 : ℝ)<Δ.card := by exact_mod_cast (by omega : 0<Δ.card)
  have hc3 : (3 : ℝ)≤Δ.card := by exact_mod_cast hΔ
  rw [directCertificate,Nat.cast_sub hcard,Nat.cast_one]
  apply (le_div_iff₀ hc).mpr
  have hmul := mul_nonneg (show (0 : ℝ)≤Δ.card-3 by linarith)
    (show (0 : ℝ)≤(b : ℝ)*d^2 by positivity)
  have hterm : (0 : ℝ)≤(b : ℝ)*d*componentCount p Δ := by positivity
  nlinarith only [hmul,hterm]

/-- A lower bound on the actual directed change counts controls every direct
shift set; larger sets are handled by their ambient term. -/
theorem directCertificate_floor_of_changes (p : ZMod d → Bool) (b : ℕ) (c : ℝ)
    (hc : c≤1/3) (hevent : ∀ s : ZMod d, s≠0 → c*d≤(changeCount p s : ℝ))
    (Δ : Finset (ZMod d)) (hΔ : Δ.Nonempty) :
    ((1+c)/2)*(b : ℝ)*d^2≤directCertificate p b Δ := by
  classical
  by_cases hcard1 : Δ.card=1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hcard1
    rw [directCertificate_singleton]
    have hh := mul_nonneg (show 0≤1-c by linarith) (show (0 : ℝ)≤(b : ℝ)*d^2 by positivity)
    nlinarith only [hh]
  by_cases hcard2 : Δ.card=2
  · obtain ⟨a,t,hat,rfl⟩ := Finset.card_eq_two.mp hcard2
    have ht : t-a≠0 := sub_ne_zero.mpr (Ne.symm hat)
    have hcount : c*d≤(componentCount p {a,t} : ℝ) := by
      rw [componentCount_pair]
      exact (hevent _ ht).trans (by exact_mod_cast changeCount_le_first_components p (t-a))
    have hm := mul_le_mul_of_nonneg_left hcount (show (0 : ℝ)≤(b : ℝ)*d by positivity)
    simp only [directCertificate,hcard2,Nat.reduceSub,Nat.cast_one,Nat.cast_ofNat,one_mul]
    nlinarith only [hm]
  · have hlarge := directCertificate_large p b Δ (by have := hΔ.card_pos; omega)
    have hh := mul_nonneg (show 0≤1/3-c by linarith) (show (0 : ℝ)≤(b : ℝ)*d^2 by positivity)
    nlinarith only [hlarge,hh]

end SharedDecoders.CapacityMask
