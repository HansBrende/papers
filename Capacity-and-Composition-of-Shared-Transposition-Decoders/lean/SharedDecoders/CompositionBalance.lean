import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.Algebra.Group.Action.Option
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Tactic

/-!
# The finite orbit-divisor obstruction to balanced outputs

The acting group need not be linear. A normal subgroup of small index in a
transitive action has a common nontrivial orbit divisor. An invariant decoder
on tuples of pointed words cannot have fibers whose cardinalities are coprime
to that divisor. Joint transitivity on tuples is not assumed.
-/

namespace SharedDecoders

open MulAction
open scoped Pointwise BigOperators

variable {G Ω X ι Z : Type*} [Group G]

/-- A divisor of every orbit size divides the size of the finite acted-on set. -/
theorem dvd_card_of_dvd_orbits [MulAction G X] [Finite X] (m : ℕ)
    (h : ∀ x : X, m ∣ (orbit G x).ncard) : m ∣ Nat.card X := by
  classical
  let := Fintype.ofFinite (orbitRel.Quotient G X)
  rw [Nat.card_congr (selfEquivSigmaOrbits G X), Nat.card_sigma]
  exact Finset.dvd_sum (fun i _ => by simpa using h i.out)

/-- Normality makes the subgroup-orbit size constant in a transitive action. -/
theorem normal_orbit_ncard_eq [MulAction G Ω] [IsPretransitive G Ω]
    (N : Subgroup G) [N.Normal] (x y : Ω) :
    (orbit N x).ncard = (orbit N y).ncard := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  rw [← smul_orbit_eq_orbit_smul]
  exact (Set.ncard_image_of_injective (orbit N x)
    (by intro u v h; simpa using congrArg (fun w => g⁻¹ • w) h)).symm

/-- The number of normal-subgroup orbits divides the subgroup index. -/
theorem normal_orbit_stabilizer_index_dvd [MulAction G Ω]
    (N : Subgroup G) (x : Ω) :
    (stabilizer G (orbit N x)).index ∣ N.index := by
  apply Subgroup.index_dvd_of_le
  intro g hg
  change g • orbit N x = orbit N x
  exact MulAction.smul_orbit (G := N) ⟨g, hg⟩ x

/-- The exact block equation supplies a nontrivial common orbit divisor when
the normal subgroup has smaller index than the transitive set. -/
theorem normal_orbit_divisor [Finite G] [Finite Ω] [Nonempty Ω]
    [MulAction G Ω] [IsPretransitive G Ω]
    (N : Subgroup G) [N.Normal] (hindex : N.index < Nat.card Ω) (x : Ω) :
    1 < (orbit N x).ncard ∧ (orbit N x).ncard ∣ Nat.card Ω := by
  have hb : IsBlock G (orbit N x) := IsBlock.orbit_of_normal x
  have hnon : (orbit N x).Nonempty := ⟨x, mem_orbit_self x⟩
  have hprod := hb.ncard_block_mul_ncard_orbit_eq hnon
  rw [← index_stabilizer G (orbit N x)] at hprod
  have hi : (stabilizer G (orbit N x)).index ≤ N.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero N.index_ne_zero_of_finite)
      (normal_orbit_stabilizer_index_dvd N x)
  have hpos : 0 < (orbit N x).ncard := hnon.ncard_pos
  refine ⟨?_, hb.ncard_dvd_card hnon⟩
  by_contra h
  have heq : (orbit N x).ncard = 1 := by omega
  rw [heq, one_mul] at hprod
  omega

/-- An invariant fiber of tuples, excluding the distinguished all-`none`
tuple, is divisible by the common nonzero-word orbit size. -/
theorem invariant_fiber_dvd [Finite G] [Finite Ω] [Finite ι]
    [MulAction G Ω] [IsPretransitive G Ω]
    (N : Subgroup G) [N.Normal] (x₀ : Ω)
    (f : (ι → Option Ω) → Z)
    (hinv : ∀ (n : N) x, f (n • x) = f x)
    (z : Z) (hz : z ≠ f (fun _ => none)) :
    (orbit N x₀).ncard ∣ Nat.card {x : ι → Option Ω // f x = z} := by
  classical
  let : MulAction N {x : ι → Option Ω // f x = z} := {
    smul := fun n x => ⟨n • x.val, (hinv n x.val).trans x.property⟩
    one_smul := fun x => Subtype.ext (one_smul N x.val)
    mul_smul := fun n m x => Subtype.ext (mul_smul n m x.val) }
  apply dvd_card_of_dvd_orbits (G := N)
  intro x
  have hne : x.val ≠ fun _ => none := by
    intro h
    apply hz
    rw [← x.property, h]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists.mp hi
  have hstab : stabilizer N x ≤ stabilizer N u := by
    intro n hn
    change n • x = x at hn
    have hv := congrFun (congrArg Subtype.val hn) i
    change n • x.val i = x.val i at hv
    rw [← hu, Option.smul_some, Option.some.injEq] at hv
    exact hv
  have hd := Subgroup.index_dvd_of_le hstab
  rw [index_stabilizer, index_stabilizer] at hd
  rwa [normal_orbit_ncard_eq N x₀ u]

/-- Balanced power-sized fibers are impossible under the actual normal action.
The hypotheses are group-action properties, not a prescribed failure set. -/
theorem no_balanced_normal_action [Finite G] [Finite Ω] [Nonempty Ω] [Finite ι]
    [MulAction G Ω] [IsPretransitive G Ω]
    (N : Subgroup G) [N.Normal] (a n : ℕ)
    (hindex : N.index < Nat.card Ω) (hcop : Nat.Coprime a (Nat.card Ω))
    (f : (ι → Option Ω) → Z)
    (hinv : ∀ (g : N) x, f (g • x) = f x)
    (z : Z) (hz : z ≠ f (fun _ => none))
    (hbalanced : Nat.card {x : ι → Option Ω // f x = z} = a ^ n) : False := by
  classical
  let x₀ : Ω := Classical.choice inferInstance
  obtain ⟨hlt, hdiv⟩ := normal_orbit_divisor N hindex x₀
  have hd := invariant_fiber_dvd N x₀ f hinv z hz
  rw [hbalanced] at hd
  have hc : Nat.Coprime (orbit N x₀).ncard a :=
    (hcop.of_dvd_right hdiv).symm
  have heq : (orbit N x₀).ncard = 1 :=
    (hc.pow_right n).eq_one_of_dvd hd
  omega

section Covariance

variable {C : Type*} [Group C] [MulAction G X] [MulAction C Z]

/-- Elements for which a decoder transforms by some output action form a
subgroup, including inverses. -/
def covarianceSubgroup (f : X → Z) : Subgroup G where
  carrier := {g | ∃ c : C, ∀ x, f (g • x) = c • f x}
  one_mem' := ⟨1, by intro x; simp⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨e, he⟩
    exact ⟨c * e, fun x => by rw [mul_smul, hc, he, mul_smul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    intro x
    have h := congrArg (fun z => c⁻¹ • z) (hc (g⁻¹ • x))
    simpa using h.symm

/-- Covariance on generators propagates to their actual generated group. -/
theorem covariance_on_generated (f : X → Z) (S : Set G)
    (hgen : Subgroup.closure S = ⊤)
    (hS : ∀ g ∈ S, ∃ c : C, ∀ x, f (g • x) = c • f x) :
    ∀ g : G, ∃ c : C, ∀ x, f (g • x) = c • f x := by
  have hle : Subgroup.closure S ≤ covarianceSubgroup (C := C) f :=
    (Subgroup.closure_le _).mpr hS
  rw [hgen] at hle
  exact fun g => hle (by trivial)

/-- Surjectivity and a faithful output action make the covariance phase unique. -/
theorem covariance_phase_unique [FaithfulSMul C Z] (f : X → Z)
    (hsur : Function.Surjective f) {g : G} {c e : C}
    (hc : ∀ x, f (g • x) = c • f x)
    (he : ∀ x, f (g • x) = e • f x) : c = e := by
  apply eq_of_smul_eq_smul (α := Z)
  intro z
  obtain ⟨x, rfl⟩ := hsur z
  exact (hc x).symm.trans (he x)

/-- The output phase is an actual group homomorphism, not a chosen
presentation or an assumed quotient. -/
noncomputable def covarianceHom [FaithfulSMul C Z] (f : X → Z)
    (hsur : Function.Surjective f)
    (hc : ∀ g : G, ∃ c : C, ∀ x, f (g • x) = c • f x) : G →* C where
  toFun g := (hc g).choose
  map_one' := covariance_phase_unique f hsur (hc 1).choose_spec (by intro x; simp)
  map_mul' g h := covariance_phase_unique f hsur (hc (g * h)).choose_spec
    (by intro x; rw [mul_smul, (hc g).choose_spec, (hc h).choose_spec, mul_smul])

theorem covarianceHom_spec [FaithfulSMul C Z] (f : X → Z)
    (hsur : Function.Surjective f)
    (hc : ∀ g : G, ∃ c : C, ∀ x, f (g • x) = c • f x) (g : G) (x : X) :
    f (g • x) = covarianceHom f hsur hc g • f x := (hc g).choose_spec x

end Covariance

/-- Complete orbit-balance obstruction from covariance on any generating set.
The pointed word type is represented as `Option Ω`; `none` is the fixed word.
Only the scalar action on `Ω` is transitive. -/
theorem no_balanced_generated_covariance
    {C : Type*} [Group C] [Finite C] [MulAction C Z] [FaithfulSMul C Z]
    [Finite G] [Finite Ω] [Nonempty Ω] [Finite ι]
    [MulAction G Ω] [IsPretransitive G Ω]
    (a n : ℕ) (hsize : Nat.card C < Nat.card Ω)
    (hcop : Nat.Coprime a (Nat.card Ω))
    (f : (ι → Option Ω) → Z) (hsur : Function.Surjective f)
    (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hS : ∀ g ∈ S, ∃ c : C, ∀ x, f (g • x) = c • f x)
    (z : Z) (hz : z ≠ f (fun _ => none))
    (hbalanced : Nat.card {x : ι → Option Ω // f x = z} = a ^ n) : False := by
  let hc := covariance_on_generated f S hgen hS
  let θ := covarianceHom f hsur hc
  have hindex : θ.ker.index < Nat.card Ω := by
    rw [Subgroup.index_ker]
    exact (Nat.card_le_card_of_injective (Subtype.val : θ.range → C)
      Subtype.val_injective).trans_lt hsize
  have hinv : ∀ (g : θ.ker) x, f (g • x) = f x := by
    intro g x
    have h := covarianceHom_spec f hsur hc g.val x
    have hg : θ g.val = 1 := g.property
    change f (g.val • x) = f x
    change f (g.val • x) = θ g.val • f x at h
    simpa [hg] using h
  exact no_balanced_normal_action θ.ker a n hindex hcop f hinv z hz hbalanced

/-- The pointed-word version: the distinguished word and its complement are
derived from an actual finite word alphabet. This transports the complete tuple
domain, not just a selected correctness sector. -/
theorem no_balanced_pointed_covariance
    {C W : Type*} [Group C] [Finite C] [MulAction C Z] [FaithfulSMul C Z]
    [Finite G] [Finite W] [Nontrivial W] [Finite ι]
    [MulAction G W] (w₀ : W)
    (hfix : ∀ g : G, g • w₀ = w₀)
    (htrans : ∀ x ≠ w₀, ∀ y ≠ w₀, ∃ g : G, g • x = y)
    (a n : ℕ) (hsize : Nat.card C < Nat.card W - 1)
    (hcop : Nat.Coprime a (Nat.card W - 1))
    (f : (ι → W) → Z) (hsur : Function.Surjective f)
    (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hS : ∀ g ∈ S, ∃ c : C, ∀ x, f (g • x) = c • f x)
    (z : Z) (hz : z ≠ f (fun _ => w₀))
    (hbalanced : Nat.card {x : ι → W // f x = z} = a ^ n) : False := by
  classical
  let Ω := {w : W // w ≠ w₀}
  let : MulAction G Ω := {
    smul := fun g x => ⟨g • x.val, by
      intro h
      apply x.property
      calc
        x.val = g⁻¹ • (g • x.val) := (inv_smul_smul g x.val).symm
        _ = g⁻¹ • w₀ := by rw [h]
        _ = w₀ := hfix _⟩
    one_smul := fun x => Subtype.ext (one_smul G x.val)
    mul_smul := fun g h x => Subtype.ext (mul_smul g h x.val) }
  let : IsPretransitive G Ω := ⟨fun x y => by
    obtain ⟨g, hg⟩ := htrans x.val x.property y.val y.property
    exact ⟨g, Subtype.ext hg⟩⟩
  let : Nonempty Ω := by
    obtain ⟨w, hw⟩ := exists_ne w₀
    exact ⟨⟨w, hw⟩⟩
  have hcard : Nat.card Ω = Nat.card W - 1 := by
    let := Fintype.ofFinite W
    simp [Ω, Nat.card_eq_fintype_card]
  let E : (ι → Option Ω) ≃ (ι → W) :=
    Equiv.piCongrRight (fun _ => Equiv.optionSubtypeNe w₀)
  have hE (g : G) (x : ι → Option Ω) : E (g • x) = g • E x := by
    funext i
    change Equiv.optionSubtypeNe w₀ (g • x i) = g • Equiv.optionSubtypeNe w₀ (x i)
    cases h : x i with
    | none => simpa using (hfix g).symm
    | some u => rfl
  let f' : (ι → Option Ω) → Z := f ∘ E
  have hsur' : Function.Surjective f' := hsur.comp E.surjective
  have hS' : ∀ g ∈ S, ∃ c : C, ∀ x, f' (g • x) = c • f' x := by
    intro g hg
    obtain ⟨c, hc⟩ := hS g hg
    refine ⟨c, ?_⟩
    intro x
    change f (E (g • x)) = c • f (E x)
    rw [hE, hc]
  have hz' : z ≠ f' (fun _ => none) := by
    have hE0 : E (fun _ => none) = fun _ => w₀ := rfl
    change z ≠ f (E (fun _ => none))
    rw [hE0]
    exact hz
  have hb' : Nat.card {x : ι → Option Ω // f' x = z} = a ^ n := by
    have he := Nat.card_congr (E.subtypeEquiv
      (p := fun x => f' x = z) (q := fun x => f x = z) (fun _ => Iff.rfl))
    exact he.trans hbalanced
  exact no_balanced_generated_covariance a n (by simpa [hcard] using hsize)
    (by simpa [hcard] using hcop)
    f' hsur' S hgen hS' z hz' hb'

end SharedDecoders
