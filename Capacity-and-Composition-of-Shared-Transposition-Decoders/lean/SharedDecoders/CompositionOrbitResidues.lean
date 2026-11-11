import SharedDecoders.CompositionBalance
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Data.Nat.ModEq

/-! # Fixed-word residues for balanced decoders

The divisor condition concerns scalar-word orbits. Stabilizer inclusion derives
the corresponding tuple condition; no transitivity of either action is used.
-/

namespace SharedDecoders

open MulAction
open scoped BigOperators

variable {G X W ι Z : Type*} [Group G]

/-- The class equation modulo any common divisor of non-singleton orbits. -/
theorem card_modEq_fixedPoints [MulAction G X] [Finite X] (m : ℕ)
    (hdiv : ∀ x : X, x ∉ fixedPoints G X → m ∣ (orbit G x).ncard) :
    Nat.card X ≡ Nat.card (fixedPoints G X) [MOD m] := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite (fixedPoints G X)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card X = Fintype.card
        (Σ y : Quotient (orbitRel G X), {x // Quotient.mk'' x = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G X))).symm
    _ = ∑ a : Quotient (orbitRel G X), Fintype.card {x // Quotient.mk'' x = a} :=
      Fintype.card_sigma
    _ ≡ ∑ _a : fixedPoints G X, 1 [MOD m] := by
      rw [← ZMod.natCast_eq_natCast_iff _ _ m, Nat.cast_sum, Nat.cast_sum]
      have key (x : X) :
          Fintype.card {y // (Quotient.mk'' y : Quotient (orbitRel G X)) =
            Quotient.mk'' x} = Fintype.card (orbit G x) := by
        simp only [Quotient.eq'']
        congr
      refine Eq.symm (Finset.sum_bij_ne_zero
        (fun a _ _ => Quotient.mk'' a.val) (fun _ _ _ => Finset.mem_univ _)
        (fun a₁ _ _ a₂ _ _ h =>
          Subtype.ext (mem_fixedPoints'.mp a₂.property a₁.val (Quotient.exact' h)))
        (fun b => Quotient.inductionOn' b fun b _ hb => ?_)
        (fun a _ _ => by rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.property]))
      have hfix : b ∈ fixedPoints G X := by
        by_contra h
        have hd : m ∣ Fintype.card (orbit G b) := by
          have hd := hdiv b h
          change m ∣ Nat.card (orbit G b) at hd
          rwa [Nat.card_eq_fintype_card] at hd
        apply hb
        rw [key, ZMod.natCast_eq_zero_iff]
        exact hd
      exact ⟨⟨b, hfix⟩, Finset.mem_univ _, by
        simpa only [key, mem_fixedPoints_iff_card_orbit_eq_one.mp hfix,
          Nat.cast_one] using hb, rfl⟩
    _ = Fintype.card (fixedPoints G X) := by simp

/-- A moved tuple contains a moved scalar word, whose stabilizer contains the
tuple stabilizer. Its orbit size therefore divides the tuple orbit size. -/
theorem tuple_orbit_divisor [MulAction G W] [Finite W] [Finite ι] (m : ℕ)
    (hdiv : ∀ w : W, w ∉ fixedPoints G W → m ∣ (orbit G w).ncard)
    (x : ι → W) (hx : x ∉ fixedPoints G (ι → W)) :
    m ∣ (orbit G x).ncard := by
  have hi : ∃ i, x i ∉ fixedPoints G W := by
    by_contra h
    apply hx
    intro g
    funext i
    exact (not_exists.mp h i |> not_not.mp) g
  obtain ⟨i, hi⟩ := hi
  have hstab : stabilizer G x ≤ stabilizer G (x i) := by
    intro g hg
    exact congrFun hg i
  have hd := Subgroup.index_dvd_of_le hstab
  rw [index_stabilizer, index_stabilizer] at hd
  exact (hdiv (x i) hi).trans hd

/-- Fixed tuples are exactly tuples of fixed scalar words. -/
def fixedTupleEquiv [MulAction G W] :
    fixedPoints G (ι → W) ≃ (ι → fixedPoints G W) where
  toFun x i := ⟨x.val i, fun g => congrFun (x.property g) i⟩
  invFun x := ⟨fun i => (x i).val, fun g => funext (fun i => (x i).property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every invariant fibre contains at least the least residue of its size
many fixed tuples. -/
theorem invariant_fiber_fixed_residue [MulAction G X] [Finite X]
    (m : ℕ) (hdiv : ∀ x : X, x ∉ fixedPoints G X → m ∣ (orbit G x).ncard)
    (f : X → Z) (hinv : ∀ (g : G) x, f (g • x) = f x) (z : Z) :
    Nat.card {x : X // f x = z} % m ≤
      Nat.card {x : fixedPoints G X // f x.val = z} := by
  classical
  let Y := {x : X // f x = z}
  let : MulAction G Y := {
    smul := fun g x => ⟨g • x.val, (hinv g x.val).trans x.property⟩
    one_smul := fun x => Subtype.ext (one_smul G x.val)
    mul_smul := fun g h x => Subtype.ext (mul_smul g h x.val) }
  have hd (x : Y) (hx : x ∉ fixedPoints G Y) : m ∣ (orbit G x).ncard := by
    have hx' : x.val ∉ fixedPoints G X := by
      intro h
      apply hx
      exact fun g => Subtype.ext (h g)
    have hs : stabilizer G x = stabilizer G x.val := by
      ext g
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have h := hdiv x.val hx'
    rwa [← index_stabilizer, ← hs, index_stabilizer] at h
  let E : fixedPoints G Y ≃ {x : fixedPoints G X // f x.val = z} := {
    toFun := fun x => ⟨⟨x.val.val, fun g => congrArg Subtype.val (x.property g)⟩,
      x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, fun g => Subtype.ext (x.val.property g)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := card_modEq_fixedPoints (G := G) m hd
  change Nat.card Y % m = _ at hc
  rw [Nat.card_congr E] at hc
  rw [hc]
  exact Nat.mod_le _ _

/-- Fixed-word residue test. This works for any orbit divisor, not only a
prime. The advertised prime-coprime consequence is a specialization. -/
theorem balanced_fixed_word_residue [MulAction G W] [Finite W] [Finite ι]
    [Fintype Z] (m F : ℕ)
    (hdiv : ∀ w : W, w ∉ fixedPoints G W → m ∣ (orbit G w).ncard)
    (f : (ι → W) → Z) (hinv : ∀ (g : G) x, f (g • x) = f x)
    (hbalanced : ∀ z, Nat.card {x : ι → W // f x = z} = F) :
    Fintype.card Z * (F % m) ≤ Nat.card (fixedPoints G W) ^ Nat.card ι := by
  classical
  have hz (z : Z) : F % m ≤
      Nat.card {x : fixedPoints G (ι → W) // f x.val = z} := by
    simpa [hbalanced] using invariant_fiber_fixed_residue m
      (tuple_orbit_divisor m hdiv) f hinv z
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hz z)
  have hc := Nat.card_congr (Equiv.sigmaFiberEquiv
    (fun x : fixedPoints G (ι → W) => f x.val))
  rw [Nat.card_sigma] at hc
  have hfix : Nat.card (fixedPoints G (ι → W)) =
      Nat.card (fixedPoints G W) ^ Nat.card ι := by
    rw [Nat.card_congr (fixedTupleEquiv (G := G) (W := W) (ι := ι))]
    exact Nat.card_fun
  simpa [hc, hfix] using h

/-- Fewer fixed scalar words than alphabet symbols are incompatible with
balanced power-sized fibres when the orbit divisor is coprime to the alphabet. -/
theorem balanced_fixed_word_small_impossible [MulAction G W] [Finite W] [Finite ι]
    [Fintype Z] (m a n : ℕ) (hm : 1 < m) (hcop : Nat.Coprime m a)
    (hι : 0 < Nat.card ι) (hZ : Fintype.card Z = a ^ Nat.card ι)
    (hfixed : Nat.card (fixedPoints G W) < a)
    (hdiv : ∀ w : W, w ∉ fixedPoints G W → m ∣ (orbit G w).ncard)
    (f : (ι → W) → Z) (hinv : ∀ (g : G) x, f (g • x) = f x)
    (hbalanced : ∀ z, Nat.card {x : ι → W // f x = z} = a^n) : False := by
  have hr : 0 < a^n % m := by
    apply Nat.pos_of_ne_zero
    intro h
    have hd : m ∣ a^n := Nat.dvd_of_mod_eq_zero h
    have := (hcop.pow_right n).eq_one_of_dvd hd
    omega
  have hb := balanced_fixed_word_residue m (a^n) hdiv f hinv hbalanced
  rw [hZ] at hb
  have hp := Nat.pow_lt_pow_left hfixed (Nat.ne_of_gt hι)
  have hmul : a^Nat.card ι ≤ a^Nat.card ι * (a^n % m) := by
    have h1 : 1 ≤ a^n % m := hr
    simpa only [mul_one] using Nat.mul_le_mul_left (a^Nat.card ι) h1
  omega

/-- A common nontrivial orbit divisor coprime to the fibre alphabet excludes
an invariant power-sized fibre avoiding the distinguished tuple. -/
theorem no_balanced_semiregular [MulAction G W] [Finite W] [Finite ι]
    (w₀ : W) (_hfix : ∀ g : G, g • w₀ = w₀) (m a n : ℕ)
    (hm : 1 < m) (hcop : Nat.Coprime m a)
    (horbit : ∀ w ≠ w₀, m ∣ (orbit G w).ncard)
    (f : (ι → W) → Z) (hinv : ∀ (g : G) x, f (g • x) = f x)
    (z : Z) (hz : z ≠ f (fun _ => w₀))
    (hbalanced : Nat.card {x : ι → W // f x = z} = a ^ n) : False := by
  classical
  let Y := {x : ι → W // f x = z}
  let : MulAction G Y := {
    smul := fun g x => ⟨g • x.val, (hinv g x.val).trans x.property⟩
    one_smul := fun x => Subtype.ext (one_smul G x.val)
    mul_smul := fun g h x => Subtype.ext (mul_smul g h x.val) }
  have hd : m ∣ Nat.card Y := by
    apply dvd_card_of_dvd_orbits (G := G)
    intro x
    have hne : x.val ≠ fun _ => w₀ := by
      intro h
      exact hz (x.property.symm.trans (congrArg f h))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hs : stabilizer G x ≤ stabilizer G (x.val i) := by
      intro g hg
      exact congrFun (congrArg Subtype.val hg) i
    have h := Subgroup.index_dvd_of_le hs
    rw [index_stabilizer, index_stabilizer] at h
    exact (horbit _ hi).trans h
  change m ∣ Nat.card {x : ι → W // f x = z} at hd
  rw [hbalanced] at hd
  have := (hcop.pow_right n).eq_one_of_dvd hd
  omega

/-- In a finite group action free away from the distinguished word, the
orbit-divisor premise is derived from the actual stabilizers. A finite cyclic
action is a special case; cyclicity itself is not needed. -/
theorem no_balanced_free_off_zero [Finite G] [MulAction G W] [Finite W] [Finite ι]
    (w₀ : W) (hfix : ∀ g : G, g • w₀ = w₀) (m a n : ℕ)
    (hcard : Nat.card G = m) (hm : 1 < m) (hcop : Nat.Coprime m a)
    (hfree : ∀ w ≠ w₀, ∀ g : G, g • w = w → g = 1)
    (f : (ι → W) → Z) (hinv : ∀ (g : G) x, f (g • x) = f x)
    (z : Z) (hz : z ≠ f (fun _ => w₀))
    (hbalanced : Nat.card {x : ι → W // f x = z} = a ^ n) : False := by
  apply no_balanced_semiregular w₀ hfix m a n hm hcop ?_ f hinv z hz hbalanced
  intro w hw
  have hs : stabilizer G w = ⊥ := by
    apply le_antisymm
    · intro g hg
      exact Subgroup.mem_bot.mpr (hfree w hw g hg)
    · exact bot_le
  rw [← index_stabilizer, hs, Subgroup.index_bot, hcard]

end SharedDecoders
