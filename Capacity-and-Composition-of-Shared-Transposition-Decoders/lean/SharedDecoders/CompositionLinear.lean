import SharedDecoders.Model
import SharedDecoders.CompositionProgression
import SharedDecoders.CompositionRamsey
import SharedDecoders.CapacityRunsOrbits
import Mathlib.Algebra.Ring.Periodic

/-!
# The actual linear two-stage interface

The second operator's fixed-input image forces a row-class-constant ambient.
Its dimension and the dimension of a rotation's fixed space are proved by
explicit coordinate restrictions.  These are properties of the actual maps,
not certificates supplied as extra hypotheses.
-/

namespace SharedDecoders

open Module

variable {F A κ κ₁ κ₂ : Type*} [Field F] [AddCommGroup A] [Module F A]
  {d : ℕ} [NeZero d]

/-- A complete shared-decoder map with linear class decoders. -/
def LinearClassUniform (p : ZMod d → κ) (K : State d A →ₗ[F] State d A) : Prop :=
  ∃ f : κ → State d A →ₗ[F] (ZMod d → A),
    ∀ X c i, K X i c = f (p c) (rot c X) i

/-- The linear ambient forced by the second stage on column-constant inputs. -/
def rowClassSpace (p : ZMod d → κ) : Submodule F (State d A) where
  carrier := {X | ∀ i j, p i = p j → X i = X j}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro X Y hX hY i j hij
    simp only [Pi.add_apply, hX i j hij, hY i j hij]
  smul_mem' := by
    intro a X hX i j hij
    simp only [Pi.smul_apply, hX i j hij]

noncomputable def classRepresentative (p : ZMod d → κ) (c : κ) : ZMod d := by
  classical
  exact if h : ∃ i, p i = c then h.choose else 0

theorem classRepresentative_spec (p : ZMod d → κ) (i : ZMod d) :
    p (classRepresentative p (p i)) = p i := by
  classical
  simp only [classRepresentative]
  split
  · rename_i h
    exact h.choose_spec
  · rename_i h
    exact False.elim (h ⟨i, rfl⟩)

/-- A linear complete map that has arbitrary total shared decoders also has
linear shared decoders. This uses the full domain, not a correctness subspace. -/
theorem linearClassUniform_of_classUniform (p : ZMod d → κ)
    (K : State d A →ₗ[F] State d A) (hK : ClassUniform p K) :
    LinearClassUniform p K := by
  classical
  obtain ⟨f, hf⟩ := hK
  let col (c : ZMod d) : State d A →ₗ[F] (ZMod d → A) := {
    toFun := fun X i => X i c
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  refine ⟨fun J => (col (classRepresentative p J)).comp
    (K.comp (rotLinear F (-classRepresentative p J))), ?_⟩
  intro X c i
  change K X i c = K (rot (-classRepresentative p (p c)) (rot c X)) i
    (classRepresentative p (p c))
  rw [hf, hf, classRepresentative_spec p c, rot_rot, rot_rot]
  congr 2
  simp

omit [NeZero d] in
theorem LinearClassUniform.classUniform {p : ZMod d → κ}
    {K : State d A →ₗ[F] State d A} (hK : LinearClassUniform p K) :
    ClassUniform p K := by
  obtain ⟨f, hf⟩ := hK
  exact ⟨fun J => f J, hf⟩

noncomputable def classRestriction (p : ZMod d → κ) :
    rowClassSpace (F := F) (A := A) p →ₗ[F] (κ → ZMod d → A) where
  toFun X c := X.1 (classRepresentative p c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem classRestriction_injective (p : ZMod d → κ) :
    Function.Injective (classRestriction (F := F) (A := A) p) := by
  intro X Y h
  apply Subtype.ext
  funext i j
  have hX := congrFun (X.2 i (classRepresentative p (p i))
    (classRepresentative_spec p i).symm) j
  have hY := congrFun (Y.2 i (classRepresentative p (p i))
    (classRepresentative_spec p i).symm) j
  exact hX.trans ((congrFun (congrFun h (p i)) j).trans hY.symm)

theorem rowClassSpace_finrank_le [Fintype κ] [FiniteDimensional F A]
    (p : ZMod d → κ) :
    finrank F (rowClassSpace (F := F) (A := A) p) ≤
      Fintype.card κ * d * finrank F A := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (classRestriction_injective (F := F) (A := A) p)
  simpa [Module.finrank_pi_fintype, ZMod.card, mul_assoc] using h

/-- Rotation restricted to the actual row-class ambient. -/
def rowClassRotation (p : ZMod d → κ) (s : ZMod d) :
    rowClassSpace (F := F) (A := A) p →ₗ[F] rowClassSpace (F := F) (A := A) p where
  toFun X := ⟨rot s X.1, by
    intro i j hij
    funext c
    exact congrFun (X.2 i j hij) (c + s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero d] in
@[simp] theorem rowClassRotation_apply (p : ZMod d → κ) (s : ZMod d)
    (X : rowClassSpace (F := F) (A := A) p) :
    (rowClassRotation p s X).1 = rot s X.1 := rfl

omit [NeZero d] in
theorem rowClassRotation_pow (p : ZMod d → κ) (s : ZMod d)
    (j : ℕ) (X : rowClassSpace (F := F) (A := A) p) :
    ((rowClassRotation p s ^ j) X).1 = rot ((j : ZMod d) * s) X.1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      simp only [pow_succ', Module.End.mul_apply, rowClassRotation_apply, ih, rot_rot]
      congr 1
      push_cast
      ring

/-- A word fixed by a positive `s`-step rotation is determined by its first `s`
coordinates.  This bound avoids a semisimplicity assumption in every characteristic. -/
theorem fixed_word_zero_of_prefix {s : ℕ} (hs : 0 < s) (x : ZMod d → A)
    (hfix : ∀ j, x (j + (s : ZMod d)) = x j)
    (hzero : ∀ j < s, x (j : ZMod d) = 0) : x = 0 := by
  have hn : ∀ n : ℕ, x (n : ZMod d) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hns : n < s
      · exact hzero n hns
      · have hle : s ≤ n := by omega
        have hsub : n - s < n := by omega
        have he := hfix ((n - s : ℕ) : ZMod d)
        rw [← Nat.cast_add, Nat.sub_add_cancel hle] at he
        exact he.trans (ih (n - s) hsub)
  funext j
  simpa using hn j.val

noncomputable def fixedClassRestriction (p : ZMod d → κ) (s : ℕ) :
    LinearMap.ker (rowClassRotation (F := F) (A := A) p (s : ZMod d) - LinearMap.id) →ₗ[F]
      (κ → Fin s → A) where
  toFun X c j := X.1.1 (classRepresentative p c) (j.val : ZMod d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fixedClassRestriction_injective (p : ZMod d → κ) {s : ℕ} (hs : 0 < s) :
    Function.Injective (fixedClassRestriction (F := F) (A := A) p s) := by
  rw [injective_iff_map_eq_zero]
  intro X hX
  have hfix : rot (s : ZMod d) X.1.1 = X.1.1 := by
    have h := X.2
    change rowClassRotation p (s : ZMod d) X.1 - X.1 = 0 at h
    exact congrArg Subtype.val (sub_eq_zero.mp h)
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply fixed_word_zero_of_prefix hs
  · intro j
    exact congrFun (congrFun hfix i) j
  · intro j hj
    have he := X.1.2 i (classRepresentative p (p i)) (classRepresentative_spec p i).symm
    rw [he]
    exact congrFun (congrFun hX (p i)) ⟨j, hj⟩

theorem rowClassRotation_fixed_finrank_le [Fintype κ] [FiniteDimensional F A]
    (p : ZMod d → κ) {s : ℕ} (hs : 0 < s) :
    finrank F (LinearMap.ker
      (rowClassRotation (F := F) (A := A) p (s : ZMod d) - LinearMap.id)) ≤
        Fintype.card κ * s * finrank F A := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (fixedClassRestriction_injective (F := F) (A := A) p hs)
  simpa [Module.finrank_pi_fintype, mul_assoc] using h

/-- A fixed matrix is specified by one value for each row class and actual
translation orbit. Unused row-class labels do not affect injectivity. -/
noncomputable def fixedClassOrbitRestriction (p : ZMod d → κ) (s : ZMod d) :
    LinearMap.ker (rowClassRotation (F := F) (A := A) p s - LinearMap.id) →ₗ[F]
      (κ → CapacityRuns.TranslationOrbit s → A) where
  toFun X c := (show Function.Periodic (X.1.1 (classRepresentative p c)) s from by
    intro j
    have h := congrArg Subtype.val (sub_eq_zero.mp X.2)
    exact congrFun (congrFun h (classRepresentative p c)) j).lift
  map_add' X Y := by
    funext c o
    induction o using Quotient.inductionOn'
    rfl
  map_smul' a X := by
    funext c o
    induction o using Quotient.inductionOn'
    rfl

theorem fixedClassOrbitRestriction_injective (p : ZMod d → κ) (s : ZMod d) :
    Function.Injective (fixedClassOrbitRestriction (F := F) (A := A) p s) := by
  intro X Y h
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  have hX := congrFun (X.1.2 i (classRepresentative p (p i))
    (classRepresentative_spec p i).symm) j
  have hY := congrFun (Y.1.2 i (classRepresentative p (p i))
    (classRepresentative_spec p i).symm) j
  exact hX.trans ((congrFun (congrFun h (p i))
    (j : CapacityRuns.TranslationOrbit s)).trans hY.symm)

/-- The exact translation-orbit count sharpens the fixed-space correction to
`gcd(d,s)`, in every characteristic and for every natural step, including zero. -/
theorem rowClassRotation_fixed_finrank_le_gcd [Fintype κ] [FiniteDimensional F A]
    (p : ZMod d → κ) (s : ℕ) :
    finrank F (LinearMap.ker
      (rowClassRotation (F := F) (A := A) p (s : ZMod d) - LinearMap.id)) ≤
        Fintype.card κ * Nat.gcd d s * finrank F A := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (fixedClassOrbitRestriction_injective (F := F) (A := A) p (s : ZMod d))
  have hg : Nat.gcd d (s % d) = Nat.gcd d s := by
    rw [Nat.gcd_comm d (s % d), ← Nat.gcd_rec]
  simpa [Module.finrank_pi_fintype, CapacityRuns.translationOrbit_card,
    ZMod.val_natCast, hg, mul_assoc] using h

/-- Repeated columns carry one whole row/lane message. -/
def repeatColumns : (ZMod d → A) →ₗ[F] State d A where
  toFun a i _ := a i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero d] in
@[simp] theorem repeatColumns_apply (a : ZMod d → A) (i j : ZMod d) :
    repeatColumns (F := F) a i j = a i := rfl

omit [NeZero d] in
@[simp] theorem rot_repeatColumns (a : ZMod d → A) (s : ZMod d) :
    rot s (repeatColumns (F := F) a) = repeatColumns (F := F) a := rfl

theorem first_swap_second [FiniteDimensional F A]
    (K₁ K₂ : State d A →ₗ[F] State d A)
    (hexact : ∀ X, K₂ (K₁ X) = swap X) (X : State d A) :
    K₁ (swap (K₂ X)) = X := by
  have hinj : Function.Injective K₁ := by
    rw [injective_iff_map_eq_zero]
    intro Y hY
    have hz : swap Y = 0 := by rw [← hexact Y, hY, map_zero]
    funext i j
    exact congrFun (congrFun hz j) i
  obtain ⟨Y, rfl⟩ := LinearMap.surjective_of_injective hinj X
  rw [hexact Y, swap_swap]

/-- An ordinary progression in the first mask imposes a finite dimension bound
on the actual two-stage product, uniformly over the lane space and the field. -/
theorem twoHop_progression_gcd [Fintype κ₂] [FiniteDimensional F A] [Nontrivial A]
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d A →ₗ[F] State d A)
    (h₁ : LinearClassUniform p₁ K₁) (h₂ : LinearClassUniform p₂ K₂)
    (hexact : ∀ X, K₂ (K₁ X) = swap X)
    (c₀ : ZMod d) {s ell : ℕ} (hell : 0 < ell)
    (hmono : ∀ j < ell, p₁ (c₀ + (j : ZMod d) * (s : ZMod d)) = p₁ c₀) :
    ell * d ≤ Fintype.card κ₂ * d +
      (ell - 1) * Fintype.card κ₂ * Nat.gcd d s := by
  classical
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  let E₀ : (ZMod d → A) →ₗ[F] State d A :=
    (swapLinear F).comp (K₂.comp repeatColumns)
  have hE₀ : ∀ a, E₀ a ∈ rowClassSpace (F := F) (A := A) p₂ := by
    intro a i j hij
    funext c
    change K₂ (repeatColumns (F := F) a) c i = K₂ (repeatColumns (F := F) a) c j
    rw [hf₂, hf₂, hij, rot_repeatColumns, rot_repeatColumns]
  let E := E₀.codRestrict (rowClassSpace (F := F) (A := A) p₂) hE₀
  have hleft (a : ZMod d → A) : K₁ (E a).1 = repeatColumns (F := F) a :=
    first_swap_second K₁ K₂ hexact _
  have hEinj : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h : repeatColumns (F := F) a = 0 := by
      rw [← hleft a, ha]
      exact map_zero K₁
    funext i
    exact congrFun (congrFun h i) 0
  let W := LinearMap.range E
  let R := rowClassRotation (F := F) (A := A) p₂ (s : ZMod d)
  let L : rowClassSpace (F := F) (A := A) p₂ →ₗ[F] (ZMod d → A) :=
    (f₁ (p₁ c₀)).comp ((rotLinear F c₀).comp (rowClassSpace p₂).subtype)
  have hobs (j : ℕ) (hj : j < ell) (a : ZMod d → A) : L ((R ^ j) (E a)) = a := by
    ext i
    change f₁ (p₁ c₀) (rot c₀ (((R ^ j) (E a)).1)) i = a i
    rw [rowClassRotation_pow, rot_rot]
    have h := hf₁ (E a).1 (c₀ + (j : ZMod d) * (s : ZMod d)) i
    rw [hmono j hj] at h
    rw [← h, hleft]
    rfl
  have hdimW : finrank F W = d * finrank F A := by
    rw [LinearMap.finrank_range_of_inj hEinj]
    simp [Module.finrank_pi_fintype, ZMod.card]
  have hker : ∀ x ∈ W, L x = 0 → x = 0 := by
    rintro x ⟨a, rfl⟩ hx
    have ha : a = 0 := by simpa using (hobs 0 hell a).symm.trans hx
    simp [ha]
  have hmessage : ∀ j < ell, ∀ x ∈ W, L ((R ^ j) x) = L x := by
    intro j hj x hx
    obtain ⟨a, rfl⟩ := hx
    exact (hobs j hj a).trans (by simpa using (hobs 0 hell a).symm)
  have hg := commonMessage_finrank_le R W L ell hell hker hmessage
  rw [hdimW] at hg
  have ha := rowClassSpace_finrank_le (F := F) (A := A) p₂
  have hf := rowClassRotation_fixed_finrank_le_gcd (F := F) (A := A) p₂ s
  have hsum := Nat.add_le_add ha (Nat.mul_le_mul_left (ell - 1) hf)
  have hscaled : (ell * d) * finrank F A ≤
      (Fintype.card κ₂ * d + (ell - 1) * Fintype.card κ₂ * Nat.gcd d s) * finrank F A := by
    simpa [R, mul_assoc, add_mul] using hg.trans hsum
  exact le_of_mul_le_mul_right hscaled (finrank_pos (R := F) (M := A))

/-- The earlier positive-step bound follows from the sharper orbit correction.
Its interface is retained for the finite Ramsey cutoff. -/
theorem twoHop_progression [Fintype κ₂] [FiniteDimensional F A] [Nontrivial A]
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d A →ₗ[F] State d A)
    (h₁ : LinearClassUniform p₁ K₁) (h₂ : LinearClassUniform p₂ K₂)
    (hexact : ∀ X, K₂ (K₁ X) = swap X)
    (c₀ : ZMod d) {s ell : ℕ} (hs : 0 < s) (hell : 0 < ell)
    (hmono : ∀ j < ell, p₁ (c₀ + (j : ZMod d) * (s : ZMod d)) = p₁ c₀) :
    ell * d ≤ Fintype.card κ₂ * d + (ell - 1) * Fintype.card κ₂ * s :=
  (twoHop_progression_gcd p₁ p₂ K₁ K₂ h₁ h₂ hexact c₀ hell hmono).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.gcd_le_right d hs)) _)

/-- A coprime-step progression one longer than the second class count forces
a quadratic class-count cutoff, independent of the progression step. -/
theorem twoHop_coprime_progression_dimension_le
    [Fintype κ₂] [FiniteDimensional F A] [Nontrivial A]
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d A →ₗ[F] State d A)
    (h₁ : LinearClassUniform p₁ K₁) (h₂ : LinearClassUniform p₂ K₂)
    (hexact : ∀ X, K₂ (K₁ X) = swap X)
    (c₀ : ZMod d) {s : ℕ} (hcop : Nat.Coprime d s)
    (hmono : ∀ j < Fintype.card κ₂ + 1,
      p₁ (c₀ + (j : ZMod d) * (s : ZMod d)) = p₁ c₀) :
    d ≤ Fintype.card κ₂ ^ 2 := by
  have h := twoHop_progression_gcd p₁ p₂ K₁ K₂ h₁ h₂ hexact
    c₀ (Nat.succ_pos _) hmono
  simp only [hcop.gcd_eq_one, mul_one, Nat.succ_sub_one, Nat.succ_mul] at h
  nlinarith

/-- A finite interval containing the relevant monochromatic progressions gives
an actual two-stage cutoff.  No inverse or source-space certificate is assumed. -/
theorem twoHop_dimension_le [Fintype κ₂] [FiniteDimensional F A] [Nontrivial A]
    (N : ℕ)
    (hRamsey : ∀ C : ℕ → κ₁, ∃ a s : ℕ, 0 < s ∧
      ∀ j < Fintype.card κ₂ + 1,
        a + s * j < N ∧ C (a + s * j) = C a)
    (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
    (K₁ K₂ : State d A →ₗ[F] State d A)
    (h₁ : LinearClassUniform p₁ K₁) (h₂ : LinearClassUniform p₂ K₂)
    (hexact : ∀ X, K₂ (K₁ X) = swap X) :
    d ≤ Fintype.card κ₂ * (N - 1) := by
  obtain ⟨a, s, hs, hprog⟩ := hRamsey (fun n => p₁ (n : ZMod d))
  have hmono : ∀ j < Fintype.card κ₂ + 1,
      p₁ ((a : ZMod d) + (j : ZMod d) * (s : ZMod d)) = p₁ (a : ZMod d) := by
    intro j hj
    simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using (hprog j hj).2
  have hdim := twoHop_progression p₁ p₂ K₁ K₂ h₁ h₂ hexact
    (a : ZMod d) hs (Nat.succ_pos _) hmono
  have hlast := (hprog (Fintype.card κ₂) (Nat.lt_succ_self _)).1
  have hstep : Fintype.card κ₂ * s ≤ N - 1 := by
    have h : s * Fintype.card κ₂ ≤ N - 1 := by omega
    simpa [mul_comm] using h
  have hd : d ≤ Fintype.card κ₂ * (Fintype.card κ₂ * s) := by
    simp only [Nat.succ_sub_one] at hdim
    nlinarith
  exact hd.trans (Nat.mul_le_mul_left _ hstep)

/-- Fixed finite class sets cannot give exact linear two-stage transposition in
all large dimensions.  The cutoff is uniform in the field and lane dimension. -/
theorem exists_twoHop_cutoff (κ₁ κ₂ : Type*) [Finite κ₁] [Fintype κ₂] :
    ∃ D₀ : ℕ, ∀ (F A : Type*) [Field F] [AddCommGroup A] [Module F A]
      [FiniteDimensional F A] [Nontrivial A] (d : ℕ) [NeZero d],
      ∀ (p₁ : ZMod d → κ₁) (p₂ : ZMod d → κ₂)
        (K₁ K₂ : State d A →ₗ[F] State d A),
      LinearClassUniform p₁ K₁ → LinearClassUniform p₂ K₂ →
      (∀ X, K₂ (K₁ X) = swap X) → d ≤ D₀ := by
  obtain ⟨N, _, hN⟩ := exists_progression_bound κ₁
    (Fintype.card κ₂ + 1) (Nat.succ_pos _)
  refine ⟨Fintype.card κ₂ * (N - 1), ?_⟩
  intro F A _ _ _ _ _ d _ p₁ p₂ K₁ K₂ h₁ h₂ hexact
  exact twoHop_dimension_le N hN p₁ p₂ K₁ K₂ h₁ h₂ hexact

/-- The kernel-checked `W(2,3) ≤ 9` certificate gives a numerical exclusion
for two binary class labels in each stage. Unused labels are allowed. -/
theorem twoHop_two_classes_le_sixteen [FiniteDimensional F A] [Nontrivial A]
    (p₁ p₂ : ZMod d → Fin 2) (K₁ K₂ : State d A →ₗ[F] State d A)
    (h₁ : LinearClassUniform p₁ K₁) (h₂ : LinearClassUniform p₂ K₂)
    (hexact : ∀ X, K₂ (K₁ X) = swap X) : d ≤ 16 := by
  have h := twoHop_dimension_le 9 (by simpa using binary_progression_nine)
    p₁ p₂ K₁ K₂ h₁ h₂ hexact
  simpa using h

end SharedDecoders
