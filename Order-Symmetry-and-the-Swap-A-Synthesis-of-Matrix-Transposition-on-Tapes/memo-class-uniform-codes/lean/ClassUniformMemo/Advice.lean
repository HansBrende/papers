import SwapRigidity.ClassUniform
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-!
# Linear advice costs one dimension per symbol

A class-uniform rule *with linear advice* `a` (`IsClassUniformCodeWithAdvice`) lets row `c` of a
code matrix `X` depend, besides the class-uniform term `dec (cls c) (rot c X)`, on the value `a X` of
a fixed linear map `a`, through a linear map `B c` that may depend on the row `c` arbitrarily.  So the
advice may be used differently at every row.

The cost of the advice is at most its rank: the matrices of the code on which the advice vanishes form
a class-uniform code for the same classes (`IsClassUniformCodeWithAdvice.inf_ker`), and they have
codimension at most `rank a` in the code (`finrank_le_finrank_inf_ker_add`).  With the bound for
interval classes this gives `2 * dim 𝒳 ≤ n ^ 2 + n * |S| + 2 * rank a`
(`IsClassUniformCodeWithAdvice.two_mul_finrank_le`).

The cost is exactly the rank, for every class-uniform code: if `p` is a projection that vanishes on a
class-uniform code `𝒳₀`, then `𝒳₀ ⊔ range p` is a class-uniform code with advice `p`
(`isClassUniformCodeWithAdvice_sup_range`) of dimension `dim 𝒳₀ + rank p` (`finrank_sup_range`).

Over a finite field the advice may be of any kind (`IsCodeWithAnyAdvice`): an arbitrary map `w` to a
finite set `Ω`, on each of whose fibers the rows obey an affine class-uniform rule for a colouring that
may depend on the advice.  Counting the fibers gives `|F| ^ dim 𝒳 ≤ |Ω| * |F| ^ D`, where `D` bounds
the codes of the selected colourings (`IsCodeWithAnyAdvice.natCard_pow_finrank_le`), and with the bound
for interval classes, `|F| ^ (2 * dim 𝒳) ≤ |Ω| ^ 2 * |F| ^ (n ^ 2 + n * s)` when every selected
colouring changes class at most `s` times (`IsCodeWithAnyAdvice.natCard_pow_two_mul_finrank_le`): one
dimension per symbol of advice and half a row per class change.

## Main results

* `IsClassUniformCodeWithAdvice.inf_ker`, `finrank_le_finrank_inf_ker_add`: the upper bound.
* `IsClassUniformCodeWithAdvice.two_mul_finrank_le`: the bound for interval classes with advice.
* `isClassUniformCodeWithAdvice_sup_range`, `finrank_sup_range`: the bound is attained.
* `IsCodeWithAnyAdvice.natCard_pow_finrank_le`, `IsCodeWithAnyAdvice.natCard_pow_two_mul_finrank_le`:
  advice of any kind over a finite field.
-/

namespace ClassUniformMemo

open Module SwapRigidity

variable {F : Type*} [Field F] {n : ℕ} {κ : Type*} {W : Type*} [AddCommGroup W] [Module F W]

/-- A subspace `𝒳` of matrices is a *class-uniform code with linear advice* `a` for the colouring
`cls` if there are linear decoders `dec k`, one for each class, and linear maps `B c`, one for each
row, such that row `c` of every `X ∈ 𝒳` is `dec (cls c) (rot c X) + B c (a X)`. -/
def IsClassUniformCodeWithAdvice (cls : ZMod n → κ) (a : Matrix (ZMod n) (ZMod n) F →ₗ[F] W)
    (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) : Prop :=
  ∃ dec : κ → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F)),
    ∃ B : ZMod n → (W →ₗ[F] (ZMod n → F)),
      ∀ X ∈ 𝒳, ∀ c, X c = dec (cls c) (rot c X) + B c (a X)

variable {cls : ZMod n → κ} {a : Matrix (ZMod n) (ZMod n) F →ₗ[F] W}
  {𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)}

/-- Where the advice vanishes, the rule is class-uniform: `𝒳 ⊓ ker a` is a class-uniform code
with the same decoders. -/
theorem IsClassUniformCodeWithAdvice.inf_ker (h : IsClassUniformCodeWithAdvice cls a 𝒳) :
    IsClassUniformCode cls (𝒳 ⊓ LinearMap.ker a) := by
  obtain ⟨dec, B, h⟩ := h
  refine ⟨dec, fun X hX c => ?_⟩
  rw [h X hX.1 c, LinearMap.mem_ker.1 hX.2, map_zero, add_zero]

variable (a 𝒳) in
/-- The matrices of `𝒳` on which `a` vanishes have codimension at most `rank a` in `𝒳`. -/
theorem finrank_le_finrank_inf_ker_add [NeZero n] :
    finrank F 𝒳 ≤ finrank F ↥(𝒳 ⊓ LinearMap.ker a) + finrank F (LinearMap.range a) := by
  let g : 𝒳 →ₗ[F] LinearMap.range a := a.rangeRestrict.domRestrict 𝒳
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have h1 : finrank F (LinearMap.range g) ≤ finrank F (LinearMap.range a) :=
    Submodule.finrank_le _
  have h2 : finrank F (LinearMap.ker g) ≤ finrank F ↥(𝒳 ⊓ LinearMap.ker a) := by
    let ι : LinearMap.ker g →ₗ[F] ↥(𝒳 ⊓ LinearMap.ker a) :=
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          have hx : g x.1 = 0 := LinearMap.mem_ker.1 x.2
          exact SetLike.mem_coe.2 (LinearMap.mem_ker.2 (congrArg Subtype.val hx))⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  omega

/-- **Linear advice costs at most one dimension per symbol.**  For a class-uniform code with linear
advice `a` and a non-empty set `S` of rows containing every row whose class differs from that of the
row before it, `2 * dim 𝒳 ≤ n ^ 2 + n * |S| + 2 * rank a`. -/
theorem IsClassUniformCodeWithAdvice.two_mul_finrank_le [NeZero n]
    (h : IsClassUniformCodeWithAdvice cls a 𝒳) {S : Finset (ZMod n)} (hS : S.Nonempty)
    (hcls : ∀ c ∉ S, cls (c - 1) = cls c) :
    2 * finrank F 𝒳 ≤ n ^ 2 + n * S.card + 2 * finrank F (LinearMap.range a) := by
  have h1 := h.inf_ker.two_mul_finrank_le hS hcls
  have h2 := finrank_le_finrank_inf_ker_add a 𝒳
  omega

/-! ### The bound is attained -/

variable {𝒳₀ : Submodule F (Matrix (ZMod n) (ZMod n) F)}
  {p : Matrix (ZMod n) (ZMod n) F →ₗ[F] Matrix (ZMod n) (ZMod n) F}

/-- **Every class-uniform code extends by any projection, with the projection as advice.**  If `p`
is a projection (`p ∘ p = p`) that vanishes on a class-uniform code `𝒳₀`, then `𝒳₀ ⊔ range p` is a
class-uniform code with advice `p`. -/
theorem isClassUniformCodeWithAdvice_sup_range (h : IsClassUniformCode cls 𝒳₀)
    (hp : p ∘ₗ p = p) (h0 : 𝒳₀ ≤ LinearMap.ker p) :
    IsClassUniformCodeWithAdvice cls p (𝒳₀ ⊔ LinearMap.range p) := by
  obtain ⟨dec, hdec⟩ := h
  let B : ZMod n → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F)) := fun c =>
    { toFun := fun w => w c - dec (cls c) (rot c w)
      map_add' := fun w w' => by
        rw [map_add, map_add]
        funext r
        simp only [Matrix.add_apply, Pi.add_apply, Pi.sub_apply]
        ring
      map_smul' := fun t w => by
        rw [map_smul, map_smul]
        funext r
        simp only [Matrix.smul_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨dec, B, fun X hX c => ?_⟩
  obtain ⟨x₀, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.1 hX
  obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hy
  have hpx : p (x₀ + p z) = p z := by
    rw [map_add, LinearMap.mem_ker.1 (h0 hx₀), zero_add, ← LinearMap.comp_apply, hp]
  rw [hpx]
  change (x₀ + p z) c = dec (cls c) (rot c (x₀ + p z)) + (p z c - dec (cls c) (rot c (p z)))
  rw [map_add, map_add, ← hdec x₀ hx₀ c]
  funext r
  simp only [Matrix.add_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-- The dimension of `𝒳₀ ⊔ range p` is `dim 𝒳₀ + rank p`. -/
theorem finrank_sup_range [NeZero n] (hp : p ∘ₗ p = p) (h0 : 𝒳₀ ≤ LinearMap.ker p) :
    finrank F ↥(𝒳₀ ⊔ LinearMap.range p) = finrank F 𝒳₀ + finrank F (LinearMap.range p) := by
  have hbot : 𝒳₀ ⊓ LinearMap.range p = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₀, hx⟩
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.1 hx
    have h1 : p (p z) = 0 := LinearMap.mem_ker.1 (h0 hx₀)
    rw [← LinearMap.comp_apply, hp] at h1
    rw [Submodule.mem_bot, h1]
  have := Submodule.finrank_sup_add_finrank_inf_eq 𝒳₀ (LinearMap.range p)
  rw [hbot, finrank_bot, add_zero] at this
  exact this

/-! ### Advice of any kind over a finite field -/

section AnyAdvice

variable {Ω : Type*}

/-- A subspace `𝒳` is a *code with advice* `w` for the colourings `cls ω` if on every fiber of the
advice map `w` the rows obey an affine class-uniform rule: there are decoders `dec` and offsets `b`,
depending on the advice value `ω`, such that row `c` of every `X ∈ 𝒳` with `w X = ω` is
`dec (cls ω c) (rot c X) + b c`.  The advice map `w` is arbitrary, and the colouring may depend on
the advice, so the advice may change the decoders of the rows that use it. -/
def IsCodeWithAnyAdvice (cls : Ω → ZMod n → κ) (w : Matrix (ZMod n) (ZMod n) F → Ω)
    (𝒳 : Submodule F (Matrix (ZMod n) (ZMod n) F)) : Prop :=
  ∀ ω, ∃ dec : κ → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F)),
    ∃ b : ZMod n → (ZMod n → F), ∀ X ∈ 𝒳, w X = ω → ∀ c, X c = dec (cls ω c) (rot c X) + b c

/-- The matrices that satisfy a class-uniform rule with the decoders `dec` for the colouring `cls`
form a subspace. -/
def ruleSpace (cls : ZMod n → κ) (dec : κ → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F))) :
    Submodule F (Matrix (ZMod n) (ZMod n) F) where
  carrier := {Y | ∀ c, Y c = dec (cls c) (rot c Y)}
  add_mem' {Y Z} hY hZ c := by
    rw [map_add, map_add, ← hY c, ← hZ c]
    rfl
  zero_mem' c := by
    rw [map_zero, map_zero]
    rfl
  smul_mem' t Y hY c := by
    rw [map_smul, map_smul, ← hY c]
    rfl

theorem mem_ruleSpace {cls : ZMod n → κ}
    {dec : κ → (Matrix (ZMod n) (ZMod n) F →ₗ[F] (ZMod n → F))} {Y : Matrix (ZMod n) (ZMod n) F} :
    Y ∈ ruleSpace cls dec ↔ ∀ c, Y c = dec (cls c) (rot c Y) :=
  Iff.rfl

/-- Over a finite field, a subspace has `|F| ^ dim` elements. -/
theorem natCard_submodule [Finite F] [NeZero n] (𝒴 : Submodule F (Matrix (ZMod n) (ZMod n) F)) :
    Nat.card 𝒴 = Nat.card F ^ finrank F 𝒴 := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite 𝒴
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F) (V := 𝒴)]

/-- **Advice of any kind costs its length, plus what it does to the classes.**  Over a finite field
`F`, if `𝒳` is a code with advice taking values in a finite set `Ω`, and every class-uniform code for
every colouring `cls ω` has dimension at most `D`, then `|F| ^ dim 𝒳 ≤ |Ω| * |F| ^ D`: the advice
costs at most `log_|F| |Ω|` dimensions on top of the largest code of the colourings it selects. -/
theorem IsCodeWithAnyAdvice.natCard_pow_finrank_le [Finite F] [NeZero n] [Fintype Ω]
    {cls : Ω → ZMod n → κ} {w : Matrix (ZMod n) (ZMod n) F → Ω}
    (h : IsCodeWithAnyAdvice cls w 𝒳) {D : ℕ}
    (hD : ∀ ω (𝒴 : Submodule F (Matrix (ZMod n) (ZMod n) F)),
      IsClassUniformCode (cls ω) 𝒴 → finrank F 𝒴 ≤ D) :
    Nat.card F ^ finrank F 𝒳 ≤ Fintype.card Ω * Nat.card F ^ D := by
  classical
  choose dec b hrule using h
  -- the homogeneous code of the fiber `ω`
  let K : Ω → Submodule F (Matrix (ZMod n) (ZMod n) F) := fun ω => 𝒳 ⊓ ruleSpace (cls ω) (dec ω)
  have hK : ∀ ω, finrank F (K ω) ≤ D := fun ω =>
    hD ω (K ω) ⟨dec ω, fun Y hY c => mem_ruleSpace.1 hY.2 c⟩
  -- a base point of every non-empty fiber
  let base : Ω → Matrix (ZMod n) (ZMod n) F := fun ω =>
    if hω : ∃ X ∈ 𝒳, w X = ω then hω.choose else 0
  have hbase : ∀ X ∈ 𝒳, base (w X) ∈ 𝒳 ∧ w (base (w X)) = w X := by
    intro X hX
    show (if hω : ∃ Y ∈ 𝒳, w Y = w X then hω.choose else 0) ∈ 𝒳 ∧
      w (if hω : ∃ Y ∈ 𝒳, w Y = w X then hω.choose else 0) = w X
    split
    · next hω => exact hω.choose_spec
    · next hω => exact absurd ⟨X, hX, rfl⟩ hω
  -- every fiber injects into the homogeneous code of its value
  have hfiber : ∀ ω, Nat.card {X : 𝒳 // w X = ω} ≤ Nat.card (K ω) := by
    intro ω
    refine Nat.card_le_card_of_injective
      (fun X : {X : 𝒳 // w X = ω} => (⟨X.1.1 - base ω, ?_⟩ : K ω)) ?_
    · obtain ⟨⟨X, hX⟩, hXω⟩ := X
      obtain ⟨hb, hbω⟩ := hbase X hX
      simp only at hXω
      subst hXω
      show X - base (w X) ∈ K (w X)
      refine ⟨𝒳.sub_mem hX hb, mem_ruleSpace.2 fun c => ?_⟩
      rw [map_sub, map_sub]
      funext r
      have h1 := congrFun (hrule (w X) X hX rfl c) r
      have h2 := congrFun (hrule (w X) (base (w X)) hb hbω c) r
      simp only [Pi.add_apply] at h1 h2
      simp only [Matrix.sub_apply, Pi.sub_apply]
      rw [h1, h2]
      ring
    · intro X Y hXY
      have := congrArg Subtype.val hXY
      simp only [sub_left_inj] at this
      exact Subtype.ext (Subtype.ext this)
  have hcard : Nat.card 𝒳 = ∑ ω, Nat.card {X : 𝒳 // w X = ω} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv (fun X : 𝒳 => w X.1)).symm
  have hpos : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 (Nat.card_pos.ne')
  rw [← natCard_submodule, hcard]
  calc ∑ ω, Nat.card {X : 𝒳 // w X = ω} ≤ ∑ _ω : Ω, Nat.card F ^ D := by
        refine Finset.sum_le_sum fun ω _ => (hfiber ω).trans ?_
        rw [natCard_submodule]
        exact Nat.pow_le_pow_right hpos (hK ω)
    _ = Fintype.card Ω * Nat.card F ^ D := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Theorem TP with advice.**  Over a finite field `F`, let `𝒳` be a code with advice taking
values in a finite set `Ω`, and suppose that every colouring `cls ω` selected by the advice changes
class at most `s` times: some non-empty set of at most `s` rows contains every row whose class differs
from that of the row before it.  Then `|F| ^ (2 * dim 𝒳) ≤ |Ω| ^ 2 * |F| ^ (n ^ 2 + n * s)`.  With `q`
advice symbols from `F` this reads `2 * dim 𝒳 ≤ n ^ 2 + n * s + 2 * q`: one dimension per symbol of
advice, and half a row per class change, wherever the changes come from. -/
theorem IsCodeWithAnyAdvice.natCard_pow_two_mul_finrank_le [Finite F] [NeZero n] [Fintype Ω]
    {cls : Ω → ZMod n → κ} {w : Matrix (ZMod n) (ZMod n) F → Ω}
    (h : IsCodeWithAnyAdvice cls w 𝒳) {s : ℕ}
    (hS : ∀ ω, ∃ S : Finset (ZMod n), S.Nonempty ∧ S.card ≤ s ∧
      ∀ c ∉ S, cls ω (c - 1) = cls ω c) :
    Nat.card F ^ (2 * finrank F 𝒳) ≤ Fintype.card Ω ^ 2 * Nat.card F ^ (n ^ 2 + n * s) := by
  have hD : ∀ ω (𝒴 : Submodule F (Matrix (ZMod n) (ZMod n) F)),
      IsClassUniformCode (cls ω) 𝒴 → finrank F 𝒴 ≤ (n ^ 2 + n * s) / 2 := by
    intro ω 𝒴 h𝒴
    obtain ⟨S, hSne, hScard, hcls⟩ := hS ω
    have := h𝒴.two_mul_finrank_le hSne hcls
    have : n * S.card ≤ n * s := Nat.mul_le_mul_left n hScard
    omega
  have hmain := h.natCard_pow_finrank_le hD
  have hpos : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.2 (Nat.card_pos.ne')
  calc Nat.card F ^ (2 * finrank F 𝒳) = (Nat.card F ^ finrank F 𝒳) ^ 2 := by
        rw [← pow_mul, mul_comm]
    _ ≤ (Fintype.card Ω * Nat.card F ^ ((n ^ 2 + n * s) / 2)) ^ 2 :=
        Nat.pow_le_pow_left hmain 2
    _ = Fintype.card Ω ^ 2 * Nat.card F ^ (2 * ((n ^ 2 + n * s) / 2)) := by
        rw [mul_pow, ← pow_mul, mul_comm ((n ^ 2 + n * s) / 2) 2]
    _ ≤ Fintype.card Ω ^ 2 * Nat.card F ^ (n ^ 2 + n * s) := by
        refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos ?_)
        omega

end AnyAdvice

end ClassUniformMemo
