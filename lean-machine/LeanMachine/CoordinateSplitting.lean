import LeanMachine.SubspaceDefect

/-! Exact capacity accounting for an idempotent which acts coordinatewise
on a code. Merely splitting the code dimension would not suffice. -/

namespace LeanMachine.CoordinateSplitting

open Module Finset
open scoped BigOperators

variable {K H A : Type*} [Field K] [AddCommGroup H] [Module K H]
  [FiniteDimensional K H] [AddCommGroup A] [Module K A] [FiniteDimensional K A]

theorem range_split (p : H →ₗ[K] H) (hp : p.comp p = p) (r : H →ₗ[K] A) :
    LinearMap.range r = LinearMap.range (r.comp p) ⊔ (LinearMap.ker p).map r := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hz : x - p x ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub]
      have hh := LinearMap.congr_fun hp x
      change p (p x) = p x at hh
      rw [hh, sub_self]
    have h1 : r (p x) ∈ LinearMap.range (r.comp p) := ⟨x, rfl⟩
    have h2 : r (x - p x) ∈ (LinearMap.ker p).map r := ⟨x - p x, hz, rfl⟩
    have hh := Submodule.add_mem_sup h1 h2
    simpa only [map_sub, add_sub_cancel] using hh
  · apply sup_le
    · exact LinearMap.range_comp_le_range p r
    · rintro _ ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩

theorem range_split_disjoint (p : H →ₗ[K] H) (hp : p.comp p = p)
    (r : H →ₗ[K] A) (D : A →ₗ[K] A) (hD : D.comp r = r.comp p) :
    Disjoint (LinearMap.range (r.comp p)) ((LinearMap.ker p).map r) := by
  have hD' (x : H) : D (r x) = r (p x) := LinearMap.congr_fun hD x
  have hp' (x : H) : p (p x) = p x := LinearMap.congr_fun hp x
  apply disjoint_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  rintro y ⟨⟨x, hx⟩, z, hz, hzy⟩
  have h1 : D y = y := by
    rw [← hx]
    change D (r (p x)) = r (p x)
    rw [hD', hp']
  have h0 : D y = 0 := by
    rw [← hzy, hD']
    rw [LinearMap.mem_ker.mp hz, map_zero]
  exact h1.symm.trans h0

theorem coordinate_rank_split (p : H →ₗ[K] H) (hp : p.comp p = p)
    (r : H →ₗ[K] A) (D : A →ₗ[K] A) (hD : D.comp r = r.comp p) :
    finrank K (LinearMap.range r) = finrank K (LinearMap.range (r.comp p)) +
      finrank K (LinearMap.range (r.domRestrict (LinearMap.ker p))) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (r.comp p)) ((LinearMap.ker p).map r)
  rw [← range_split p hp r, (range_split_disjoint p hp r D hD).eq_bot,
    finrank_bot, add_zero] at h
  rw [LinearMap.range_domRestrict]
  exact h

theorem rank_factor_eq (p : H →ₗ[K] H) (r : H →ₗ[K] A)
    (hinj : Function.Injective (r.domRestrict (LinearMap.range p))) :
    finrank K (LinearMap.range (r.comp p)) = finrank K (LinearMap.range p) := by
  rw [LinearMap.range_comp, ← LinearMap.range_domRestrict]
  exact LinearMap.finrank_range_of_inj hinj

end LeanMachine.CoordinateSplitting
