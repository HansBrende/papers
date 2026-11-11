import SharedDecoders.CapacityIteration

/-! # No-loss completion by the class-covariant space

The source is linear, but its decoders need not be. Completion replaces the
source and is not asserted to contain it. The residual is its actual intersection
with the projection kernel, not the image under the complementary projection.
-/

namespace SharedDecoders

open Module LinearMap

variable {F A κ : Type*} [Field F] [AddCommGroup A] [Module F A] {d : ℕ}

def classProjection (p : ZMod d → κ) (r : κ → ZMod d) :
    State d A →ₗ[F] State d A where
  toFun X c j := X (r (p c)) (j + c - r (p c))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem classProjection_apply (p : ZMod d → κ) (r : κ → ZMod d)
    (X : State d A) (c j : ZMod d) :
    classProjection (F := F) p r X c j = X (r (p c)) (j + c - r (p c)) := rfl

theorem classProjection_idempotent {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (X : State d A) :
    classProjection (F := F) p r (classProjection (F := F) p r X) = classProjection (F := F) p r X := by
  funext c j
  simp [hr]

theorem classProjection_rot (p : ZMod d → κ) (r : κ → ZMod d)
    (X : State d A) (s : ZMod d) :
    classProjection (F := F) p r (rot s X) = rot s (classProjection (F := F) p r X) := by
  funext c j
  simp only [classProjection_apply, rot_apply]
  congr 1
  abel

theorem classProjection_mem_range_iff {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) {X : State d A} :
    X ∈ LinearMap.range (classProjection (F := F) p r) ↔ classProjection (F := F) p r X = X := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact classProjection_idempotent hr Y
  · intro h
    exact ⟨X, h⟩

theorem mem_classProjection_ker {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) {X : State d A} :
    X ∈ LinearMap.ker (classProjection (F := F) p r) ↔ ∀ a, X (r a) = 0 := by
  constructor
  · intro h a
    funext j
    have hh := congrFun (congrFun (LinearMap.mem_ker.mp h) (r a)) j
    simpa [hr] using hh
  · intro h
    apply LinearMap.mem_ker.mpr
    funext c j
    exact congrFun (h (p c)) (j + c - r (p c))

noncomputable def classProjectionRangeEquiv {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    LinearMap.range (classProjection (F := F) (A := A) p r) ≃ₗ[F]
      (κ → ZMod d → A) where
  toFun X a := (X : State d A) (r a)
  invFun Y := ⟨fun c j => Y (p c) (j + c - r (p c)), by
    apply (classProjection_mem_range_iff hr).2
    funext c j
    simp [hr]⟩
  left_inv X := by
    apply Subtype.ext
    exact (classProjection_mem_range_iff hr).1 X.2
  right_inv Y := by
    funext a j
    simp [hr]
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def completedCode (p : ZMod d → κ) (r : κ → ZMod d)
    (C : Submodule F (State d A)) : Submodule F (State d A) :=
  (C ⊓ LinearMap.ker (classProjection (F := F) p r)) ⊔ LinearMap.range (classProjection (F := F) p r)

def completedDecoder (p : ZMod d → κ) (r : κ → ZMod d)
    (f : κ → State d A → (ZMod d → A)) (a : κ) (Y : State d A) (j : ZMod d) : A :=
  f a (Y - classProjection (F := F) p r Y) j + Y (r a) (j - r a)

theorem completedDecoder_correct {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) {C : Submodule F (State d A)}
    (f : κ → State d A → (ZMod d → A))
    (hf : ∀ X ∈ C, ∀ c, X c = f (p c) (rot c X)) :
    ∀ X ∈ completedCode p r C, ∀ c,
      X c = completedDecoder (F := F) p r f (p c) (rot c X) := by
  intro X hX c
  obtain ⟨X₀, h₀, H, hH, rfl⟩ := Submodule.mem_sup.mp hX
  have hp₀ : classProjection (F := F) p r X₀ = 0 := LinearMap.mem_ker.mp h₀.2
  have hpH : classProjection (F := F) p r H = H := (classProjection_mem_range_iff hr).1 hH
  have hrep : X₀ (r (p c)) = 0 := (mem_classProjection_ker hr).1 h₀.2 (p c)
  have hstrip : rot c (X₀ + H) - classProjection (F := F) p r (rot c (X₀ + H)) = rot c X₀ := by
    rw [classProjection_rot, map_add, hp₀, hpH, zero_add]
    funext i j
    simp [rot]
  have hdecode := hf X₀ h₀.1 c
  funext j
  dsimp only [completedDecoder]
  rw [hstrip, ← hdecode]
  have hc := congrFun (congrFun hpH c) j
  simp only [classProjection_apply] at hc
  simp only [Pi.add_apply, rot_apply, hrep, Pi.zero_apply, zero_add]
  rw [← hc]
  congr 2
  abel

theorem IsSharedCode.completedCode {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) {C : Submodule F (State d A)}
    (h : IsSharedCode F p C) : IsSharedCode F p (completedCode p r C) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨completedDecoder (F := F) p r f, completedDecoder_correct hr f hf⟩

theorem classProjection_ker_disjoint_range {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    Disjoint (LinearMap.ker (classProjection (F := F) (A := A) p r))
      (LinearMap.range (classProjection (F := F) p r)) := by
  rw [Submodule.disjoint_def]
  intro X hker hran
  exact ((classProjection_mem_range_iff hr).1 hran).symm.trans (LinearMap.mem_ker.mp hker)

theorem completedCode_eq_of_range_le {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) {C : Submodule F (State d A)}
    (hC : LinearMap.range (classProjection p r) ≤ C) : completedCode p r C = C := by
  apply le_antisymm (sup_le inf_le_left hC)
  intro X hX
  apply Submodule.mem_sup.mpr
  let P := classProjection (F := F) (A := A) p r
  refine ⟨X - P X, ⟨C.sub_mem hX (hC ⟨X, rfl⟩), ?_⟩, P X, ⟨X, rfl⟩, ?_⟩
  · apply LinearMap.mem_ker.mpr
    simp only [map_sub, P, classProjection_idempotent hr, sub_self]
  · exact sub_add_cancel X (P X)

variable [NeZero d] [Fintype κ] [FiniteDimensional F A]

theorem finrank_classProjection_range {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) :
    finrank F (LinearMap.range (classProjection (F := F) (A := A) p r)) =
      Fintype.card κ * d * finrank F A := by
  rw [(classProjectionRangeEquiv (F := F) (A := A) hr).finrank_eq]
  simp [Module.finrank_pi_fintype, ZMod.card, mul_assoc]

theorem finrank_completedCode {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (C : Submodule F (State d A)) :
    finrank F (completedCode p r C) =
      finrank F (C ⊓ LinearMap.ker (classProjection (F := F) p r) : Submodule F (State d A)) +
      Fintype.card κ * d * finrank F A := by
  have hd := (classProjection_ker_disjoint_range (F := F) (A := A) hr).mono_left
    (inf_le_right : C ⊓ LinearMap.ker (classProjection (F := F) p r) ≤ _)
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (C ⊓ LinearMap.ker (classProjection (F := F) p r)) (LinearMap.range (classProjection (F := F) p r))
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_classProjection_range hr] at hh
  exact hh

theorem finrank_le_completedCode {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (C : Submodule F (State d A)) :
    finrank F C ≤ finrank F (completedCode p r C) := by
  let P := classProjection (F := F) (A := A) p r
  have hnull := LinearMap.finrank_range_add_finrank_ker (P.comp C.subtype)
  have hker : finrank F (LinearMap.ker (P.comp C.subtype)) = finrank F (C ⊓ LinearMap.ker P : Submodule F (State d A)) := by
    rw [LinearMap.ker_comp]
    have hco : (C ⊓ P.ker).comap C.subtype = P.ker.comap C.subtype := by
      ext x
      simp
    rw [← hco]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ LinearMap.ker P ≤ C)).finrank_eq
  have hran : finrank F (LinearMap.range (P.comp C.subtype)) ≤
      finrank F (LinearMap.range P) := Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  rw [hker] at hnull
  rw [finrank_completedCode hr, ← finrank_classProjection_range hr]
  dsimp [P] at hnull hran
  omega

theorem finrank_completedCode_add_rank {p : ZMod d → κ} {r : κ → ZMod d}
    (hr : ∀ a, p (r a) = a) (C : Submodule F (State d A)) :
    finrank F (completedCode p r C) +
      finrank F (LinearMap.range ((classProjection p r).comp C.subtype)) =
      finrank F C + Fintype.card κ * d * finrank F A := by
  let P := classProjection (F := F) (A := A) p r
  have hnull := LinearMap.finrank_range_add_finrank_ker (P.comp C.subtype)
  have hker : finrank F (LinearMap.ker (P.comp C.subtype)) =
      finrank F (C ⊓ LinearMap.ker P : Submodule F (State d A)) := by
    rw [LinearMap.ker_comp]
    have hco : (C ⊓ P.ker).comap C.subtype = P.ker.comap C.subtype := by
      ext x
      simp
    rw [← hco]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : C ⊓ LinearMap.ker P ≤ C)).finrank_eq
  rw [hker] at hnull
  rw [finrank_completedCode hr]
  dsimp [P] at hnull
  omega

end SharedDecoders
