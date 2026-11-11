import SharedDecoders.ConstructionProjector
import SharedDecoders.CapacityCompletion

/-! # The complete deterministic cyclic lift in product coordinates -/

namespace SharedDecoders

open Module LinearMap

variable {F A G I κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup G] [Fintype G]

theorem orbitInflate_injective (hG : (Fintype.card G : F) ≠ 0) :
    Function.Injective (orbitInflate (F := F) (A := A) (G := G) (I := I)) := by
  intro X Y h
  have hh := congrArg (orbitAverage (F := F)) h
  simpa only [orbitAverage_inflate hG] using hh

def inflateSeed (C : Submodule F (I → I → A)) : (G → C) →ₗ[F] LiftState G I A where
  toFun Y := orbitInflate (F := F) (fun z => (Y z : I → I → A))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def liftNull : Submodule F (LiftState G I A) :=
  symmetricSpace ⊓ LinearMap.ker (orbitAverage (F := F))

def liftedCode (C : Submodule F (I → I → A)) : Submodule F (LiftState G I A) :=
  liftNull ⊔ LinearMap.range (inflateSeed C)

theorem liftNull_disjoint_seed (hG : (Fintype.card G : F) ≠ 0)
    (C : Submodule F (I → I → A)) :
    Disjoint (liftNull (G := G)) (LinearMap.range (inflateSeed C)) := by
  rw [Submodule.disjoint_def]
  intro X hX hY
  obtain ⟨Y, rfl⟩ := hY
  have hh : (fun z => (Y z : I → I → A)) = 0 := by
    have havg := LinearMap.mem_ker.mp hX.2
    change orbitAverage (F := F) (orbitInflate (F := F) (fun z => (Y z : I → I → A))) = 0 at havg
    rwa [orbitAverage_inflate hG] at havg
  change orbitInflate (F := F) (fun z => (Y z : I → I → A)) = 0
  rw [hh, map_zero]

variable {s : ℕ}

def IsProductSharedCode (p : ZMod s → κ) (C : Submodule F (LiftState G (ZMod s) A)) : Prop :=
  ∃ f : κ → LiftState G (ZMod s) A → (G × ZMod s → A),
    ∀ X ∈ C, ∀ u v, X (u, v) = f (p v) (liftRot u v X)

def liftedDecoder (f : κ → State s A → (ZMod s → A))
    (a : κ) (Y : LiftState G (ZMod s) A) (ar : G × ZMod s) : A :=
  (Y - cyclicProjector (F := F) Y) ar (0, 0) +
    f a (orbitAverage (F := F) Y ar.1) ar.2

theorem liftedDecoder_correct {p : ZMod s → κ} {C : Submodule F (State s A)}
    (f : κ → State s A → (ZMod s → A))
    (hf : ∀ X ∈ C, ∀ c, X c = f (p c) (rot c X))
    (hG : (Fintype.card G : F) ≠ 0) :
    ∀ X ∈ liftedCode (G := G) C, ∀ u v,
      X (u, v) = liftedDecoder (F := F) f (p v) (liftRot u v X) := by
  intro X hX u v
  obtain ⟨X₀, h₀, H, hH, rfl⟩ := Submodule.mem_sup.mp hX
  obtain ⟨Y, rfl⟩ := hH
  have havg₀ : orbitAverage (F := F) X₀ = 0 := LinearMap.mem_ker.mp h₀.2
  have havgH : orbitAverage (F := F) (inflateSeed C Y) = fun z => (Y z : State s A) :=
    orbitAverage_inflate hG (fun z => (Y z : State s A))
  have he₀ : cyclicProjector (F := F) X₀ = 0 := by
    change orbitInflate (F := F) (orbitAverage (F := F) X₀) = 0
    rw [havg₀, map_zero]
  have heH : cyclicProjector (F := F) (inflateSeed C Y) = inflateSeed C Y := by
    change orbitInflate (F := F) (orbitAverage (F := F) (inflateSeed C Y)) = _
    rw [havgH]
    rfl
  have hstrip : liftRot u v (X₀ + inflateSeed C Y) -
      cyclicProjector (F := F) (liftRot u v (X₀ + inflateSeed C Y)) = liftRot u v X₀ := by
    rw [cyclicProjector_rot, map_add, he₀, heH, zero_add]
    funext ar hc
    simp [liftRot]
  funext ar
  rcases ar with ⟨a, r⟩
  dsimp only [liftedDecoder]
  rw [hstrip]
  have harg : orbitAverage (F := F) (liftRot u v (X₀ + inflateSeed C Y)) a =
      rot v (Y (a + u) : State s A) := by
    funext i j
    rw [orbitAverage_rot]
    have hz := congrFun (congrFun (congrFun
      (show orbitAverage (F := F) (X₀ + inflateSeed C Y) = fun z => (Y z : State s A) by
        rw [map_add, havg₀, havgH, zero_add]) (a + u)) i) (j + v)
    exact hz
  rw [harg, ← hf (Y (a + u)) (Y (a + u)).property v]
  have hsym := h₀.1 (u, v) (a, r)
  change X₀ (u, v) (a, r) + (Y (u + a) : State s A) v r =
    X₀ (a, r) (0 + u, 0 + v) + (Y (a + u) : State s A) v r
  rw [zero_add, zero_add, hsym, add_comm u a]

theorem IsSharedCode.liftedCode {p : ZMod s → κ}
    {C : Submodule F (State s A)} (h : IsSharedCode F p C)
    (hG : (Fintype.card G : F) ≠ 0) : IsProductSharedCode p (liftedCode (G := G) C) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨liftedDecoder (F := F) f, liftedDecoder_correct f hf hG⟩

end SharedDecoders
