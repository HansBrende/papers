import SharedDecoders.ConstructionCRT

/-! # The whole correctness set of the displayed cyclic lift

If the seed subspace is the full correctness set of its displayed decoder,
the lifted source is also the full correctness set. The proof applies to
arbitrary deterministic seed decoders under that exact seed premise.
-/

namespace SharedDecoders

variable {F A G κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup G] [Fintype G] {s : ℕ}

theorem average_projector_residual (hG : (Fintype.card G : F) ≠ 0)
    (X : LiftState G (ZMod s) A) :
    orbitAverage (F := F) (X - cyclicProjector (F := F) X) = 0 := by
  rw [map_sub]
  change orbitAverage (F := F) X -
    orbitAverage (F := F) (orbitInflate (F := F) (orbitAverage (F := F) X)) = 0
  rw [orbitAverage_inflate hG, sub_self]

theorem average_swap_projector_residual (hG : (Fintype.card G : F) ≠ 0)
    (X : LiftState G (ZMod s) A) :
    orbitAverage (F := F) (liftSwap (X - cyclicProjector (F := F) X)) = 0 := by
  funext z r c
  rw [orbitAverage_swap]
  exact congrFun (congrFun (congrFun (average_projector_residual hG X) z) c) r

theorem lifted_rule_global {p : ZMod s → κ}
    (f : κ → State s A → (ZMod s → A)) (X : LiftState G (ZMod s) A)
    (h : ∀ u v, X (u,v) = liftedDecoder (F := F) f (p v) (liftRot u v X)) :
    X = liftSwap (X - cyclicProjector (F := F) X) +
      orbitInflate (F := F) (fun z v r => f (p v) (rot v (orbitAverage (F := F) X z)) r) := by
  funext uv ar
  rcases uv with ⟨u,v⟩
  rcases ar with ⟨a,r⟩
  have hh := congrFun (h u v) (a,r)
  dsimp only [liftedDecoder] at hh
  rw [cyclicProjector_rot] at hh
  have harg : orbitAverage (F := F) (liftRot u v X) a =
      rot v (orbitAverage (F := F) X (a+u)) := by
    funext i j
    rw [orbitAverage_rot]
    rfl
  rw [harg] at hh
  change X (u,v) (a,r) = (X (a,r) (u,v) - cyclicProjector (F := F) X (a,r) (u,v)) +
    f (p v) (rot v (orbitAverage (F := F) X (u+a))) r
  simpa only [liftRot, Pi.sub_apply, zero_add, add_comm a u] using hh

/-- No extra correctness inputs appear beyond the lifted code when the seed is exact. -/
theorem mem_liftedCode_iff_full_rule {p : ZMod s → κ}
    (f : κ → State s A → (ZMod s → A)) (C : Submodule F (State s A))
    (hfull : ∀ Y, Y ∈ C ↔ ∀ c, Y c = f (p c) (rot c Y))
    (hG : (Fintype.card G : F) ≠ 0) (X : LiftState G (ZMod s) A) :
    X ∈ liftedCode (G := G) C ↔
      ∀ u v, X (u,v) = liftedDecoder (F := F) f (p v) (liftRot u v X) := by
  constructor
  · exact fun hX => liftedDecoder_correct f (fun Y hY => (hfull Y).mp hY) hG X hX
  · intro hX
    let H := orbitAverage (F := F) X
    let R : G → State s A := fun z v r => f (p v) (rot v (H z)) r
    have hg : X = liftSwap (X - cyclicProjector (F := F) X) + orbitInflate (F := F) R :=
      lifted_rule_global f X hX
    have hHR : H = R := by
      have hh := congrArg (orbitAverage (F := F)) hg
      rwa [map_add, average_swap_projector_residual hG X, orbitAverage_inflate hG, zero_add] at hh
    have hC (z : G) : H z ∈ C := by
      apply (hfull _).mpr
      intro c
      exact congrFun (congrFun hHR z) c
    have hsym : X - cyclicProjector (F := F) X ∈ symmetricSpace (F := F) := by
      have hr : orbitInflate (F := F) R = cyclicProjector (F := F) X := by
        rw [← hHR]
        rfl
      rw [hr] at hg
      have he : X - cyclicProjector (F := F) X =
          liftSwap (X - cyclicProjector (F := F) X) := sub_eq_iff_eq_add.mpr hg
      intro ar bt
      exact congrFun (congrFun he ar) bt
    apply Submodule.mem_sup.mpr
    refine ⟨X - cyclicProjector (F := F) X, ?_, cyclicProjector (F := F) X, ?_, ?_⟩
    · exact ⟨hsym, LinearMap.mem_ker.mpr (average_projector_residual hG X)⟩
    · exact ⟨fun z => ⟨H z, hC z⟩, rfl⟩
    · exact sub_add_cancel X (cyclicProjector (F := F) X)

end SharedDecoders
