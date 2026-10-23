import TransposeFollowup.AdaptiveForestCount

/-! The selected forest refinement is an actual public protocol. Its pin list
is a function of the completed transcript alone. -/

namespace TransposeFollowup.AdaptiveForest

open Classical
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def residue (G : SimpleGraph V) (R : ℕ) (hR : 0 < R) : Fin R :=
  (exists_pins_card_mul_le G hR).choose

omit [DecidableEq V] in
theorem residue_charge (G : SimpleGraph V) (R : ℕ) (hR : 0 < R) :
    R * (pins G R (residue G R hR).val).card ≤ (nonroots G).card :=
  (exists_pins_card_mul_le G hR).choose_spec

noncomputable def selectedPins (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (m : List Bool) : Finset V :=
  pins (p.interactionGraph m) R (residue (p.interactionGraph m) R hR).val

noncomputable def owner (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (m : List Bool) : V → V :=
  ancestor (p.interactionGraph m) R (residue (p.interactionGraph m) R hR).val

noncomputable def refined (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) : PublicProtocol V (fun _ => Bool) :=
  p.appendCoordinates (fun m => (selectedPins p R hR m).toList) []

theorem selectedPins_charge (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (m : List Bool)
    (hG : (p.interactionGraph m).IsAcyclic)
    (hpair : p.Along (fun s => s.card ≤ 2) m) :
    R * (selectedPins p R hR m).card ≤ m.length :=
  (residue_charge (p.interactionGraph m) R hR).trans
    (nonroots_card_le_queries p m hG hpair)

omit [DecidableEq V] in
theorem refined_length (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (y : V → Bool) :
    ((refined p R hR).run y).length =
      (p.run y).length + (selectedPins p R hR (p.run y)).card := by
  simp [refined, PublicProtocol.length_run_appendCoordinates]

theorem refined_length_mul_le (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (y : V → Bool)
    (hG : (p.interactionGraph (p.run y)).IsAcyclic)
    (hpair : p.Along (fun s => s.card ≤ 2) (p.run y)) :
    R * ((refined p R hR).run y).length ≤ (R + 1) * (p.run y).length := by
  rw [refined_length, Nat.mul_add, Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left (selectedPins_charge p R hR (p.run y) hG hpair) _

theorem refined_fiber (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (base : V → Bool) :
    (refined p R hR).fullFiber ((refined p R hR).run base) =
      p.pinnedFiber (p.run base) (selectedPins p R hR (p.run base)) base := by
  simpa [refined] using p.fullFiber_appendCoordinates
    (fun m => (selectedPins p R hR m).toList) base

theorem refined_rectangle (p : PublicProtocol V (fun _ => Bool))
    (R : ℕ) (hR : 0 < R) (base : V → Bool)
    (hG : (p.interactionGraph (p.run base)).IsAcyclic) :
    CoordinateRectangle (owner p R hR (p.run base))
      ((refined p R hR).fullFiber ((refined p R hR).run base)) := by
  rw [refined_fiber]
  exact p.coordinateRectangle_pinnedFiber _ _ _ _ rfl
    (forest_along_ancestor p _ hG hR (residue _ R hR).isLt)

/-- Whole ancestor classes can be grouped further without losing the full
fiber product property. The grouping is fixed after the public leaf is fixed. -/
theorem refined_rectangle_grouped {A : Type*} [DecidableEq A]
    (p : PublicProtocol V (fun _ => Bool)) (R : ℕ) (hR : 0 < R)
    (base : V → Bool) (hG : (p.interactionGraph (p.run base)).IsAcyclic)
    (group : V → A) :
    CoordinateRectangle (group ∘ owner p R hR (p.run base))
      ((refined p R hR).fullFiber ((refined p R hR).run base)) := by
  rw [refined_fiber]
  apply p.coordinateRectangle_pinnedFiber _ _ _ _ rfl
  apply p.along_separated_of_graph_compatible
  intro v hv w hw ha
  exact congrArg group (ancestor_eq_of_adj_not_pinned _ hG hR
    (residue _ R hR).isLt hv hw ha)

/-- The grouping may be given directly on coordinates, provided it is constant
on each ancestor class. This avoids introducing unused group labels. -/
theorem refined_rectangle_of_owner_factors {A : Type*} [DecidableEq A]
    (p : PublicProtocol V (fun _ => Bool)) (R : ℕ) (hR : 0 < R)
    (base : V → Bool) (hG : (p.interactionGraph (p.run base)).IsAcyclic)
    (group : V → A)
    (hgroup : ∀ v w, owner p R hR (p.run base) v = owner p R hR (p.run base) w → group v = group w) :
    CoordinateRectangle group
      ((refined p R hR).fullFiber ((refined p R hR).run base)) := by
  rw [refined_fiber]
  apply p.coordinateRectangle_pinnedFiber _ _ _ _ rfl
  apply p.along_separated_of_graph_compatible
  intro v hv w hw ha
  apply hgroup
  exact ancestor_eq_of_adj_not_pinned _ hG hR (residue _ R hR).isLt hv hw ha

end TransposeFollowup.AdaptiveForest
