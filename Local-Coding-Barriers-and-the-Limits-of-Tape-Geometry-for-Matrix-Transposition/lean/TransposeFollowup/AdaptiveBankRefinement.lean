import TransposeFollowup.AdaptiveBankProtocol

/-! A leaf-dependent pin list is queried only after the original public
execution ends. Every appended value is an actual charged unary answer. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace LocalQuery

def coordinate {V : Type*} (v : V) : LocalQuery V (fun _ => Bool) where
  support := {v}
  read := fun y => y v
  locality := by intro x y h; exact h v (Finset.mem_singleton_self v)

end LocalQuery

namespace PublicProtocol

variable {V : Type*}

def observeCoordinates : List V → PublicProtocol V (fun _ => Bool)
  | [] => .halt
  | v :: vs => .query (.coordinate v) (fun _ => observeCoordinates vs)

@[simp] theorem run_observeCoordinates (vs : List V) (y : V → Bool) :
    (observeCoordinates vs).run y = vs.map y := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [observeCoordinates, run, LocalQuery.coordinate] using congrArg (List.cons (y v)) ih

/-- The accumulated history, not a private input-dependent selector, chooses
the finite ordered pin list at each completed public leaf. -/
def appendCoordinates (pins : List Bool → List V) :
    PublicProtocol V (fun _ => Bool) → List Bool → PublicProtocol V (fun _ => Bool)
  | .halt, h => observeCoordinates (pins h)
  | .query q next, h => .query q (fun a => appendCoordinates pins (next a) (h ++ [a]))

theorem run_appendCoordinates (p : PublicProtocol V (fun _ => Bool))
    (pins : List Bool → List V) (h : List Bool) (y : V → Bool) :
    (appendCoordinates pins p h).run y =
      p.run y ++ (pins (h ++ p.run y)).map y := by
  induction p generalizing h with
  | halt => simp [appendCoordinates, run]
  | query q next ih =>
    simp [appendCoordinates, run, ih, List.append_assoc]

theorem length_run_appendCoordinates (p : PublicProtocol V (fun _ => Bool))
    (pins : List Bool → List V) (y : V → Bool) :
    ((appendCoordinates pins p []).run y).length =
      (p.run y).length + (pins (p.run y)).length := by
  simp [run_appendCoordinates]

theorem run_appendCoordinates_eq_iff (p : PublicProtocol V (fun _ => Bool))
    (pins : List Bool → List V) (h : List Bool) (x y : V → Bool) :
    (appendCoordinates pins p h).run x = (appendCoordinates pins p h).run y ↔
      p.run x = p.run y ∧
        (pins (h ++ p.run x)).map x = (pins (h ++ p.run x)).map y := by
  induction p generalizing h with
  | halt => simp [appendCoordinates, run]
  | query q next ih =>
    by_cases ha : q.read x = q.read y
    · simp only [appendCoordinates, run, ha, List.cons.injEq, true_and]
      rw [ih (q.read y)]
      simp only [List.append_assoc, List.singleton_append]
    · simp [appendCoordinates, run, ha]

/-- The refined full fiber is exactly the original full fiber plus the
selected coordinate pins, not a new support graph with old edges erased. -/
theorem fullFiber_appendCoordinates [Fintype V] [DecidableEq V]
    (p : PublicProtocol V (fun _ => Bool)) (pins : List Bool → List V)
    (base : V → Bool) :
    (appendCoordinates pins p []).fullFiber ((appendCoordinates pins p []).run base) =
      p.pinnedFiber (p.run base) (pins (p.run base)).toFinset base := by
  ext y
  simp only [mem_fullFiber, mem_pinnedFiber, run_appendCoordinates_eq_iff,
    List.nil_append, List.mem_toFinset]
  constructor
  · rintro ⟨hm, hv⟩
    refine ⟨hm, ?_⟩
    rw [hm] at hv
    exact List.map_inj_left.mp hv
  · rintro ⟨hm, hv⟩
    refine ⟨hm, ?_⟩
    rw [hm]
    exact List.map_inj_left.mpr hv

end PublicProtocol

end TransposeFollowup
