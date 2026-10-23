import TransposeFollowup.ProtocolTruncation
import TransposeFollowup.InteractionGraph
import TransposeFollowup.RectangleEntropy

/-! Public coordinate queries and their actual full-cube fibers. The existing
public strategy interface permits nontermination outside a correct family;
its finite truncations retain exactly the charged terminating transcripts.
No independence of a promised input family is assumed here. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

namespace PublicProtocol

variable {V K : Type*} [Fintype V] [DecidableEq V] [DecidableEq K]

/-- The full stored-cube fiber, retaining assignments outside the correct family. -/
noncomputable def fullFiber (p : PublicProtocol V (fun _ => Bool))
    (m : List Bool) : Finset (V → Bool) := Finset.univ.filter (fun y => p.run y = m)

@[simp] theorem mem_fullFiber (p : PublicProtocol V (fun _ => Bool))
    (m : List Bool) (y : V → Bool) : y ∈ p.fullFiber m ↔ p.run y = m := by
  simp [fullFiber]

/-- Publicly selected coordinate values refine a transcript fiber. -/
noncomputable def pinnedFiber (p : PublicProtocol V (fun _ => Bool))
    (m : List Bool) (pins : Finset V) (base : V → Bool) : Finset (V → Bool) :=
  (p.fullFiber m).filter (fun y => ∀ v ∈ pins, y v = base v)

@[simp] theorem mem_pinnedFiber (p : PublicProtocol V (fun _ => Bool))
    (m : List Bool) (pins : Finset V) (base y : V → Bool) :
    y ∈ p.pinnedFiber m pins base ↔ p.run y = m ∧ ∀ v ∈ pins, y v = base v := by
  simp [pinnedFiber]

/-- Pinning one endpoint of each inter-group query suffices for exact product
fibers. The owner may still assign a pinned coordinate to its original group. -/
theorem coordinateRectangle_pinnedFiber (p : PublicProtocol V (fun _ => Bool))
    (m : List Bool) (pins : Finset V) (owner : V → K) (base : V → Bool)
    (hb : p.run base = m) (hs : p.Along (Separated pins owner) m) :
    CoordinateRectangle owner (p.pinnedFiber m pins base) := by
  intro x hx
  have hw : ∀ a, ∃ y : V → Bool, p.run y = m ∧
      (∀ v ∈ pins, y v = base v) ∧ ∀ v, owner v = a → y v = x v := by
    intro a
    obtain ⟨y, hy, he⟩ := hx a
    obtain ⟨hm, hpin⟩ := (p.mem_pinnedFiber m pins base y).mp hy
    refine ⟨y, hm, hpin, ?_⟩
    intro v hv
    have hxy := (bitView_eq_iff _ x y).mp he v
    exact (hxy (by simp [ownedCoordinates, hv])).symm
  have hfix : ∀ v ∈ pins, x v = base v := by
    intro v hv
    obtain ⟨y, _, hp, hy⟩ := hw (owner v)
    exact (hy v rfl).symm.trans (hp v hv)
  exact (p.mem_pinnedFiber m pins base x).mpr
    ((p.fiber_factorization m pins owner base x hb hs).mpr ⟨hfix, hw⟩)

theorem coordinateRectangle_fullFiber (p : PublicProtocol V (fun _ => Bool))
    (m : List Bool) (owner : V → K) (base : V → Bool)
    (hb : p.run base = m) (hs : p.Along (Separated ∅ owner) m) :
    CoordinateRectangle owner (p.fullFiber m) := by
  have he : p.pinnedFiber m ∅ base = p.fullFiber m := by
    ext y
    simp
  rw [← he]
  exact p.coordinateRectangle_pinnedFiber m ∅ owner base hb hs

theorem coordinateRectangle_fullFiber_of_edges
    (p : PublicProtocol V (fun _ => Bool)) (m : List Bool)
    (owner : V → K) (base : V → Bool) (hb : p.run base = m)
    (howner : ∀ v w, (p.interactionGraph m).Adj v w → owner v = owner w) :
    CoordinateRectangle owner (p.fullFiber m) := by
  apply p.coordinateRectangle_fullFiber m owner base hb
  exact p.along_separated_of_graph_compatible m ∅ owner
    (fun v _ w _ h => howner v w h)

omit [Fintype V] [DecidableEq V] in
/-- Actual query occurrences, including constants and repeats, are bounded
by the length of the supplied answer string. -/
theorem querySupports_length_le (p : PublicProtocol V (fun _ => Bool)) (m : List Bool) :
    (p.querySupports m).length ≤ m.length := by
  induction p generalizing m with
  | halt => simp [querySupports]
  | query q next ih =>
    cases m with
    | nil => simp [querySupports]
    | cons a m => simpa [querySupports] using ih a m

omit [Fintype V] [DecidableEq V] in
theorem querySupports_run_length (p : PublicProtocol V (fun _ => Bool)) (y : V → Bool) :
    (p.querySupports (p.run y)).length = (p.run y).length := by
  induction p with
  | halt => rfl
  | query q next ih => simp [run, querySupports, ih]

end PublicProtocol

end TransposeFollowup
