import Transpose.Frames.GadgetMixing

/-!
# Item itineraries and the itinerary condition for tight two-class coarsenings

Formalisation of item itineraries — chain existence and the admissibility condition under tight
two-class coarsenings — in the run model of `GadgetRuns.lean`, using the presence sets of
`GadgetMixing.lean` and the cargo rule of `GadgetCargo.lean`.  Chains are found by following an
item backwards through the moves that carry it (`chain_of_present`).  The stronger statement that
every carrying move lies on such a chain (hence condition (C)) is formalised in
`GadgetItineraryC.lean`.

Setting: a valid run `evs` from `init S` ending with wire `ρ u` at frame `tgt u` holding `e u`.
A *hop* of item `s` is a move `.move w f₁` of the run whose cargo (the vector of `w` just before
the move) has `s`-coordinate `1`; its origin is the frame of `w` just before the move.  A *chain*
of `s` from `f₀` to `fk` is a strictly increasing list of positions of hops of `s` in `evs`, the
first starting at `f₀`, each starting where the previous one ends, the last ending at `fk`.

* `IsHop c evs s i f₀ f₁`, `IsChain c evs s f₀ fk is`: hops and chains (positions `i` into `evs`,
  run from `c`).
* `chain_of_present` (presence in chain form): if `s` is present at `f` after a valid segment, it
  was present at some `f'` before it and there is a chain of `s` from `f'` to `f` along the segment.
* `chain_exists` / `chain_exists_visible` (**item itineraries, chain existence**):
  every item `s` has a chain from `S s` to `tgt s` along the run, all of whose hops change the
  frame (`Visible`).
* `cargo_rule_coarse`: the cargo rule of `GadgetCargo.lean` transported through a two-class
  coarsening `π : F → Bool` with `π (tgt u) = !π (S u)`: if exactly `W` moves of the run are
  `π`-visible, the cargo of every `π`-visible move lies in the span of the items whose home class
  is the destination class.
* `itinerary_condition` (**item itineraries, admissibility at one functional**): under the same
  tightness hypothesis, every `π`-visible hop of `s` starts on the birth side of `s`:
  `π (origin) = π (S s)`.
* `chain_itinerary`: the two combined — a chain of `s` from `S s` to `tgt s` all of whose
  `π`-visible hops start on the birth side of `s`.
* `vmoves_map_eq_countP`: the number of `π`-visible moves is the number of jumps whose
  endpoints have distinct `π`-classes.
* Matrix instance (`F = Matrix (Fin m) (Fin m) (ZMod 2)`, `tgt u = S u + 1`, `π_Λ M = ⟪Λ, M⟫`
  with `tr Λ = 1`): `itinerary_condition_matrix`: for a tight `Λ` with `⟪Λ, J⟫ = 1` at a hop with
  jump `J = f₁ - f₀` carrying `s`, `⟪Λ, S s + f₀⟫ = 0`.
-/

namespace Transpose.ShearFrame

variable {W : ℕ} {F : Type}

/-! ### Hops and chains -/

/-- The event at position `i` of `evs` (run from `c`) is a hop of item `s` from frame `f₀` to
frame `f₁`: it is `.move w f₁` for a wire `w` which, just before the event, is at `f₀` and whose
vector has `s`-coordinate `1` (the cargo carries `s`). -/
def IsHop (c : Cfg W F) (evs : List (Event W F)) (s : Fin W) (i : ℕ) (f₀ f₁ : F) : Prop :=
  ∃ w, evs[i]? = some (.move w f₁) ∧ (c.run (evs.take i)).frame w = f₀ ∧
    (c.run (evs.take i)).vec w s = 1

/-- `IsChain c evs s f₀ fk is`: the positions `is` form a chain of hops of `s` from `f₀` to `fk`
along `evs` (run from `c`): the empty chain requires `f₀ = fk`; otherwise the first position is a
hop from `f₀` to some `f₁`, all later positions are larger, and the rest is a chain from `f₁` to
`fk`. -/
def IsChain (c : Cfg W F) (evs : List (Event W F)) (s : Fin W) : F → F → List ℕ → Prop
  | f₀, fk, [] => f₀ = fk
  | f₀, fk, i :: is => ∃ f₁, IsHop c evs s i f₀ f₁ ∧ (∀ j ∈ is, i < j) ∧ IsChain c evs s f₁ fk is

/-- The positions of a chain are strictly increasing. -/
theorem IsChain.pairwise {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain c evs s f₀ fk is → is.Pairwise (· < ·)
  | _, _, [], _ => List.Pairwise.nil
  | _, _, _ :: _, ⟨_, _, hlt, hc⟩ => List.Pairwise.cons hlt hc.pairwise

/-- Every position of a chain is a hop of `s` (between some frames). -/
theorem IsChain.hop_of_mem {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain c evs s f₀ fk is → ∀ i ∈ is, ∃ g₀ g₁, IsHop c evs s i g₀ g₁
  | _, _, [], _, _, h => (List.not_mem_nil h).elim
  | f₀, _, i :: is, ⟨f₁, hhop, _, hc⟩, j, hj => by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨f₀, f₁, hhop⟩
      · exact hc.hop_of_mem j hj

/-- Every position of a chain is a move of the run carrying `s`. -/
theorem IsChain.carries_of_mem {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {f₀ fk : F}
    {is : List ℕ} (hc : IsChain c evs s f₀ fk is) {i : ℕ} (hi : i ∈ is) :
    ∃ w f₁, evs[i]? = some (.move w f₁) ∧ (c.run (evs.take i)).vec w s = 1 := by
  obtain ⟨_, _, w, hw, _, hs⟩ := hc.hop_of_mem i hi
  exact ⟨w, _, hw, hs⟩

/-- Shifting a hop past one more event at the front. -/
theorem IsHop.succ {c : Cfg W F} {ev : Event W F} {evs : List (Event W F)} {s : Fin W} {i : ℕ}
    {f₀ f₁ : F} (h : IsHop (c.step ev) evs s i f₀ f₁) : IsHop c (ev :: evs) s (i + 1) f₀ f₁ := by
  obtain ⟨w, hw, hf, hs⟩ := h
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [List.getElem?_cons_succ]; exact hw
  · rw [List.take_succ_cons]; exact hf
  · rw [List.take_succ_cons]; exact hs

/-- Shifting a chain past one more event at the front. -/
theorem IsChain.succ {c : Cfg W F} {ev : Event W F} {evs : List (Event W F)} {s : Fin W} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain (c.step ev) evs s f₀ fk is →
      IsChain c (ev :: evs) s f₀ fk (is.map (· + 1))
  | _, _, [], h => h
  | _, _, i :: is, ⟨f₁, hhop, hlt, hc⟩ => by
      refine ⟨f₁, hhop.succ, ?_, hc.succ⟩
      intro j hj
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
      exact Nat.succ_lt_succ (hlt j' hj')

/-- All hops at the positions `is` are *visible*: they change the frame of the moved wire. -/
def Visible (c : Cfg W F) (evs : List (Event W F)) (is : List ℕ) : Prop :=
  ∀ i ∈ is, ∀ (w : Fin W) (f₁ : F), evs[i]? = some (.move w f₁) →
    (c.run (evs.take i)).frame w ≠ f₁

theorem Visible.succ {c : Cfg W F} {ev : Event W F} {evs : List (Event W F)} {is : List ℕ}
    (h : Visible (c.step ev) evs is) : Visible c (ev :: evs) (is.map (· + 1)) := by
  intro j hj w f₁ hw
  obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
  rw [List.getElem?_cons_succ] at hw
  rw [List.take_succ_cons]
  exact h j' hj' w f₁ hw

/-! ### Presence in chain form: presence is created only by hops -/

/-- If `s` is present at `f` after a valid segment, it was present at some `f'` before the
segment and there is a chain of visible hops of `s` from `f'` to `f` along the segment. -/
theorem chain_of_present (s : Fin W) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs → ∀ f, (c.run evs).present s f →
      ∃ f' is, c.present s f' ∧ IsChain c evs s f' f is ∧ Visible c evs is
  | [], c, _, f, h => ⟨f, [], h, rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | .gate i j :: evs, c, hv, f, h => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      obtain ⟨f', is, hf', hc, hvis⟩ := chain_of_present s evs (c.step (.gate i j)) hv' f h
      exact ⟨f', is.map (· + 1), (present_gate c hij hf s f').mp hf', hc.succ, hvis.succ⟩
  | .move w f₁ :: evs, c, hv, f, h => by
      obtain ⟨_, hv'⟩ := hv
      obtain ⟨f', is, hf', hc, hvis⟩ := chain_of_present s evs (c.step (.move w f₁)) hv' f h
      by_cases hs : c.vec w s = 1
      · obtain ⟨w', hw', hs'⟩ := hf'
        by_cases hww : w' = w
        · -- the witness is the moved wire
          subst hww
          have hf1 : f' = f₁ := by simpa [Cfg.step] using hw'.symm
          subst hf1
          by_cases hnoop : c.frame w' = f'
          · -- an invisible move: `s` was already present at `f'`
            exact ⟨f', is.map (· + 1), ⟨w', hnoop, hs⟩, hc.succ, hvis.succ⟩
          · -- a visible move: it is the first hop
            refine ⟨c.frame w', 0 :: is.map (· + 1), ⟨w', rfl, hs⟩,
              ⟨f', ⟨w', rfl, rfl, hs⟩, ?_, hc.succ⟩, ?_⟩
            · intro j hj
              obtain ⟨j', _, rfl⟩ := List.mem_map.mp hj
              exact Nat.succ_pos j'
            · intro j hj w'' f'' hw''
              rcases List.mem_cons.mp hj with rfl | hj
              · obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw'')
                exact hnoop
              · exact hvis.succ j hj w'' f'' hw''
        · refine ⟨f', is.map (· + 1), ⟨w', ?_, hs'⟩, hc.succ, hvis.succ⟩
          simpa [Cfg.step, Function.update_of_ne hww] using hw'
      · exact ⟨f', is.map (· + 1), (present_move_of_ne_one c w f₁ hs f').mp hf', hc.succ,
          hvis.succ⟩

/-- **Item itineraries, chain existence, visible form.** In a valid run from `init S`
ending with wire `ρ u` at frame `tgt u` holding `e u`, every item `s` has a chain of
frame-changing hops from `S s` to `tgt s`. -/
theorem chain_exists_visible (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) (s : Fin W) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (tgt s) is ∧ Visible (init S) evs is := by
  obtain ⟨f', is, hf', hc, hvis⟩ := chain_of_present s evs (init S) hv (tgt s)
    ((present_final _ tgt ρ hframe hvec s (tgt s)).mpr rfl)
  rw [← (present_init S s f').mp hf'] at hc
  exact ⟨is, hc, hvis⟩

/-- **Item itineraries, chain existence.** In a valid run from `init S` ending with
wire `ρ u` at frame `tgt u` holding `e u`, every item `s` has a chain of hops from `S s` to
`tgt s`: strictly increasing positions `i₁ < ⋯ < i_k` into `evs`, each a move `.move w_j f_j`
whose cargo `((init S).run (evs.take i_j)).vec w_j` has `s`-coordinate `1`, the origin of the
first hop being `S s`, the destination `f_j` of hop `j` being the origin of hop `j + 1`, and
`f_k = tgt s` (the empty chain if `S s = tgt s`). -/
theorem chain_exists (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) (s : Fin W) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (tgt s) is :=
  let ⟨is, hc, _⟩ := chain_exists_visible S tgt ρ evs hv hframe hvec s
  ⟨is, hc⟩

/-! ### Supports of vectors in a target span -/

/-- A vector of `targetI T f` vanishes at every item whose `T`-value is not `f`. -/
theorem apply_eq_zero_of_mem_targetI {T : Fin W → F} {f : F} {x : Vec W} (hx : x ∈ targetI T f)
    {s : Fin W} (hs : T s ≠ f) : x s = 0 := by
  have hle : targetI T f ≤ LinearMap.ker (LinearMap.proj s : Vec W →ₗ[ZMod 2] ZMod 2) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    exact e_apply_of_ne (fun h => hs (h ▸ hu))
  have h := LinearMap.mem_ker.mp (hle hx)
  rwa [LinearMap.proj_apply] at h

/-- An item carried by a vector of `targetI T f` has `T`-value `f`. -/
theorem eq_of_mem_targetI_of_apply_eq_one {T : Fin W → F} {f : F} {x : Vec W}
    (hx : x ∈ targetI T f) {s : Fin W} (hs : x s = 1) : T s = f := by
  by_contra h
  rw [apply_eq_zero_of_mem_targetI hx h] at hs
  exact absurd hs (by decide)

/-! ### The cargo rule through a two-class coarsening -/

/-- The coarsened run from `init S` is the run from `init (π ∘ S)`. -/
theorem init_map {F' : Type} (π : F → F') (S : Fin W → F) :
    (init S).map π = init (fun u => π (S u)) := rfl

/-- **Cargo rule, coarsened.** Let `π : F → Bool` separate every source from its target
(`π (tgt u) = !π (S u)`), and suppose exactly `W` moves of the run are `π`-visible.  Then the cargo
of every `π`-visible move (position `i`, wire `w`, destination `f₀`) lies in the span of the items
whose home class `!π (S u)` is the destination class `π f₀`. -/
theorem cargo_rule_coarse [DecidableEq F] (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) = W)
    (i : ℕ) (hi : i < evs.length) (w : Fin W) (f₀ : F) (hmove : evs[i] = .move w f₀)
    (hvis : π (((init S).run (evs.take i)).frame w) ≠ π f₀) :
    ((init S).run (evs.take i)).vec w ∈ targetI (fun u => !π (S u)) (π f₀) := by
  have hrun : ∀ l : List (Event W F),
      (init (fun u => π (S u))).run (l.map (Event.map π)) = ((init S).run l).map π :=
    fun l => run_map π l (init S)
  have hi' : i < (evs.map (Event.map π)).length := by rw [List.length_map]; exact hi
  have hmove' : (evs.map (Event.map π))[i] = .move w (π f₀) := by
    rw [List.getElem_map, hmove]; rfl
  have htake : (evs.map (Event.map π)).take i = (evs.take i).map (Event.map π) :=
    List.map_take.symm
  have h := cargo_rule_getElem (fun u => π (S u)) (fun u => !π (S u))
    (fun u => by cases π (S u) <;> decide)
    (fun u f h => by cases f <;> cases hS : π (S u) <;> simp_all)
    ρ (evs.map (Event.map π)) (allValid_map π evs _ hv)
    (fun u => by rw [hrun]; show π (((init S).run evs).frame (ρ u)) = _; rw [hframe, hπ])
    (fun u => by rw [hrun]; exact hvec u)
    hW i hi' w (π f₀) hmove' (by rw [htake, hrun]; exact hvis)
  rw [htake, hrun] at h
  exact h

/-- **Item itineraries, admissibility at one functional.** Let `π : F → Bool` separate
every source from its target (`π (tgt u) = !π (S u)`) and suppose exactly `W` moves of the run
are `π`-visible (the coarsening is *tight*).  Then every `π`-visible hop of any item `s` starts
on the birth side of `s`: for a move `.move w f₀` at position `i` whose cargo has
`s`-coordinate `1` and whose origin and destination have different `π`-classes,
`π (origin) = π (S s)` (equivalently `π f₀ = π (tgt s)`). -/
theorem itinerary_condition [DecidableEq F] (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) = W)
    (i : ℕ) (hi : i < evs.length) (w : Fin W) (f₀ : F) (hmove : evs[i] = .move w f₀)
    (s : Fin W) (hs : ((init S).run (evs.take i)).vec w s = 1)
    (hvis : π (((init S).run (evs.take i)).frame w) ≠ π f₀) :
    π (((init S).run (evs.take i)).frame w) = π (S s) := by
  have hmem := cargo_rule_coarse S tgt ρ evs hv hframe hvec π hπ hW i hi w f₀ hmove hvis
  have h1 : (!π (S s)) = π f₀ := eq_of_mem_targetI_of_apply_eq_one hmem hs
  rw [← h1] at hvis
  revert hvis
  cases π (((init S).run (evs.take i)).frame w) <;> cases π (S s) <;> decide

/-- The same, with the tightness hypothesis `≤ W` (equivalent, by `visible_ge_W_of_coarse`). -/
theorem itinerary_condition_of_le [DecidableEq F] (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) ≤ W)
    (i : ℕ) (hi : i < evs.length) (w : Fin W) (f₀ : F) (hmove : evs[i] = .move w f₀)
    (s : Fin W) (hs : ((init S).run (evs.take i)).vec w s = 1)
    (hvis : π (((init S).run (evs.take i)).frame w) ≠ π f₀) :
    π (((init S).run (evs.take i)).frame w) = π (S s) :=
  itinerary_condition S tgt ρ evs hv hframe hvec π hπ
    (le_antisymm hW (visible_ge_W_of_coarse S tgt ρ evs hv hframe hvec π
      (fun u => by rw [hπ]; cases π (S u) <;> decide)))
    i hi w f₀ hmove s hs hvis

/-- **Item itineraries, combined form.** Under a tight two-class coarsening `π`,
every item `s` has a chain of frame-changing hops from `S s` to `tgt s` along the run, and every
`π`-visible hop of that chain starts on the birth side of `s` (so the partial displacement
`S s + f_{j-1}` is `π`-invisible at every `π`-visible hop `j`). -/
theorem chain_itinerary [DecidableEq F] (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) = W) (s : Fin W) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (tgt s) is ∧ Visible (init S) evs is ∧
      ∀ i ∈ is, ∀ (w : Fin W) (f₀ : F), evs[i]? = some (.move w f₀) →
        π (((init S).run (evs.take i)).frame w) ≠ π f₀ →
        π (((init S).run (evs.take i)).frame w) = π (S s) := by
  obtain ⟨is, hc, hvis⟩ := chain_exists_visible S tgt ρ evs hv hframe hvec s
  refine ⟨is, hc, hvis, ?_⟩
  intro i hi w f₀ hmove hvis
  obtain ⟨w', f₁, hw', hs'⟩ := hc.carries_of_mem hi
  rw [hmove] at hw'
  obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw')
  obtain ⟨hlen, hget⟩ := List.getElem?_eq_some_iff.mp hmove
  exact itinerary_condition S tgt ρ evs hv hframe hvec π hπ hW i hlen w f₀ hget s hs' hvis

/-! ### Visible moves of a coarsened run, as a count over the jumps -/

/-- The number of `π`-visible moves is the number of jumps `(f, f')` of the run with
`π f ≠ π f'`. -/
theorem vmoves_map_eq_countP [DecidableEq F] {F' : Type} [DecidableEq F'] (π : F → F') :
    ∀ (evs : List (Event W F)) (c : Cfg W F),
      vmoves (evs.map (Event.map π)) (c.map π) =
        (jumps evs c).countP (fun p => decide (π p.1 ≠ π p.2))
  | [], _ => rfl
  | .gate i j :: evs, c => by
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.gate i j)) =
        (jumps evs (c.step (.gate i j))).countP _
      rw [step_map_gate]
      exact vmoves_map_eq_countP π evs _
  | .move w f :: evs, c => by
      show vmoves (evs.map (Event.map π)) ((c.map π).step (.move w (π f))) +
          (if (c.map π).frame w = π f then 0 else 1) =
        ((c.frame w, f) :: jumps evs (c.step (.move w f))).countP _
      rw [step_map_move, List.countP_cons, vmoves_map_eq_countP π evs _]
      show _ + (if π (c.frame w) = π f then 0 else 1) = _
      by_cases h : π (c.frame w) = π f <;> simp [h]

/-! ### The matrix instance: `F₂^{m×m}` frames, targets `S u + 1`, coarsenings `⟪Λ, ·⟫` -/

section MatrixInstance

variable {m : ℕ}

/-- The pairing `⟪Λ, M⟫ = Σ_{i,j} Λ i j * M i j` of two `m × m` matrices over `F₂`. -/
def pairing (Λ M : Matrix (Fin m) (Fin m) (ZMod 2)) : ZMod 2 := ∑ i, ∑ j, Λ i j * M i j

/-- The two-class coarsening `M ↦ [⟪Λ, M⟫ = 1]` defined by a functional `Λ`. -/
def classOf (Λ M : Matrix (Fin m) (Fin m) (ZMod 2)) : Bool := decide (pairing Λ M = 1)

theorem pairing_add (Λ A B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    pairing Λ (A + B) = pairing Λ A + pairing Λ B := by
  simp [pairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairing_one (Λ : Matrix (Fin m) (Fin m) (ZMod 2)) : pairing Λ 1 = Λ.trace := by
  simp [pairing, Matrix.one_apply, Matrix.trace, Matrix.diag]

/-- A trace-one functional separates every frame from its shift by `1`. -/
theorem classOf_add_one (Λ : Matrix (Fin m) (Fin m) (ZMod 2)) (hΛ : Λ.trace = 1)
    (M : Matrix (Fin m) (Fin m) (ZMod 2)) : classOf Λ (M + 1) = !classOf Λ M := by
  unfold classOf
  rw [pairing_add, pairing_one, hΛ]
  generalize pairing Λ M = a
  revert a; decide

/-- A jump `A → B` is `Λ`-visible iff `⟪Λ, B - A⟫ = 1`. -/
theorem classOf_ne_iff (Λ A B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    classOf Λ A ≠ classOf Λ B ↔ pairing Λ (B - A) = 1 := by
  have hB : pairing Λ B = pairing Λ A + pairing Λ (B - A) := by rw [← pairing_add, add_sub_cancel]
  unfold classOf
  rw [hB]
  generalize pairing Λ A = a
  generalize pairing Λ (B - A) = b
  revert a b; decide

/-- Two frames have the same `Λ`-class iff `⟪Λ, A + B⟫ = 0`. -/
theorem classOf_eq_iff (Λ A B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    classOf Λ A = classOf Λ B ↔ pairing Λ (A + B) = 0 := by
  unfold classOf
  rw [pairing_add]
  generalize pairing Λ A = a
  generalize pairing Λ B = b
  revert a b; decide

/-- `Λ` is tight (exactly `W` jumps `J` with `⟪Λ, J⟫ = 1`) iff the coarsened run has exactly `W`
visible moves. -/
theorem tight_iff_vmoves (S : Fin W → Matrix (Fin m) (Fin m) (ZMod 2))
    (evs : List (Event W (Matrix (Fin m) (Fin m) (ZMod 2)))) (Λ : Matrix (Fin m) (Fin m) (ZMod 2)) :
    (jumps evs (init S)).countP (fun p => decide (pairing Λ (p.2 - p.1) = 1)) = W ↔
      vmoves (evs.map (Event.map (classOf Λ))) ((init S).map (classOf Λ)) = W := by
  rw [vmoves_map_eq_countP]
  refine Iff.of_eq (congrArg (· = W) ?_)
  apply List.countP_congr
  intro p _
  simp only [decide_eq_true_eq]
  exact (classOf_ne_iff Λ p.1 p.2).symm

/-- **Item itineraries, matrix instance.** Frames in `F₂^{m×m}`, targets `S u + 1`.  Let `Λ` be a
trace-one functional that is *tight* for the run: exactly `W` of its jumps `J` have `⟪Λ, J⟫ = 1`.
Then at every hop of an item `s` — a move `.move w f₁` at position `i` of the run whose cargo has
`s`-coordinate `1` — with jump `J = f₁ - f₀` (`f₀` the origin frame) such that `⟪Λ, J⟫ = 1`, the
partial displacement satisfies `⟪Λ, S s + f₀⟫ = 0`. -/
theorem itinerary_condition_matrix (S : Fin W → Matrix (Fin m) (Fin m) (ZMod 2))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin m) (Fin m) (ZMod 2))))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (Λ : Matrix (Fin m) (Fin m) (ZMod 2)) (hΛ : Λ.trace = 1)
    (htight : (jumps evs (init S)).countP (fun p => decide (pairing Λ (p.2 - p.1) = 1)) = W)
    (i : ℕ) (hi : i < evs.length) (w : Fin W) (f₁ : Matrix (Fin m) (Fin m) (ZMod 2))
    (hmove : evs[i] = .move w f₁)
    (s : Fin W) (hs : ((init S).run (evs.take i)).vec w s = 1)
    (hJ : pairing Λ (f₁ - ((init S).run (evs.take i)).frame w) = 1) :
    pairing Λ (S s + ((init S).run (evs.take i)).frame w) = 0 := by
  have h := itinerary_condition S (fun u => S u + 1) ρ evs hv hframe hvec (classOf Λ)
    (fun u => classOf_add_one Λ hΛ (S u)) ((tight_iff_vmoves S evs Λ).mp htight)
    i hi w f₁ hmove s hs ((classOf_ne_iff Λ _ _).mpr hJ)
  rw [classOf_eq_iff, add_comm] at h
  exact h

/-- The combined form for matrix frames: every item `s` has a chain of frame-changing hops from
`S s` to `S s + 1`, and at every hop (position `i`, move `.move w f₁`, origin `f₀`) and every
tight trace-one `Λ` with `⟪Λ, f₁ - f₀⟫ = 1`, `⟪Λ, S s + f₀⟫ = 0`: the partial displacement
`S s + f₀ = J_1 + ⋯ + J_{j-1}` lies in `Z(J_j)`, the common kernel of the tight functionals
seeing `J_j`. -/
theorem chain_itinerary_matrix (S : Fin W → Matrix (Fin m) (Fin m) (ZMod 2))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin m) (Fin m) (ZMod 2))))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) (s : Fin W) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (S s + 1) is ∧ Visible (init S) evs is ∧
      ∀ i ∈ is, ∀ (w : Fin W) (f₁ : Matrix (Fin m) (Fin m) (ZMod 2)),
        evs[i]? = some (.move w f₁) →
        ∀ Λ : Matrix (Fin m) (Fin m) (ZMod 2), Λ.trace = 1 →
          (jumps evs (init S)).countP (fun p => decide (pairing Λ (p.2 - p.1) = 1)) = W →
          pairing Λ (f₁ - ((init S).run (evs.take i)).frame w) = 1 →
          pairing Λ (S s + ((init S).run (evs.take i)).frame w) = 0 := by
  obtain ⟨is, hc, hvis⟩ := chain_exists_visible S (fun u => S u + 1) ρ evs hv hframe hvec s
  refine ⟨is, hc, hvis, ?_⟩
  intro i hi w f₁ hmove Λ hΛ htight hJ
  obtain ⟨w', f₁', hw', hs'⟩ := hc.carries_of_mem hi
  rw [hmove] at hw'
  obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw')
  obtain ⟨hlen, hget⟩ := List.getElem?_eq_some_iff.mp hmove
  exact itinerary_condition_matrix S ρ evs hv hframe hvec Λ hΛ htight i hlen w f₁ hget s hs' hJ

end MatrixInstance

/-! ### Sanity checks on the two-wire run of `GadgetMixing.lean`

`W = 2`, both wires start at `false`: `gate 0 1` (wire `0` now holds `e 0 + e 1`), `move 0 true`
(carries items `0` and `1`), `move 1 true` (carries item `1`), `gate 0 1` (restores `e 0`).
Chains: item `0` has the chain `[1]`; item `1` has the chains `[1]` and `[2]`; `[1, 2]` is not a
chain of item `1` (the second hop does not start where the first one ends), `[2]` is not a chain of
item `0` (that move does not carry `0`), and the empty list is not a chain from `false` to `true`. -/

deriving instance DecidableEq for Event

instance decidableIsHop [DecidableEq F] [Fintype F] (c : Cfg W F) (evs : List (Event W F))
    (s : Fin W) (i : ℕ) (f₀ f₁ : F) : Decidable (IsHop c evs s i f₀ f₁) := by
  unfold IsHop; infer_instance

instance decidableIsChain [DecidableEq F] [Fintype F] (c : Cfg W F) (evs : List (Event W F))
    (s : Fin W) : ∀ (f₀ fk : F) (is : List ℕ), Decidable (IsChain c evs s f₀ fk is)
  | f₀, fk, [] => show Decidable (f₀ = fk) from inferInstance
  | f₀, fk, i :: is =>
      haveI : ∀ f₁, Decidable (IsChain c evs s f₁ fk is) := fun f₁ => decidableIsChain c evs s f₁ fk is
      show Decidable (∃ f₁, IsHop c evs s i f₀ f₁ ∧ (∀ j ∈ is, i < j) ∧ IsChain c evs s f₁ fk is)
        from inferInstance

/-- The two-wire run. -/
def sanityRun : List (Event 2 Bool) := [.gate 0 1, .move 0 true, .move 1 true, .gate 0 1]

example : IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true [1] := by decide
example : IsChain (init (W := 2) (fun _ => false)) sanityRun 1 false true [1] := by decide
example : IsChain (init (W := 2) (fun _ => false)) sanityRun 1 false true [2] := by decide
example : ¬ IsChain (init (W := 2) (fun _ => false)) sanityRun 1 false true [1, 2] := by decide
example : ¬ IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true [2] := by decide
example : ¬ IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true [] := by decide
example : ¬ IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true [3] := by decide

/-- A no-op move (`move 1 false` while wire `1` is at `false`) carrying item `1` is a hop from
`false` to `false`, but not a visible one. -/
def sanityRun' : List (Event 2 Bool) := [.move 1 false, .move 1 true]

example : IsChain (init (W := 2) (fun _ => false)) sanityRun' 1 false true [0, 1] := by decide
example : ¬ Visible (init (W := 2) (fun _ => false)) sanityRun' [0, 1] := by
  unfold Visible; decide
example : IsChain (init (W := 2) (fun _ => false)) sanityRun' 1 false true [1] ∧
    Visible (init (W := 2) (fun _ => false)) sanityRun' [1] := by
  unfold Visible; decide

/-- The hypotheses of `chain_exists` hold for the two-wire run (with `ρ = 1`, `tgt = !S`), so
each item has a chain; and the coarsening `π = id` on `Bool` is tight (2 visible moves), so
`chain_itinerary` applies as well. -/
example : ∃ is : List ℕ, IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true is :=
  chain_exists (fun _ => false) (fun _ => true) 1 sanityRun (by decide) (by decide) (by decide) 0

example : vmoves (sanityRun.map (Event.map id)) ((init (W := 2) (fun _ => false)).map id) = 2 := by
  decide

example : ∃ is : List ℕ, IsChain (init (W := 2) (fun _ => false)) sanityRun 1 false true is ∧
    Visible (init (W := 2) (fun _ => false)) sanityRun is ∧
    ∀ i ∈ is, ∀ (w : Fin 2) (f₀ : Bool), sanityRun[i]? = some (.move w f₀) →
      id (((init (W := 2) (fun _ => false)).run (sanityRun.take i)).frame w) ≠ id f₀ →
      id (((init (W := 2) (fun _ => false)).run (sanityRun.take i)).frame w) = id false :=
  chain_itinerary (fun _ => false) (fun _ => true) 1 sanityRun (by decide) (by decide) (by decide)
    id (by decide) (by decide) 1

end Transpose.ShearFrame
