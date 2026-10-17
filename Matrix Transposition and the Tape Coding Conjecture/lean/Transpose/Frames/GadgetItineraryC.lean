import Transpose.Frames.GadgetItinerary

/-!
# Every carrying move lies on a chain of its item; condition (C) at one functional

`GadgetItinerary.lean` proves *existence* of a chain of every item (item itineraries).  Walking
from a carrying move backwards to the source of its item (`chain_of_present`) and forwards to the
target (`chain_to_present`) shows more — **every** move carrying an item lies on a chain of that
item from its source to its target.  Hence **condition (C)**: under a tight two-class coarsening
every visible move of the run lies on an admissible itinerary of some item (every move carries a
nonzero vector, hence some item: `exists_vec_eq_one`, from the linear independence of the wire
vectors, `linearIndependent_vec_init_run`).

Setting as in `GadgetItinerary.lean`: a valid run `evs` from `init S` ending with wire `ρ u` at
frame `tgt u` holding `e u`; hops `IsHop`, chains `IsChain`, visibility `Visible`.

* Position bookkeeping: hops/chains/visibility of a prefix `evs.take n` are hops/chains/visibility
  of `evs` at the same positions (`IsHop.of_take`, `IsChain.of_take`, `Visible.of_take`); those of a
  suffix `evs.drop n` (run from `c.run (evs.take n)`) are those of `evs` at positions shifted by `n`
  (`IsHop.of_drop`, `IsChain.of_drop`, `Visible.of_drop`); chains concatenate (`IsChain.append`).
* `chain_to_present` (the forward dual of `chain_of_present`): if `s` is present at `f` before a
  valid segment, then after the segment `s` is present at some `f'` reached from `f` by a chain of
  visible hops of `s` along the segment.
* `carrying_move_on_chain_split` / **`carrying_move_on_chain`**: every frame-changing
  move at position `i` whose cargo has `s`-coordinate `1` lies on a chain of visible hops of `s`
  from `S s` to `tgt s`; `carrying_move_on_some_chain` is the version without the frame-changing
  hypothesis (the chain then need not be visible at `i`).
* `chain_admissible`: under a tight two-class coarsening every `π`-visible hop of every chain of `s`
  starts on the birth side of `s` (the per-chain form of `itinerary_condition`).
* **`carrying_move_on_admissible_chain`** (condition (C) at one functional): under the tightness
  hypotheses of `itinerary_condition`, every visible carrying move lies on a visible chain of its
  item all of whose `π`-visible hops start on the item's birth side;
  **`carrying_move_on_admissible_chain_matrix`**: the matrix instance (frames `F₂^{m×m}`, targets
  `S u + 1`): every frame-changing move at position `i` carrying `s` lies on a chain of `s` from
  `S s` to `S s + 1` such that at every hop with jump `J` and every tight trace-one `Λ` seeing `J`,
  `⟪Λ, S s + origin⟫ = 0`.
* `exists_vec_eq_one`: every wire vector along the run has some coordinate `1`, so every move
  carries some item; **`visible_move_on_admissible_chain`** (condition (C) for every visible move):
  under a tight `π`, every frame-changing move of the run lies on a visible chain of *some* item
  all of whose `π`-visible hops start on that item's birth side.
* Bookkeeping (an itinerary is a sub-multiset of the run's jumps): `hopJump c evs i`
  is the (origin, destination) pair of the move at position `i`; the hop pairs of any chain,
  `is.filterMap (hopJump c evs)`, form a sublist (`IsChain.hopJumps_sublist`), hence a sub-multiset
  (`IsChain.hopJumps_le`), of `jumps evs c`; they form a path from `f₀` to `fk` (`IsChain.isPath`),
  so in the matrix instance the jump matrices of a chain from `S s` to `S s + 1` sum to `1`
  (`IsChain.sum_jumps_matrix`).
-/

namespace Transpose.ShearFrame

variable {W : ℕ} {F : Type}

/-! ### Position bookkeeping: prefixes, suffixes, concatenation -/

/-- A position of a chain of hops along `evs.take n` is below `n`. -/
theorem IsChain.lt_of_take {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {n : ℕ} {f₀ fk : F}
    {is : List ℕ} (hc : IsChain c (evs.take n) s f₀ fk is) : ∀ j ∈ is, j < n := by
  intro j hj
  obtain ⟨_, _, _, hw, _, _⟩ := hc.hop_of_mem j hj
  obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hw
  rw [List.length_take] at hlen
  exact lt_of_lt_of_le hlen (min_le_left _ _)

/-- A position of a chain of hops along `evs` is below the length of `evs`. -/
theorem IsChain.lt_length {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {f₀ fk : F}
    {is : List ℕ} (hc : IsChain c evs s f₀ fk is) : ∀ j ∈ is, j < evs.length := by
  intro j hj
  obtain ⟨_, _, _, hw, _, _⟩ := hc.hop_of_mem j hj
  exact (List.getElem?_eq_some_iff.mp hw).1

/-- A hop along the prefix `evs.take n` is a hop along `evs` at the same position. -/
theorem IsHop.of_take {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {n i : ℕ} {f₀ f₁ : F}
    (h : IsHop c (evs.take n) s i f₀ f₁) : IsHop c evs s i f₀ f₁ := by
  obtain ⟨w, hw, hf, hs⟩ := h
  have hin : i < n := by
    obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hw
    rw [List.length_take] at hlen
    exact lt_of_lt_of_le hlen (min_le_left _ _)
  rw [List.getElem?_take_of_lt hin] at hw
  rw [List.take_take, min_eq_left hin.le] at hf hs
  exact ⟨w, hw, hf, hs⟩

/-- A chain along the prefix `evs.take n` is a chain along `evs` at the same positions. -/
theorem IsChain.of_take {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {n : ℕ} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain c (evs.take n) s f₀ fk is → IsChain c evs s f₀ fk is
  | _, _, [], h => h
  | _, _, _ :: _, ⟨f₁, hhop, hlt, hc⟩ => ⟨f₁, hhop.of_take, hlt, hc.of_take⟩

/-- Visibility along the prefix `evs.take n` is visibility along `evs`, at positions below `n`. -/
theorem Visible.of_take {c : Cfg W F} {evs : List (Event W F)} {n : ℕ} {is : List ℕ}
    (hb : ∀ i ∈ is, i < n) (h : Visible c (evs.take n) is) : Visible c evs is := by
  intro i hi w f₁ hw
  have hin := hb i hi
  have h' := h i hi w f₁ (by rw [List.getElem?_take_of_lt hin]; exact hw)
  rwa [List.take_take, min_eq_left hin.le] at h'

/-- A hop along the suffix `evs.drop n` (run from the configuration after `evs.take n`) is a hop
along `evs` at the position shifted by `n`. -/
theorem IsHop.of_drop {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {n j : ℕ} {f₀ f₁ : F}
    (h : IsHop (c.run (evs.take n)) (evs.drop n) s j f₀ f₁) : IsHop c evs s (n + j) f₀ f₁ := by
  obtain ⟨w, hw, hf, hs⟩ := h
  rw [List.getElem?_drop] at hw
  rw [← run_append, ← List.take_add] at hf hs
  exact ⟨w, hw, hf, hs⟩

/-- A chain along the suffix `evs.drop n` is a chain along `evs` at the positions shifted by `n`. -/
theorem IsChain.of_drop {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {n : ℕ} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain (c.run (evs.take n)) (evs.drop n) s f₀ fk is →
      IsChain c evs s f₀ fk (is.map (n + ·))
  | _, _, [], h => h
  | _, _, _ :: _, ⟨f₁, hhop, hlt, hc⟩ => by
      refine ⟨f₁, hhop.of_drop, ?_, hc.of_drop⟩
      intro j hj
      obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj
      exact Nat.add_lt_add_left (hlt j' hj') n

/-- Visibility along the suffix `evs.drop n` is visibility along `evs` at the shifted positions. -/
theorem Visible.of_drop {c : Cfg W F} {evs : List (Event W F)} {n : ℕ} {is : List ℕ}
    (h : Visible (c.run (evs.take n)) (evs.drop n) is) : Visible c evs (is.map (n + ·)) := by
  intro i hi w f₁ hw
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  rw [← List.getElem?_drop] at hw
  have h' := h j hj w f₁ hw
  rwa [← run_append, ← List.take_add] at h'

/-- Two chains of `s` concatenate when the first ends where the second starts and all positions of
the first precede all positions of the second. -/
theorem IsChain.append {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {f₂ : F} {is₂ : List ℕ} :
    ∀ {f₀ f₁ : F} {is₁ : List ℕ}, IsChain c evs s f₀ f₁ is₁ → IsChain c evs s f₁ f₂ is₂ →
      (∀ a ∈ is₁, ∀ b ∈ is₂, a < b) → IsChain c evs s f₀ f₂ (is₁ ++ is₂)
  | _, _, [], h₁, h₂, _ => by
      have h₁' : _ = _ := h₁
      subst h₁'
      exact h₂
  | _, _, i :: is₁, ⟨g, hhop, hlt, hc⟩, h₂, hlt' => by
      refine ⟨g, hhop, ?_, hc.append h₂ (fun a ha b hb => hlt' a (List.mem_cons_of_mem i ha) b hb)⟩
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hlt j hj
      · exact hlt' i List.mem_cons_self j hj

theorem Visible.append {c : Cfg W F} {evs : List (Event W F)} {is₁ is₂ : List ℕ}
    (h₁ : Visible c evs is₁) (h₂ : Visible c evs is₂) : Visible c evs (is₁ ++ is₂) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h₁ i hi
  · exact h₂ i hi

/-! ### The forward dual of `chain_of_present`: presence propagates along chains -/

/-- If `s` is present at `f` before a valid segment, then after the segment `s` is present at some
`f'` and there is a chain of visible hops of `s` from `f` to `f'` along the segment.  (Presence at
`f` can only end through a move out of `f` carrying `s`, which is a hop from `f`.) -/
theorem chain_to_present (s : Fin W) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs → ∀ f, c.present s f →
      ∃ f' is, (c.run evs).present s f' ∧ IsChain c evs s f f' is ∧ Visible c evs is
  | [], c, _, f, h => ⟨f, [], h, rfl, fun _ h => (List.not_mem_nil h).elim⟩
  | .gate i j :: evs, c, hv, f, h => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      obtain ⟨f', is, hf', hc, hvis⟩ := chain_to_present s evs (c.step (.gate i j)) hv' f
        ((present_gate c hij hf s f).mpr h)
      exact ⟨f', is.map (· + 1), hf', hc.succ, hvis.succ⟩
  | .move w f₁ :: evs, c, hv, f, h => by
      obtain ⟨_, hv'⟩ := hv
      by_cases hs : c.vec w s = 1
      · by_cases hw : c.frame w = f
        · -- the moved wire sits at `f` and carries `s`: after the move `s` is present at `f₁`
          obtain ⟨f', is, hf', hc, hvis⟩ := chain_to_present s evs (c.step (.move w f₁)) hv' f₁
            (present_move_dest c w f₁ hs)
          by_cases hf1 : f = f₁
          · -- an invisible move: `s` stays present at `f = f₁`
            subst hf1
            exact ⟨f', is.map (· + 1), hf', hc.succ, hvis.succ⟩
          · -- a visible move: it is the first hop of the chain
            refine ⟨f', 0 :: is.map (· + 1), hf', ⟨f₁, ⟨w, rfl, hw, hs⟩, ?_, hc.succ⟩, ?_⟩
            · intro j hj
              obtain ⟨j', _, rfl⟩ := List.mem_map.mp hj
              exact Nat.succ_pos j'
            · intro j hj w'' f'' hw''
              rcases List.mem_cons.mp hj with rfl | hj
              · obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw'')
                show c.frame w ≠ f₁
                rw [hw]; exact hf1
              · exact hvis.succ j hj w'' f'' hw''
        · -- the moved wire is not at `f`: presence at `f` survives
          obtain ⟨f', is, hf', hc, hvis⟩ := chain_to_present s evs (c.step (.move w f₁)) hv' f
            (present_move_of_ne_origin c w f₁ s hw h)
          exact ⟨f', is.map (· + 1), hf', hc.succ, hvis.succ⟩
      · obtain ⟨f', is, hf', hc, hvis⟩ := chain_to_present s evs (c.step (.move w f₁)) hv' f
          ((present_move_of_ne_one c w f₁ hs f).mpr h)
        exact ⟨f', is.map (· + 1), hf', hc.succ, hvis.succ⟩

/-! ### Every carrying move lies on a chain of its item -/

/-- **Every carrying move lies on a chain, split form.** In a valid run from `init S` ending with
wire `ρ u` at frame `tgt u` holding `e u`, let the event at position `i` be a move `.move w f₁`
whose cargo (the vector of `w` just before it) has `s`-coordinate `1`.  Then there are positions
`is₁` (all `< i`) and `is₂` (all `> i`) such that `is₁ ++ i :: is₂` is a chain of `s` from `S s`
to `tgt s` along the run, and all hops at `is₁` and at `is₂` change the frame. -/
theorem carrying_move_on_chain_split (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (s : Fin W) (i : ℕ) (w : Fin W) (f₁ : F) (hmove : evs[i]? = some (.move w f₁))
    (hs : ((init S).run (evs.take i)).vec w s = 1) :
    ∃ is₁ is₂ : List ℕ, IsChain (init S) evs s (S s) (tgt s) (is₁ ++ i :: is₂) ∧
      Visible (init S) evs is₁ ∧ Visible (init S) evs is₂ ∧
      (∀ j ∈ is₁, j < i) ∧ (∀ j ∈ is₂, i < j) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hmove
  -- the run splits as `evs.take i ++ .move w f₁ :: evs.drop (i + 1)`
  have hsplit : evs = evs.take i ++ evs.drop i := (List.take_append_drop i evs).symm
  have hdrop : evs.drop i = .move w f₁ :: evs.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, hget]
  have hv' := (allValid_append _ _ _).mp (hsplit ▸ hv)
  have hv₁ : (init S).allValid (evs.take i) := hv'.1
  have hv₂ : (((init S).run (evs.take i)).step (.move w f₁)).allValid (evs.drop (i + 1)) := by
    have h := hv'.2
    rw [hdrop] at h
    exact h.2
  have htake1 : evs.take (i + 1) = evs.take i ++ [.move w f₁] := by
    rw [List.take_add_one, hmove]; rfl
  have hc₂ : (init S).run (evs.take (i + 1)) = ((init S).run (evs.take i)).step (.move w f₁) := by
    rw [htake1, run_append]; rfl
  have hend : (((init S).run (evs.take i)).step (.move w f₁)).run (evs.drop (i + 1)) =
      (init S).run evs := by
    rw [← hc₂, ← run_append, List.take_append_drop]
  -- backward: `s` is present at the origin just before the move, hence reached it from `S s`
  obtain ⟨f', is₁, hf', hc₁, hvis₁⟩ := chain_of_present s (evs.take i) (init S) hv₁
    (((init S).run (evs.take i)).frame w) ⟨w, rfl, hs⟩
  obtain rfl := (present_init S s f').mp hf'
  have hb₁ : ∀ j ∈ is₁, j < i := hc₁.lt_of_take
  -- forward: `s` is present at `f₁` just after the move, hence reaches `tgt s` from there
  obtain ⟨f'', is₂, hf'', hc₂', hvis₂⟩ := chain_to_present s (evs.drop (i + 1))
    (((init S).run (evs.take i)).step (.move w f₁)) hv₂ f₁
    (present_move_dest ((init S).run (evs.take i)) w f₁ hs)
  rw [hend] at hf''
  obtain rfl := (present_final _ tgt ρ hframe hvec s f'').mp hf''
  rw [← hc₂] at hc₂' hvis₂
  have hb₂ : ∀ j ∈ is₂.map (i + 1 + ·), i < j := by
    intro j hj
    obtain ⟨j', _, rfl⟩ := List.mem_map.mp hj
    omega
  refine ⟨is₁, is₂.map (i + 1 + ·), ?_, hvis₁.of_take hb₁, hvis₂.of_drop, hb₁, hb₂⟩
  refine hc₁.of_take.append ⟨f₁, ⟨w, hmove, rfl, hs⟩, hb₂, hc₂'.of_drop⟩ ?_
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hb₁ a ha
  · exact (hb₁ a ha).trans (hb₂ b hb)

/-- **Every carrying move lies on a chain of its item.** In a valid run from `init S`
ending with wire `ρ u` at frame `tgt u` holding `e u`, every frame-changing move at position `i`
whose cargo has `s`-coordinate `1` lies on a chain of frame-changing hops of `s` from `S s` to
`tgt s` along the run. -/
theorem carrying_move_on_chain (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (s : Fin W) (i : ℕ) (w : Fin W) (f₁ : F) (hmove : evs[i]? = some (.move w f₁))
    (hs : ((init S).run (evs.take i)).vec w s = 1)
    (hne : ((init S).run (evs.take i)).frame w ≠ f₁) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (tgt s) is ∧ Visible (init S) evs is ∧ i ∈ is := by
  obtain ⟨is₁, is₂, hc, hvis₁, hvis₂, _, _⟩ :=
    carrying_move_on_chain_split S tgt ρ evs hv hframe hvec s i w f₁ hmove hs
  refine ⟨is₁ ++ i :: is₂, hc, hvis₁.append ?_, List.mem_append_right _ List.mem_cons_self⟩
  intro j hj w' f₁' hw'
  rcases List.mem_cons.mp hj with rfl | hj
  · rw [hmove] at hw'
    obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw')
    exact hne
  · exact hvis₂ j hj w' f₁' hw'

/-- Without the frame-changing hypothesis: every move carrying `s` (visible or not) lies on some
chain of `s` from `S s` to `tgt s`. -/
theorem carrying_move_on_some_chain (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (s : Fin W) (i : ℕ) (w : Fin W) (f₁ : F) (hmove : evs[i]? = some (.move w f₁))
    (hs : ((init S).run (evs.take i)).vec w s = 1) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (tgt s) is ∧ i ∈ is :=
  let ⟨is₁, is₂, hc, _, _, _, _⟩ :=
    carrying_move_on_chain_split S tgt ρ evs hv hframe hvec s i w f₁ hmove hs
  ⟨is₁ ++ i :: is₂, hc, List.mem_append_right _ List.mem_cons_self⟩

/-! ### Condition (C) at one functional -/

/-- Under a tight two-class coarsening `π`, every `π`-visible hop of **any** chain of `s` starts
on the birth side of `s` (`itinerary_condition`, applied hop by hop). -/
theorem chain_admissible [DecidableEq F] (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) = W) (s : Fin W) {f₀ fk : F}
    {is : List ℕ} (hc : IsChain (init S) evs s f₀ fk is) :
    ∀ i ∈ is, ∀ (w : Fin W) (f₁ : F), evs[i]? = some (.move w f₁) →
      π (((init S).run (evs.take i)).frame w) ≠ π f₁ →
      π (((init S).run (evs.take i)).frame w) = π (S s) := by
  intro i hi w f₁ hmove hvis
  obtain ⟨w', f₁', hw', hs'⟩ := hc.carries_of_mem hi
  rw [hmove] at hw'
  obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw')
  obtain ⟨hlen, hget⟩ := List.getElem?_eq_some_iff.mp hmove
  exact itinerary_condition S tgt ρ evs hv hframe hvec π hπ hW i hlen w f₁ hget s hs' hvis

/-- **Condition (C) at one functional.** Let `π : F → Bool` separate every source from its target
(`π (tgt u) = !π (S u)`) and be tight (exactly `W` moves of the run are `π`-visible).  Then every
frame-changing move at position `i` whose cargo has `s`-coordinate `1` lies on a chain of
frame-changing hops of `s` from `S s` to `tgt s` all of whose `π`-visible hops start on the birth
side of `s`. -/
theorem carrying_move_on_admissible_chain [DecidableEq F] (S tgt : Fin W → F)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) = W)
    (s : Fin W) (i : ℕ) (w : Fin W) (f₁ : F) (hmove : evs[i]? = some (.move w f₁))
    (hs : ((init S).run (evs.take i)).vec w s = 1)
    (hne : ((init S).run (evs.take i)).frame w ≠ f₁) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (tgt s) is ∧ Visible (init S) evs is ∧ i ∈ is ∧
      ∀ j ∈ is, ∀ (w' : Fin W) (f₀ : F), evs[j]? = some (.move w' f₀) →
        π (((init S).run (evs.take j)).frame w') ≠ π f₀ →
        π (((init S).run (evs.take j)).frame w') = π (S s) :=
  let ⟨is, hc, hvis, hi⟩ :=
    carrying_move_on_chain S tgt ρ evs hv hframe hvec s i w f₁ hmove hs hne
  ⟨is, hc, hvis, hi, chain_admissible S tgt ρ evs hv hframe hvec π hπ hW s hc⟩

section MatrixInstance

variable {m : ℕ}

/-- **Condition (C), matrix instance** (frames in `F₂^{m×m}`, targets `S u + 1`).  Every
frame-changing move at position `i` carrying `s` lies on a chain of frame-changing hops of `s`
from `S s` to `S s + 1` such that at every hop (position `j`, move `.move w' f₀`, origin
`g₀ = ((init S).run (evs.take j)).frame w'`, jump `J = f₀ - g₀`) and every tight trace-one `Λ`
with `⟪Λ, J⟫ = 1`, the partial displacement satisfies `⟪Λ, S s + g₀⟫ = 0`. -/
theorem carrying_move_on_admissible_chain_matrix (S : Fin W → Matrix (Fin m) (Fin m) (ZMod 2))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin m) (Fin m) (ZMod 2))))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (s : Fin W) (i : ℕ) (w : Fin W) (f₁ : Matrix (Fin m) (Fin m) (ZMod 2))
    (hmove : evs[i]? = some (.move w f₁))
    (hs : ((init S).run (evs.take i)).vec w s = 1)
    (hne : ((init S).run (evs.take i)).frame w ≠ f₁) :
    ∃ is : List ℕ, IsChain (init S) evs s (S s) (S s + 1) is ∧ Visible (init S) evs is ∧ i ∈ is ∧
      ∀ j ∈ is, ∀ (w' : Fin W) (f₀ : Matrix (Fin m) (Fin m) (ZMod 2)),
        evs[j]? = some (.move w' f₀) →
        ∀ Λ : Matrix (Fin m) (Fin m) (ZMod 2), Λ.trace = 1 →
          (jumps evs (init S)).countP (fun p => decide (pairing Λ (p.2 - p.1) = 1)) = W →
          pairing Λ (f₀ - ((init S).run (evs.take j)).frame w') = 1 →
          pairing Λ (S s + ((init S).run (evs.take j)).frame w') = 0 := by
  obtain ⟨is, hc, hvis, hi⟩ :=
    carrying_move_on_chain S (fun u => S u + 1) ρ evs hv hframe hvec s i w f₁ hmove hs hne
  refine ⟨is, hc, hvis, hi, ?_⟩
  intro j hj w' f₀ hmove' Λ hΛ htight hJ
  obtain ⟨w'', f₀', hw', hs'⟩ := hc.carries_of_mem hj
  rw [hmove'] at hw'
  obtain ⟨rfl, rfl⟩ := Event.move.inj (Option.some.inj hw')
  obtain ⟨hlen, hget⟩ := List.getElem?_eq_some_iff.mp hmove'
  exact itinerary_condition_matrix S ρ evs hv hframe hvec Λ hΛ htight j hlen w' f₀ hget s hs' hJ

end MatrixInstance

/-! ### Every move carries some item: condition (C) for every visible move of the run -/

/-- Along a valid run from `init S` every wire vector has some coordinate `1` (the vectors stay
linearly independent, `linearIndependent_vec_init_run`, hence are nonzero).  In particular every
move carries some item. -/
theorem exists_vec_eq_one (S : Fin W → F) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (i : ℕ) (w : Fin W) : ∃ s, ((init S).run (evs.take i)).vec w s = 1 := by
  have hv₁ : (init S).allValid (evs.take i) :=
    ((allValid_append _ _ _).mp ((List.take_append_drop i evs).symm ▸ hv)).1
  have hne : ((init S).run (evs.take i)).vec w ≠ 0 :=
    (linearIndependent_vec_init_run S (evs.take i) hv₁).ne_zero w
  by_contra h
  apply hne
  funext s
  exact zmod2_eq_zero_of_ne_one fun hs => h ⟨s, hs⟩

/-- **Condition (C) for every visible move.** Under a tight two-class coarsening `π`, every
frame-changing move of the run lies on a visible chain of some item `s` from `S s` to `tgt s`
all of whose `π`-visible hops start on the birth side of `s`. -/
theorem visible_move_on_admissible_chain [DecidableEq F] (S tgt : Fin W → F)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (π : F → Bool) (hπ : ∀ u, π (tgt u) = !π (S u))
    (hW : vmoves (evs.map (Event.map π)) ((init S).map π) = W)
    (i : ℕ) (w : Fin W) (f₁ : F) (hmove : evs[i]? = some (.move w f₁))
    (hne : ((init S).run (evs.take i)).frame w ≠ f₁) :
    ∃ (s : Fin W) (is : List ℕ), IsChain (init S) evs s (S s) (tgt s) is ∧
      Visible (init S) evs is ∧ i ∈ is ∧
      ∀ j ∈ is, ∀ (w' : Fin W) (f₀ : F), evs[j]? = some (.move w' f₀) →
        π (((init S).run (evs.take j)).frame w') ≠ π f₀ →
        π (((init S).run (evs.take j)).frame w') = π (S s) :=
  let ⟨s, hs⟩ := exists_vec_eq_one S evs hv i w
  ⟨s, carrying_move_on_admissible_chain S tgt ρ evs hv hframe hvec π hπ hW s i w f₁ hmove hs hne⟩

/-! ### Bookkeeping: the hop pairs of a chain form a sub-multiset of the jumps of the run -/

/-- The jump (origin, destination) of the event at position `i` of `evs` (run from `c`), if that
event is a move. -/
def hopJump (c : Cfg W F) (evs : List (Event W F)) (i : ℕ) : Option (F × F) :=
  match evs[i]? with
  | some (.move w f₁) => some ((c.run (evs.take i)).frame w, f₁)
  | _ => none

theorem hopJump_succ (c : Cfg W F) (ev : Event W F) (evs : List (Event W F)) (i : ℕ) :
    hopJump c (ev :: evs) (i + 1) = hopJump (c.step ev) evs i := by
  simp only [hopJump, List.getElem?_cons_succ, List.take_succ_cons]
  rfl

/-- A hop of `s` at position `i` from `f₀` to `f₁` has jump `(f₀, f₁)`. -/
theorem IsHop.hopJump_eq {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {i : ℕ} {f₀ f₁ : F}
    (h : IsHop c evs s i f₀ f₁) : hopJump c evs i = some (f₀, f₁) := by
  obtain ⟨w, hw, hf, _⟩ := h
  simp only [hopJump, hw, hf]

/-- The jumps of a run are the hop jumps at the positions `0, …, length - 1`. -/
theorem jumps_eq_filterMap_range :
    ∀ (evs : List (Event W F)) (c : Cfg W F),
      jumps evs c = (List.range evs.length).filterMap (hopJump c evs)
  | [], _ => rfl
  | ev :: evs, c => by
      have hcomp : hopJump c (ev :: evs) ∘ Nat.succ = hopJump (c.step ev) evs :=
        funext fun i => hopJump_succ c ev evs i
      rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, hcomp,
        ← jumps_eq_filterMap_range evs (c.step ev)]
      cases ev with
      | gate i j => rfl
      | move w f => rfl

/-- A strictly increasing list of numbers below `n` is a sublist of `List.range n`. -/
theorem sublist_range_of_pairwise_lt (is : List ℕ) (n : ℕ) (hp : is.Pairwise (· < ·))
    (hb : ∀ i ∈ is, i < n) : List.Sublist is (List.range n) := by
  have heq : is = (List.range n).filter (fun x => decide (x ∈ is)) := by
    apply List.SortedLT.eq_of_mem_iff hp.sortedLT
      ((List.pairwise_lt_range.filter (fun x => decide (x ∈ is))).sortedLT)
    intro a
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => ⟨hb a h, h⟩, fun h => h.2⟩
  have h := List.filter_sublist (p := fun x => decide (x ∈ is)) (l := List.range n)
  rwa [← heq] at h

/-- The hop pairs of a chain of `s` form a sublist of the jumps of the run (hops are distinct
moves taken in order). -/
theorem IsChain.hopJumps_sublist {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {f₀ fk : F}
    {is : List ℕ} (hc : IsChain c evs s f₀ fk is) :
    List.Sublist (is.filterMap (hopJump c evs)) (jumps evs c) := by
  rw [jumps_eq_filterMap_range]
  exact (sublist_range_of_pairwise_lt is evs.length hc.pairwise hc.lt_length).filterMap _

/-- The hop pairs of a chain form a sub-multiset of the jumps of the run. -/
theorem IsChain.hopJumps_le {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} {f₀ fk : F}
    {is : List ℕ} (hc : IsChain c evs s f₀ fk is) :
    (↑(is.filterMap (hopJump c evs)) : Multiset (F × F)) ≤ ↑(jumps evs c) :=
  Multiset.coe_le.mpr hc.hopJumps_sublist.subperm

/-- `IsPath f₀ fk js`: the pairs `js` form a path from `f₀` to `fk` (each pair starts where the
previous one ends). -/
def IsPath : F → F → List (F × F) → Prop
  | f₀, fk, [] => f₀ = fk
  | f₀, fk, p :: js => p.1 = f₀ ∧ IsPath p.2 fk js

/-- The hop pairs of a chain from `f₀` to `fk` form a path from `f₀` to `fk`. -/
theorem IsChain.isPath {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain c evs s f₀ fk is →
      IsPath f₀ fk (is.filterMap (hopJump c evs))
  | _, _, [], h => h
  | _, _, _ :: _, ⟨f₁, hhop, _, hc⟩ => by
      rw [List.filterMap_cons_some hhop.hopJump_eq]
      exact ⟨rfl, hc.isPath⟩

/-- The length of the hop-pair list of a chain is the number of hops. -/
theorem IsChain.length_hopJumps {c : Cfg W F} {evs : List (Event W F)} {s : Fin W} :
    ∀ {f₀ fk : F} {is : List ℕ}, IsChain c evs s f₀ fk is →
      (is.filterMap (hopJump c evs)).length = is.length
  | _, _, [], _ => rfl
  | _, _, _ :: _, ⟨_, hhop, _, hc⟩ => by
      rw [List.filterMap_cons_some hhop.hopJump_eq, List.length_cons, List.length_cons,
        hc.length_hopJumps]

/-- Along a path the differences `destination - origin` telescope. -/
theorem IsPath.sum_map_sub {G : Type} [AddCommGroup G] :
    ∀ {f₀ fk : G} {js : List (G × G)}, IsPath f₀ fk js →
      (js.map (fun p => p.2 - p.1)).sum = fk - f₀
  | _, _, [], h => by rw [h]; simp
  | _, _, (a, b) :: js, ⟨ha, hp⟩ => by
      rw [List.map_cons, List.sum_cons, hp.sum_map_sub]
      simp only at ha
      rw [ha]; abel

/-- **Matrix instance.** The jump matrices `J = f₁ - f₀` of any chain of `s` from `S s` to
`S s + 1` sum to `1`. -/
theorem IsChain.sum_jumps_matrix {m : ℕ} {S : Fin W → Matrix (Fin m) (Fin m) (ZMod 2)}
    {evs : List (Event W (Matrix (Fin m) (Fin m) (ZMod 2)))} {s : Fin W} {is : List ℕ}
    (hc : IsChain (init S) evs s (S s) (S s + 1) is) :
    ((is.filterMap (hopJump (init S) evs)).map (fun p => p.2 - p.1)).sum = 1 := by
  rw [hc.isPath.sum_map_sub, add_sub_cancel_left]

/-! ### Sanity checks

On the two-wire run `sanityRun` of `GadgetItinerary.lean` (`gate 0 1`, `move 0 true`,
`move 1 true`, `gate 0 1`; both wires start at `false`, `tgt = true`): the move at position `1`
carries items `0` and `1` and lies on the chain `[1]` of each; the move at position `2` carries
item `1` and lies on its chain `[2]`.  On a three-frame run (`F = Fin 3`, both wires from `0` to
`2` in two hops each) the move at position `1` (`move 0 2`, carrying item `0` from frame `1`) lies
in the middle of the chain `[0, 1]` of item `0`. -/

instance decidableIsPath [DecidableEq F] : ∀ (f₀ fk : F) (js : List (F × F)),
    Decidable (IsPath f₀ fk js)
  | f₀, fk, [] => show Decidable (f₀ = fk) from inferInstance
  | f₀, fk, p :: js =>
      haveI := decidableIsPath p.2 fk js
      show Decidable (p.1 = f₀ ∧ IsPath p.2 fk js) from inferInstance

example : hopJump (init (W := 2) (fun _ => false)) sanityRun 0 = none := by decide
example : hopJump (init (W := 2) (fun _ => false)) sanityRun 1 = some (false, true) := by decide
example : hopJump (init (W := 2) (fun _ => false)) sanityRun 2 = some (false, true) := by decide
example : hopJump (init (W := 2) (fun _ => false)) sanityRun 4 = none := by decide
example : jumps sanityRun (init (W := 2) (fun _ => false)) = [(false, true), (false, true)] := by
  decide
example : ([2] : List ℕ).filterMap (hopJump (init (W := 2) (fun _ => false)) sanityRun) =
    [(false, true)] := by decide
example : List.Sublist (([2] : List ℕ).filterMap (hopJump (init (W := 2) (fun _ => false)) sanityRun))
    (jumps sanityRun (init (W := 2) (fun _ => false))) := by decide
example : IsPath false true [(false, true)] := by decide
example : ¬ IsPath false true [(false, true), (false, true)] := by decide

/-- The move at position `1` (carrying item `0`) lies on a visible chain of item `0`
(`carrying_move_on_chain` applies); the chain `[1]` witnesses the conclusion. -/
example : ∃ is : List ℕ, IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true is ∧
    Visible (init (W := 2) (fun _ => false)) sanityRun is ∧ 1 ∈ is :=
  carrying_move_on_chain (fun _ => false) (fun _ => true) 1 sanityRun (by decide) (by decide)
    (by decide) 0 1 0 true (by decide) (by decide) (by decide)

example : IsChain (init (W := 2) (fun _ => false)) sanityRun 0 false true [1] ∧
    Visible (init (W := 2) (fun _ => false)) sanityRun [1] ∧ 1 ∈ [1] := by
  unfold Visible; decide

/-- The move at position `2` (carrying item `1`) lies on a visible chain of item `1`, with the
admissibility clause for the tight coarsening `π = id`. -/
example : ∃ is : List ℕ, IsChain (init (W := 2) (fun _ => false)) sanityRun 1 false true is ∧
    Visible (init (W := 2) (fun _ => false)) sanityRun is ∧ 2 ∈ is ∧
    ∀ j ∈ is, ∀ (w' : Fin 2) (f₀ : Bool), sanityRun[j]? = some (.move w' f₀) →
      id (((init (W := 2) (fun _ => false)).run (sanityRun.take j)).frame w') ≠ id f₀ →
      id (((init (W := 2) (fun _ => false)).run (sanityRun.take j)).frame w') = id false :=
  carrying_move_on_admissible_chain (fun _ => false) (fun _ => true) 1 sanityRun (by decide)
    (by decide) (by decide) id (by decide) (by decide) 1 2 1 true (by decide) (by decide) (by decide)

example : IsChain (init (W := 2) (fun _ => false)) sanityRun 1 false true [2] ∧
    Visible (init (W := 2) (fun _ => false)) sanityRun [2] ∧ 2 ∈ [2] := by
  unfold Visible; decide

/-- A three-frame run: both wires go from frame `0` to frame `2` through frame `1`. -/
def sanityRun3 : List (Event 2 (Fin 3)) := [.move 0 1, .move 0 2, .move 1 1, .move 1 2]

example : (init (W := 2) (fun _ => (0 : Fin 3))).allValid sanityRun3 := by decide

/-- The move at position `1` (`move 0 2`, carrying item `0` from frame `1`) lies on a chain of
item `0` from `0` to `2`; the chain `[0, 1]` witnesses it, with position `1` in the middle. -/
example : ∃ is : List ℕ, IsChain (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3 0 0 2 is ∧
    Visible (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3 is ∧ 1 ∈ is :=
  carrying_move_on_chain (fun _ => (0 : Fin 3)) (fun _ => 2) 1 sanityRun3 (by decide) (by decide)
    (by decide) 0 1 0 2 (by decide) (by decide) (by decide)

example : IsChain (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3 0 0 2 [0, 1] ∧
    Visible (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3 [0, 1] ∧ 1 ∈ [0, 1] := by
  unfold Visible; decide

example : ([0, 1] : List ℕ).filterMap (hopJump (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3) =
    [(0, 1), (1, 2)] := by decide
example : IsPath (0 : Fin 3) 2 [(0, 1), (1, 2)] := by decide
example : List.Sublist
    (([0, 1] : List ℕ).filterMap (hopJump (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3))
    (jumps sanityRun3 (init (W := 2) (fun _ => (0 : Fin 3)))) := by decide
/-- `[1]` is not a chain of item `0` from `0` to `2` (it starts at frame `1`), and `[2]` is not a
chain of item `0` at all (that move carries item `1`). -/
example : ¬ IsChain (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3 0 0 2 [1] := by decide
example : ¬ IsChain (init (W := 2) (fun _ => (0 : Fin 3))) sanityRun3 0 0 2 [2] := by decide

end Transpose.ShearFrame
