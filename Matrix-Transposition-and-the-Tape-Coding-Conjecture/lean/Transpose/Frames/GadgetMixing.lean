import Transpose.Frames.GadgetCargo

/-!
# The mixing lemma: a single mixed move forces an extra hop

Formalisation of the mixing lemma, in the run model of `GadgetRuns.lean`.

Setting: a valid run `evs` from `init S` ending with wire `ρ u` at frame `tgt u` holding `e u`.
A move event `.move w g` *carries* item `s` if the moved vector (the vector of `w` just before the
event) has `s`-coordinate `1`; its *cargo* is that vector.  Frames are weighted by a cost
`d : F → F → ℕ` with `d f f = 0`, `d f g = 0 → f = g` and the triangle inequality (in the
application `F` = `m × m` matrices and `d` = rank of the difference); `m ≤ d (S s) (tgt s)` for
every item.  The rank-weighted hop count of `s` is `hopCost d s evs (init S)`, the sum of
`d (origin) (destination)` over the moves carrying `s` (moves that do not change the frame
contribute `d f f = 0`).

* `Cfg.present c s f`: some wire at `f` has `s`-coordinate `1` (presence is unchanged by gates and
  by moves whose cargo lacks `s`).
* `forward_bound` / `backward_bound`: if `s` is present at `f` after (before) a run segment, then
  `s` was (will be) present at some `f'` with `d f' f` (`d f f'`) at most the hop cost of the
  segment.  Together with the initial and final presence sets this gives item itineraries in the
  form needed here: `hopCost_ge`: `d (S s) (tgt s) ≤ hopCost d s evs (init S)`.
* `not_present_before_mixed`, `no_second_arrival`: an item `s` of minimal hop count (`≤ m`)
  carried by a visible move into `g` is not present at `g` before that move, and no later visible
  move carrying `s` has destination `g`.
* `mixedAt` and `mixedAt_run`: after a visible move into `g` whose cargo `x` has support `X` of
  size `≥ 2`, as long as no later visible move into `g` carries an item of `X` and every visible
  move out of `g` carries a unit vector, every wire at `g` is constant on the coordinates `X` and
  some wire at `g` has `s₀`-coordinate `1` (`s₀ ∈ X`); this cannot hold at the end of the run.
* `mixed_move_forces_extra_hop` (the mixing lemma, strong form) and `mixing_lemma` ("exactly one
  mixed move"): some item `s` of the support of the mixed cargo has
  `m + 1 ≤ hopCost d s evs (init S)`.

The unit-vector hypothesis is used only for visible moves *out of `g` after the mixed move*
(`unitMovesFrom`); symmetry of `d` is not needed.
-/

namespace Transpose.ShearFrame

variable {W : ℕ} {F : Type}

/-! ### Presence, hop costs and unit-cargo runs -/

/-- Item `s` is present at frame `f`: some wire at `f` has `s`-coordinate `1`. -/
def Cfg.present (c : Cfg W F) (s : Fin W) (f : F) : Prop :=
  ∃ w, c.frame w = f ∧ c.vec w s = 1

/-- The `d`-weighted hop count of item `s` along an event list: the sum of
`d (old frame) (new frame)` over the moves whose cargo has `s`-coordinate `1`. -/
def hopCost (d : F → F → ℕ) (s : Fin W) : List (Event W F) → Cfg W F → ℕ
  | [], _ => 0
  | .gate i j :: evs, c => hopCost d s evs (c.step (.gate i j))
  | .move w f :: evs, c =>
      (if c.vec w s = 1 then d (c.frame w) f else 0) + hopCost d s evs (c.step (.move w f))

/-- Every visible move (one that changes the frame of the moved wire) carries a unit vector. -/
def unitMoves : List (Event W F) → Cfg W F → Prop
  | [], _ => True
  | .gate i j :: evs, c => unitMoves evs (c.step (.gate i j))
  | .move w f :: evs, c =>
      (c.frame w ≠ f → ∃ u, c.vec w = e u) ∧ unitMoves evs (c.step (.move w f))

/-- Every visible move *out of frame `g`* carries a unit vector. -/
def unitMovesFrom (g : F) : List (Event W F) → Cfg W F → Prop
  | [], _ => True
  | .gate i j :: evs, c => unitMovesFrom g evs (c.step (.gate i j))
  | .move w f :: evs, c =>
      (c.frame w = g → f ≠ g → ∃ u, c.vec w = e u) ∧ unitMovesFrom g evs (c.step (.move w f))

theorem unitMovesFrom_of_unitMoves (g : F) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), unitMoves evs c → unitMovesFrom g evs c
  | [], _, _ => trivial
  | .gate i j :: evs, c, h => unitMovesFrom_of_unitMoves g evs _ h
  | .move w f :: evs, c, h =>
      ⟨fun hw hf => h.1 (by rw [hw]; exact hf.symm), unitMovesFrom_of_unitMoves g evs _ h.2⟩

theorem hopCost_append (d : F → F → ℕ) (s : Fin W) :
    ∀ (l₁ l₂ : List (Event W F)) (c : Cfg W F),
      hopCost d s (l₁ ++ l₂) c = hopCost d s l₁ c + hopCost d s l₂ (c.run l₁)
  | [], l₂, c => by simp [hopCost, Cfg.run]
  | .gate i j :: l₁, l₂, c => by
      show hopCost d s (l₁ ++ l₂) (c.step (.gate i j)) =
        hopCost d s l₁ (c.step (.gate i j)) + hopCost d s l₂ ((c.step (.gate i j)).run l₁)
      exact hopCost_append d s l₁ l₂ _
  | .move w f :: l₁, l₂, c => by
      show (if c.vec w s = 1 then d (c.frame w) f else 0) + hopCost d s (l₁ ++ l₂) (c.step (.move w f)) =
        (if c.vec w s = 1 then d (c.frame w) f else 0) + hopCost d s l₁ (c.step (.move w f)) +
          hopCost d s l₂ ((c.step (.move w f)).run l₁)
      rw [hopCost_append d s l₁ l₂ _, Nat.add_assoc]

theorem hopCost_cons_move (d : F → F → ℕ) (s : Fin W) (c : Cfg W F) (w : Fin W) (f : F)
    (evs : List (Event W F)) (hs : c.vec w s = 1) :
    hopCost d s (.move w f :: evs) c = d (c.frame w) f + hopCost d s evs (c.step (.move w f)) := by
  show (if c.vec w s = 1 then d (c.frame w) f else 0) + _ = _
  rw [ite_eq_left hs]

/-! ### Arithmetic in `ZMod 2` -/

theorem zmod2_add_eq_one {a b : ZMod 2} (h : a + b = 1) : a = 1 ∨ b = 1 := by
  revert a b; decide

theorem zmod2_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  revert a; decide

theorem e_apply_self (u : Fin W) : e u u = (1 : ZMod 2) := Pi.single_eq_same u 1

theorem e_apply_of_ne {u s : Fin W} (h : s ≠ u) : e u s = (0 : ZMod 2) := Pi.single_eq_of_ne h 1

theorem eq_of_e_apply_eq_one {u s : Fin W} (h : e u s = 1) : s = u := by
  by_contra hne
  rw [e_apply_of_ne hne] at h
  exact absurd h (by decide)

/-! ### Presence changes only through carrying moves -/

/-- Gates do not change presence. -/
theorem present_gate (c : Cfg W F) {i j : Fin W} (hij : i ≠ j) (hf : c.frame i = c.frame j)
    (s : Fin W) (f : F) : (c.step (.gate i j)).present s f ↔ c.present s f := by
  simp only [Cfg.present, Cfg.step]
  constructor
  · rintro ⟨w, hw, hs⟩
    by_cases hwi : w = i
    · subst hwi
      rw [Function.update_self] at hs
      rcases zmod2_add_eq_one hs with h | h
      · exact ⟨w, hw, h⟩
      · exact ⟨j, hf ▸ hw, h⟩
    · rw [Function.update_of_ne hwi] at hs
      exact ⟨w, hw, hs⟩
  · rintro ⟨w, hw, hs⟩
    by_cases hwi : w = i
    · subst hwi
      by_cases hj : c.vec j s = 1
      · exact ⟨j, hf ▸ hw, by rw [Function.update_of_ne (Ne.symm hij)]; exact hj⟩
      · refine ⟨w, hw, ?_⟩
        rw [Function.update_self, Pi.add_apply, hs, zmod2_eq_zero_of_ne_one hj, add_zero]
    · exact ⟨w, hw, by rw [Function.update_of_ne hwi]; exact hs⟩

/-- A move whose cargo lacks `s` does not change the presence of `s` anywhere. -/
theorem present_move_of_ne_one (c : Cfg W F) (w : Fin W) (f₁ : F) {s : Fin W}
    (hs : c.vec w s ≠ 1) (f : F) : (c.step (.move w f₁)).present s f ↔ c.present s f := by
  simp only [Cfg.present, Cfg.step]
  constructor
  · rintro ⟨w', hw', hs'⟩
    have hww : w' ≠ w := fun h => hs (h ▸ hs')
    exact ⟨w', by rw [Function.update_of_ne hww] at hw'; exact hw', hs'⟩
  · rintro ⟨w', hw', hs'⟩
    have hww : w' ≠ w := fun h => hs (h ▸ hs')
    exact ⟨w', by rw [Function.update_of_ne hww]; exact hw', hs'⟩

/-- A move carrying `s` makes `s` present at its destination. -/
theorem present_move_dest (c : Cfg W F) (w : Fin W) (f₁ : F) {s : Fin W} (hs : c.vec w s = 1) :
    (c.step (.move w f₁)).present s f₁ :=
  ⟨w, by simp [Cfg.step], hs⟩

/-- Presence at a frame other than the destination of a move was already there before. -/
theorem present_of_present_move_of_ne (c : Cfg W F) (w : Fin W) (f₁ : F) (s : Fin W) {f : F}
    (hf : f ≠ f₁) (h : (c.step (.move w f₁)).present s f) : c.present s f := by
  obtain ⟨w', hw', hs'⟩ := h
  have hww : w' ≠ w := by
    rintro rfl
    exact hf (Eq.symm (by simpa [Cfg.step] using hw'))
  exact ⟨w', by simpa [Cfg.step, Function.update_of_ne hww] using hw', hs'⟩

/-- Presence at a frame other than the origin of a move survives the move. -/
theorem present_move_of_ne_origin (c : Cfg W F) (w : Fin W) (f₁ : F) (s : Fin W) {f : F}
    (hf : c.frame w ≠ f) (h : c.present s f) : (c.step (.move w f₁)).present s f := by
  obtain ⟨w', hw', hs'⟩ := h
  have hww : w' ≠ w := fun h => hf (h ▸ hw')
  exact ⟨w', by simpa [Cfg.step, Function.update_of_ne hww] using hw', hs'⟩

/-- Initially `s` is present exactly at `S s`. -/
theorem present_init (S : Fin W → F) (s : Fin W) (f : F) : (init S).present s f ↔ S s = f := by
  simp only [Cfg.present, init]
  constructor
  · rintro ⟨w, hw, hs⟩
    rw [eq_of_e_apply_eq_one hs]
    exact hw
  · intro h
    exact ⟨s, h, e_apply_self s⟩

/-- At the end `s` is present exactly at `tgt s`. -/
theorem present_final (c : Cfg W F) (tgt : Fin W → F) (ρ : Equiv.Perm (Fin W))
    (hframe : ∀ u, c.frame (ρ u) = tgt u) (hvec : ∀ u, c.vec (ρ u) = e u) (s : Fin W) (f : F) :
    c.present s f ↔ tgt s = f := by
  constructor
  · rintro ⟨w, hw, hs⟩
    have hw' : w = ρ (ρ.symm w) := (Equiv.apply_symm_apply ρ w).symm
    rw [hw', hvec] at hs
    rw [hw', hframe] at hw
    rw [eq_of_e_apply_eq_one hs]
    exact hw
  · intro h
    exact ⟨ρ s, by rw [hframe]; exact h, by rw [hvec]; exact e_apply_self s⟩

/-! ### Item itineraries in potential form: hop costs dominate the distance travelled by presence -/

/-- **Forward bound.** If `s` is present at `f` after the segment, it was present before the
segment at some `f'` with `d f' f` at most the hop cost of the segment. -/
theorem forward_bound (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (htri : ∀ f g h, d f h ≤ d f g + d g h) (s : Fin W) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs → ∀ f, (c.run evs).present s f →
      ∃ f', c.present s f' ∧ d f' f ≤ hopCost d s evs c
  | [], c, _, f, h => ⟨f, h, by rw [hd0]; exact Nat.zero_le _⟩
  | .gate i j :: evs, c, hv, f, h => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      obtain ⟨f', hf', hd⟩ := forward_bound d hd0 htri s evs (c.step (.gate i j)) hv' f h
      exact ⟨f', (present_gate c hij hf s f').mp hf', hd⟩
  | .move w f₁ :: evs, c, hv, f, h => by
      obtain ⟨_, hv'⟩ := hv
      obtain ⟨f', hf', hd⟩ := forward_bound d hd0 htri s evs (c.step (.move w f₁)) hv' f h
      by_cases hs : c.vec w s = 1
      · rw [hopCost_cons_move d s c w f₁ evs hs]
        obtain ⟨w', hw', hs'⟩ := hf'
        by_cases hww : w' = w
        · subst hww
          have hf1 : f' = f₁ := by simpa [Cfg.step] using hw'.symm
          subst hf1
          refine ⟨c.frame w', ⟨w', rfl, hs⟩, ?_⟩
          calc d (c.frame w') f ≤ d (c.frame w') f' + d f' f := htri _ _ _
            _ ≤ d (c.frame w') f' + hopCost d s evs (c.step (.move w' f')) := by omega
        · refine ⟨f', ⟨w', ?_, hs'⟩, by omega⟩
          simpa [Cfg.step, Function.update_of_ne hww] using hw'
      · have h0 : hopCost d s (.move w f₁ :: evs) c = hopCost d s evs (c.step (.move w f₁)) := by
          show (if c.vec w s = 1 then d (c.frame w) f₁ else 0) + _ = _
          rw [ite_eq_right hs, Nat.zero_add]
        rw [h0]
        exact ⟨f', (present_move_of_ne_one c w f₁ hs f').mp hf', hd⟩

/-- **Backward bound.** If `s` is present at `f` before the segment, it is present after the
segment at some `f'` with `d f f'` at most the hop cost of the segment. -/
theorem backward_bound (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (htri : ∀ f g h, d f h ≤ d f g + d g h) (s : Fin W) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs → ∀ f, c.present s f →
      ∃ f', (c.run evs).present s f' ∧ d f f' ≤ hopCost d s evs c
  | [], c, _, f, h => ⟨f, h, by rw [hd0]; exact Nat.zero_le _⟩
  | .gate i j :: evs, c, hv, f, h => by
      obtain ⟨⟨hij, hf⟩, hv'⟩ := hv
      exact backward_bound d hd0 htri s evs (c.step (.gate i j)) hv' f
        ((present_gate c hij hf s f).mpr h)
  | .move w f₁ :: evs, c, hv, f, h => by
      obtain ⟨_, hv'⟩ := hv
      by_cases hs : c.vec w s = 1
      · rw [hopCost_cons_move d s c w f₁ evs hs]
        obtain ⟨w', hw', hs'⟩ := h
        by_cases hww : w' = w
        · subst hww
          subst hw'
          obtain ⟨f', hf', hd⟩ := backward_bound d hd0 htri s evs (c.step (.move w' f₁)) hv' f₁
            (present_move_dest c w' f₁ hs)
          refine ⟨f', hf', ?_⟩
          calc d (c.frame w') f' ≤ d (c.frame w') f₁ + d f₁ f' := htri _ _ _
            _ ≤ d (c.frame w') f₁ + hopCost d s evs (c.step (.move w' f₁)) := by omega
        · obtain ⟨f', hf', hd⟩ := backward_bound d hd0 htri s evs (c.step (.move w f₁)) hv' f
            ⟨w', by simpa [Cfg.step, Function.update_of_ne hww] using hw', hs'⟩
          exact ⟨f', hf', by omega⟩
      · have h0 : hopCost d s (.move w f₁ :: evs) c = hopCost d s evs (c.step (.move w f₁)) := by
          show (if c.vec w s = 1 then d (c.frame w) f₁ else 0) + _ = _
          rw [ite_eq_right hs, Nat.zero_add]
        rw [h0]
        exact backward_bound d hd0 htri s evs (c.step (.move w f₁)) hv' f
          ((present_move_of_ne_one c w f₁ hs f).mpr h)

/-- **Item itineraries, chain bound.** The hop cost of every item is at least the distance from
its source to its target. -/
theorem hopCost_ge (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (htri : ∀ f g h, d f h ≤ d f g + d g h)
    (S tgt : Fin W → F) (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u) (s : Fin W) :
    d (S s) (tgt s) ≤ hopCost d s evs (init S) := by
  obtain ⟨f', hf', hd⟩ := backward_bound d hd0 htri s evs (init S) hv (S s)
    ((present_init S s (S s)).mpr rfl)
  rw [← (present_final _ tgt ρ hframe hvec s f').mp hf'] at hd
  exact hd

/-! ### Minimal items: absent from the destination before, never arriving there again -/

theorem run_cons (c : Cfg W F) (ev : Event W F) (evs : List (Event W F)) :
    c.run (ev :: evs) = (c.step ev).run evs := rfl

/-- **(i)** An item `s` with hop cost `≤ m` carried by a visible move into `g` is not present at
`g` just before that move. -/
theorem not_present_before_mixed (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (hpos : ∀ f g, d f g = 0 → f = g) (htri : ∀ f g h, d f h ≤ d f g + d g h) (m : ℕ)
    (S tgt : Fin W → F) (hm : ∀ s, m ≤ d (S s) (tgt s))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (g : F)
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ g)
    (s : Fin W) (hs : ((init S).run evs₁).vec w s = 1)
    (hH : hopCost d s evs (init S) ≤ m) :
    ¬ ((init S).run evs₁).present s g := by
  intro hpres
  subst hsplit
  obtain ⟨hv1, _, hv2⟩ := (allValid_append _ _ _).mp hv
  rw [hopCost_append, hopCost_cons_move d s _ w g evs₂ hs] at hH
  simp only [run_append, run_cons] at hframe hvec
  obtain ⟨f', hf', hd1⟩ := forward_bound d hd0 htri s evs₁ (init S) hv1 g hpres
  rw [← (present_init S s f').mp hf'] at hd1
  obtain ⟨f'', hf'', hd2⟩ := backward_bound d hd0 htri s evs₂ _ hv2 g (present_move_dest _ w g hs)
  rw [← (present_final _ tgt ρ hframe hvec s f'').mp hf''] at hd2
  have h1 := htri (S s) g (tgt s)
  have h2 := hm s
  have h3 : d (((init S).run evs₁).frame w) g ≠ 0 := fun h => hvis (hpos _ _ h)
  omega

/-- **(ii)** An item `s` with hop cost `≤ m` carried by a move into `g` is not carried by any
later visible move into `g`. -/
theorem no_second_arrival (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (hpos : ∀ f g, d f g = 0 → f = g) (htri : ∀ f g h, d f h ≤ d f g + d g h) (m : ℕ)
    (S tgt : Fin W → F) (hm : ∀ s, m ≤ d (S s) (tgt s))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (g : F)
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (s : Fin W) (hs : ((init S).run evs₁).vec w s = 1)
    (hH : hopCost d s evs (init S) ≤ m)
    (p' q' : List (Event W F)) (w' : Fin W) (hsplit₂ : evs₂ = p' ++ .move w' g :: q')
    (hvis' : ((((init S).run evs₁).step (.move w g)).run p').frame w' ≠ g) :
    ((((init S).run evs₁).step (.move w g)).run p').vec w' s ≠ 1 := by
  intro hs'
  subst hsplit hsplit₂
  obtain ⟨hv1, _, hv2⟩ := (allValid_append _ _ _).mp hv
  obtain ⟨_, _, hv3⟩ := (allValid_append _ _ _).mp hv2
  rw [hopCost_append, hopCost_cons_move d s _ w g _ hs, hopCost_append,
    hopCost_cons_move d s _ w' g q' hs'] at hH
  simp only [run_append, run_cons] at hframe hvec
  obtain ⟨f', hf', hd1⟩ := forward_bound d hd0 htri s evs₁ (init S) hv1
    (((init S).run evs₁).frame w) ⟨w, rfl, hs⟩
  rw [← (present_init S s f').mp hf'] at hd1
  obtain ⟨f'', hf'', hd2⟩ := backward_bound d hd0 htri s q' _ hv3 g (present_move_dest _ w' g hs')
  rw [← (present_final _ tgt ρ hframe hvec s f'').mp hf''] at hd2
  have h1 := htri (S s) (((init S).run evs₁).frame w) (tgt s)
  have h2 := htri (((init S).run evs₁).frame w) g (tgt s)
  have h3 := hm s
  have h4 : d (((((init S).run evs₁).step (.move w g)).run p').frame w') g ≠ 0 :=
    fun h => hvis' (hpos _ _ h)
  omega

/-! ### The mixing invariant at the destination frame -/

/-- Frame `g` is *mixed on the support of `x`*, witnessed by `s₀`: every wire at `g` is constant on
the coordinates `{t | x t = 1}`, and `s₀` is present at `g`.  (When `x s₀ = 1`, this says that the
projection of the span at `g` onto the support coordinates is the line spanned by the all-ones
vector.) -/
def mixedAt (c : Cfg W F) (g : F) (x : Vec W) (s₀ : Fin W) : Prop :=
  (∀ w', c.frame w' = g → ∀ t, x t = 1 → c.vec w' t = c.vec w' s₀) ∧ c.present s₀ g

/-- The invariant survives one event, provided a visible move out of `g` carries a unit vector and
a visible move into `g` carries nothing of the support of `x`. -/
theorem mixedAt_step (c : Cfg W F) (g : F) (x : Vec W) {s₀ t₀ : Fin W} (hs₀ : x s₀ = 1)
    (ht₀ : x t₀ = 1) (hne : s₀ ≠ t₀) (ev : Event W F) (hv : c.valid ev)
    (hinv : mixedAt c g x s₀)
    (hunit : ∀ w' f₁, ev = .move w' f₁ → c.frame w' = g → f₁ ≠ g → ∃ u, c.vec w' = e u)
    (harr : ∀ w', ev = .move w' g → c.frame w' ≠ g → ∀ t, x t = 1 → c.vec w' t ≠ 1) :
    mixedAt (c.step ev) g x s₀ := by
  obtain ⟨hA, hB⟩ := hinv
  cases ev with
  | gate i j =>
    obtain ⟨hij, hf⟩ := hv
    refine ⟨?_, (present_gate c hij hf s₀ g).mpr hB⟩
    intro w' hw' t ht
    simp only [Cfg.step] at hw' ⊢
    by_cases hwi : w' = i
    · subst hwi
      rw [Function.update_self, Pi.add_apply, Pi.add_apply, hA w' hw' t ht,
        hA j (hf.symm.trans hw') t ht]
    · rw [Function.update_of_ne hwi]
      exact hA w' hw' t ht
  | move w' f₁ =>
    by_cases hchg : c.frame w' = f₁
    · have hself : c.step (.move w' f₁) = c := by
        simp only [Cfg.step]
        rw [← hchg, Function.update_eq_self]
      rw [hself]
      exact ⟨hA, hB⟩
    · by_cases hout : c.frame w' = g
      · -- a visible move out of `g`: it carries `e u` with `u ≠ s₀` (constancy on the support)
        obtain ⟨u, hu⟩ := hunit w' f₁ rfl hout (fun h => hchg (hout.trans h.symm))
        have hus : u ≠ s₀ := by
          rintro rfl
          have h := hA w' hout t₀ ht₀
          rw [hu, e_apply_of_ne (Ne.symm hne), e_apply_self] at h
          exact absurd h (by decide)
        have hs0 : c.vec w' s₀ ≠ 1 := by
          rw [hu, e_apply_of_ne (Ne.symm hus)]
          decide
        refine ⟨?_, (present_move_of_ne_one c w' f₁ hs0 g).mpr hB⟩
        intro w'' hw'' t ht
        simp only [Cfg.step] at hw'' ⊢
        have hww : w'' ≠ w' := by
          rintro rfl
          rw [Function.update_self] at hw''
          exact hchg (hout.trans hw''.symm)
        rw [Function.update_of_ne hww] at hw''
        exact hA w'' hw'' t ht
      · by_cases hin : f₁ = g
        · -- a visible move into `g`: its cargo vanishes on the support
          have hX := harr w' (by rw [hin]) hout
          have hs0 : c.vec w' s₀ ≠ 1 := hX s₀ hs₀
          refine ⟨?_, (present_move_of_ne_one c w' f₁ hs0 g).mpr hB⟩
          intro w'' hw'' t ht
          simp only [Cfg.step] at hw'' ⊢
          by_cases hww : w'' = w'
          · subst hww
            rw [zmod2_eq_zero_of_ne_one (hX t ht), zmod2_eq_zero_of_ne_one hs0]
          · rw [Function.update_of_ne hww] at hw''
            exact hA w'' hw'' t ht
        · -- a move not touching `g`
          refine ⟨?_, present_move_of_ne_origin c w' f₁ s₀ hout hB⟩
          intro w'' hw'' t ht
          simp only [Cfg.step] at hw'' ⊢
          have hww : w'' ≠ w' := by
            rintro rfl
            rw [Function.update_self] at hw''
            exact hin hw''
          rw [Function.update_of_ne hww] at hw''
          exact hA w'' hw'' t ht

/-- The invariant is maintained along a valid run in which every visible move out of `g` carries
a unit vector and no visible move into `g` carries an item of the support of `x`. -/
theorem mixedAt_run (g : F) (x : Vec W) {s₀ t₀ : Fin W} (hs₀ : x s₀ = 1) (ht₀ : x t₀ = 1)
    (hne : s₀ ≠ t₀) :
    ∀ (evs : List (Event W F)) (c : Cfg W F), c.allValid evs → mixedAt c g x s₀ →
      unitMovesFrom g evs c →
      (∀ (p' q' : List (Event W F)) (w' : Fin W), evs = p' ++ .move w' g :: q' →
        (c.run p').frame w' ≠ g → ∀ t, x t = 1 → (c.run p').vec w' t ≠ 1) →
      mixedAt (c.run evs) g x s₀
  | [], _, _, hinv, _, _ => hinv
  | ev :: evs, c, hv, hinv, hunit, harr => by
      obtain ⟨hv1, hv2⟩ := hv
      have hstep : mixedAt (c.step ev) g x s₀ := by
        refine mixedAt_step c g x hs₀ ht₀ hne ev hv1 hinv ?_ ?_
        · intro w' f₁ hev hw hf
          subst hev
          exact hunit.1 hw hf
        · intro w' hev hw t ht
          subst hev
          exact harr [] evs w' rfl hw t ht
      refine mixedAt_run g x hs₀ ht₀ hne evs (c.step ev) hv2 hstep ?_ ?_
      · cases ev with
        | gate i j => exact hunit
        | move w f => exact hunit.2
      · intro p' q' w' hsplit hw t ht
        exact harr (ev :: p') q' w' (congrArg (ev :: ·) hsplit) hw t ht

/-! ### The mixing lemma -/

/-- **Mixing lemma, strong form.** In a valid run from `init S` ending with wire `ρ u` at `tgt u`
holding `e u`, let `.move w g` be a visible move whose cargo `x` has two distinct items `s₀ ≠ t₀`
in its support, and suppose every later visible move *out of `g`* carries a unit vector.  Then
some item `s` of the support of `x` has `d`-weighted hop count at least `m + 1`, for any cost
`d` with `d f f = 0`, `d f g = 0 → f = g`, the triangle inequality, and `m ≤ d (S s) (tgt s)`. -/
theorem mixed_move_forces_extra_hop (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (hpos : ∀ f g, d f g = 0 → f = g) (htri : ∀ f g h, d f h ≤ d f g + d g h) (m : ℕ)
    (S tgt : Fin W → F) (hm : ∀ s, m ≤ d (S s) (tgt s))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (g : F)
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ g)
    (s₀ t₀ : Fin W) (hs₀ : ((init S).run evs₁).vec w s₀ = 1)
    (ht₀ : ((init S).run evs₁).vec w t₀ = 1) (hne : s₀ ≠ t₀)
    (hunit : unitMovesFrom g evs₂ (((init S).run evs₁).step (.move w g))) :
    ∃ s, ((init S).run evs₁).vec w s = 1 ∧ m + 1 ≤ hopCost d s evs (init S) := by
  by_contra hcon
  have hH : ∀ s, ((init S).run evs₁).vec w s = 1 → hopCost d s evs (init S) ≤ m := by
    intro s hs
    by_contra h
    exact hcon ⟨s, hs, by omega⟩
  -- (i): no item of the support is present at `g` before the mixed move
  have hnp : ∀ s, ((init S).run evs₁).vec w s = 1 → ¬ ((init S).run evs₁).present s g :=
    fun s hs => not_present_before_mixed d hd0 hpos htri m S tgt hm ρ evs hv hframe hvec
      evs₁ evs₂ w g hsplit hvis s hs (hH s hs)
  -- the invariant holds right after the mixed move
  have hinv : mixedAt (((init S).run evs₁).step (.move w g)) g (((init S).run evs₁).vec w) s₀ := by
    refine ⟨?_, present_move_dest _ w g hs₀⟩
    intro w' hw' t ht
    simp only [Cfg.step] at hw' ⊢
    by_cases hww : w' = w
    · subst hww
      rw [ht, hs₀]
    · rw [Function.update_of_ne hww] at hw'
      have h1 : ((init S).run evs₁).vec w' t ≠ 1 := fun h => hnp t ht ⟨w', hw', h⟩
      have h2 : ((init S).run evs₁).vec w' s₀ ≠ 1 := fun h => hnp s₀ hs₀ ⟨w', hw', h⟩
      rw [zmod2_eq_zero_of_ne_one h1, zmod2_eq_zero_of_ne_one h2]
  -- ... and is maintained to the end, by (ii)
  have hv2 : (((init S).run evs₁).step (.move w g)).allValid evs₂ := by
    subst hsplit
    exact ((allValid_append _ _ _).mp hv).2.2
  have hend := mixedAt_run g _ hs₀ ht₀ hne evs₂ _ hv2 hinv hunit (by
    intro p' q' w' hsplit₂ hw t ht
    exact no_second_arrival d hd0 hpos htri m S tgt hm ρ evs hv hframe hvec evs₁ evs₂ w g hsplit
      t ht (hH t ht) p' q' w' hsplit₂ hw)
  have hrun : (((init S).run evs₁).step (.move w g)).run evs₂ = (init S).run evs := by
    rw [hsplit, run_append, run_cons]
  rw [hrun] at hend
  -- contradiction at the end: the wire witnessing `s₀` at `g` holds `e s₀`, not constant on `X`
  obtain ⟨hA, w', hw', hs'⟩ := hend
  have hvec' : ((init S).run evs).vec w' = e (ρ.symm w') := by
    have h := hvec (ρ.symm w')
    rwa [Equiv.apply_symm_apply] at h
  rw [hvec'] at hs'
  have hu : s₀ = ρ.symm w' := eq_of_e_apply_eq_one hs'
  have hAt := hA w' hw' t₀ ht₀
  rw [hvec', ← hu, e_apply_of_ne (Ne.symm hne), e_apply_self] at hAt
  exact absurd hAt (by decide)

/-- **Mixing lemma.** If exactly one visible move of the run has a cargo of support `≥ 2` — the
move `.move w g` at the split, with `s₀ ≠ t₀` in its support — and every other visible move
carries a unit vector, then some item `s` of that support has `d`-weighted hop count at least
`m + 1`.  (The hypothesis on the moves before the mixed move is not used.) -/
theorem mixing_lemma (d : F → F → ℕ) (hd0 : ∀ f, d f f = 0)
    (hpos : ∀ f g, d f g = 0 → f = g) (htri : ∀ f g h, d f h ≤ d f g + d g h) (m : ℕ)
    (S tgt : Fin W → F) (hm : ∀ s, m ≤ d (S s) (tgt s))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W F)) (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = tgt u)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W F)) (w : Fin W) (g : F)
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ g)
    (s₀ t₀ : Fin W) (hs₀ : ((init S).run evs₁).vec w s₀ = 1)
    (ht₀ : ((init S).run evs₁).vec w t₀ = 1) (hne : s₀ ≠ t₀)
    (_hunit₁ : unitMoves evs₁ (init S))
    (hunit₂ : unitMoves evs₂ (((init S).run evs₁).step (.move w g))) :
    ∃ s, ((init S).run evs₁).vec w s = 1 ∧ m + 1 ≤ hopCost d s evs (init S) :=
  mixed_move_forces_extra_hop d hd0 hpos htri m S tgt hm ρ evs hv hframe hvec evs₁ evs₂ w g
    hsplit hvis s₀ t₀ hs₀ ht₀ hne (unitMovesFrom_of_unitMoves g evs₂ _ hunit₂)

/-! ### The intended instance: rational matrix frames, cost of a jump = rank of the difference -/

section MatrixFrames

variable {n : ℕ}

variable {K : Type} [Field K]

/-- Subadditivity of the rank (as `rank_add_le` in `Gadget.lean`, reproved here to keep the
import of this file minimal). -/
theorem rank_add_le' (A B : Matrix (Fin n) (Fin n) K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank K ↥(LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- A matrix of rank `0` over a field is zero. -/
theorem eq_zero_of_rank_eq_zero {A : Matrix (Fin n) (Fin n) K} (h : A.rank = 0) : A = 0 := by
  have hrange : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  ext i j
  have hmem : Matrix.mulVec A (Pi.single j 1) ∈ LinearMap.range A.mulVecLin :=
    ⟨Pi.single j 1, Matrix.mulVecLin_apply _ _⟩
  rw [hrange, Submodule.mem_bot] at hmem
  have hij := congrFun hmem i
  rw [Matrix.mulVec_single_one] at hij
  simpa using hij

/-- **Mixing lemma for matrix frames over any field** `K`: `n × n` frames, targets `S u + 1`, cost
of a jump from `A` to `B` equal to `rank (B - A)` over `K`. -/
theorem mixing_lemma_matrix_field (S : Fin W → Matrix (Fin n) (Fin n) K)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin n) (Fin n) K)))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W (Matrix (Fin n) (Fin n) K))) (w : Fin W)
    (g : Matrix (Fin n) (Fin n) K)
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ g)
    (s₀ t₀ : Fin W) (hs₀ : ((init S).run evs₁).vec w s₀ = 1)
    (ht₀ : ((init S).run evs₁).vec w t₀ = 1) (hne : s₀ ≠ t₀)
    (hunit₁ : unitMoves evs₁ (init S))
    (hunit₂ : unitMoves evs₂ (((init S).run evs₁).step (.move w g))) :
    ∃ s, ((init S).run evs₁).vec w s = 1 ∧
      n + 1 ≤ hopCost (fun A B => (B - A).rank) s evs (init S) := by
  refine mixing_lemma (fun A B => (B - A).rank) (fun f => by simp) 
    (fun A B h => (sub_eq_zero.mp (eq_zero_of_rank_eq_zero h)).symm)
    (fun f g h => by
      have : h - f = (g - f) + (h - g) := by abel
      rw [this]
      exact rank_add_le' _ _) n S (fun u => S u + 1)
    (fun s => by simp) ρ evs hv hframe hvec evs₁ evs₂ w g hsplit hvis s₀ t₀ hs₀ ht₀ hne hunit₁ hunit₂

/-- The mixing lemma in the mod-2 relaxation (frames in `F₂^{n×n}`, cost = rank over `F₂`). -/
theorem mixing_lemma_matrix_zmod2 (S : Fin W → Matrix (Fin n) (Fin n) (ZMod 2))
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin n) (Fin n) (ZMod 2))))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W (Matrix (Fin n) (Fin n) (ZMod 2)))) (w : Fin W)
    (g : Matrix (Fin n) (Fin n) (ZMod 2))
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ g)
    (s₀ t₀ : Fin W) (hs₀ : ((init S).run evs₁).vec w s₀ = 1)
    (ht₀ : ((init S).run evs₁).vec w t₀ = 1) (hne : s₀ ≠ t₀)
    (hunit₁ : unitMoves evs₁ (init S))
    (hunit₂ : unitMoves evs₂ (((init S).run evs₁).step (.move w g))) :
    ∃ s, ((init S).run evs₁).vec w s = 1 ∧
      n + 1 ≤ hopCost (fun A B => (B - A).rank) s evs (init S) :=
  mixing_lemma_matrix_field S ρ evs hv hframe hvec evs₁ evs₂ w g hsplit hvis s₀ t₀ hs₀ ht₀ hne hunit₁ hunit₂

/-- **Mixing lemma for matrix frames**: rational `n × n` matrix frames, targets `S u + 1`, cost of
a jump from `A` to `B` equal to `rank (B - A)`.  If exactly one visible move has a cargo of support
`≥ 2` and every other visible move carries a unit vector, some item of that support has
rank-weighted hop count `≥ n + 1`. -/
theorem mixing_lemma_matrix (S : Fin W → Matrix (Fin n) (Fin n) ℚ)
    (ρ : Equiv.Perm (Fin W)) (evs : List (Event W (Matrix (Fin n) (Fin n) ℚ)))
    (hv : (init S).allValid evs)
    (hframe : ∀ u, ((init S).run evs).frame (ρ u) = S u + 1)
    (hvec : ∀ u, ((init S).run evs).vec (ρ u) = e u)
    (evs₁ evs₂ : List (Event W (Matrix (Fin n) (Fin n) ℚ))) (w : Fin W)
    (g : Matrix (Fin n) (Fin n) ℚ)
    (hsplit : evs = evs₁ ++ .move w g :: evs₂)
    (hvis : ((init S).run evs₁).frame w ≠ g)
    (s₀ t₀ : Fin W) (hs₀ : ((init S).run evs₁).vec w s₀ = 1)
    (ht₀ : ((init S).run evs₁).vec w t₀ = 1) (hne : s₀ ≠ t₀)
    (hunit₁ : unitMoves evs₁ (init S))
    (hunit₂ : unitMoves evs₂ (((init S).run evs₁).step (.move w g))) :
    ∃ s, ((init S).run evs₁).vec w s = 1 ∧
      n + 1 ≤ hopCost (fun A B => (B - A).rank) s evs (init S) :=
  mixing_lemma (fun A B => (B - A).rank)
    (fun A => by simp)
    (fun A B h => (sub_eq_zero.mp (eq_zero_of_rank_eq_zero h)).symm)
    (fun A B C => by
      have h : C - A = (B - A) + (C - B) := by abel
      rw [h]
      exact rank_add_le' _ _)
    n S (fun u => S u + 1)
    (fun u => by simp)
    ρ evs hv hframe hvec evs₁ evs₂ w g hsplit hvis s₀ t₀ hs₀ ht₀ hne hunit₁ hunit₂

end MatrixFrames

/-! ### A sanity check of the definitions on a two-wire run (`F = Bool`, discrete cost)

Wire `0` is gated to `e 0 + e 1` at `false`, moved to `true` (the single mixed move), wire `1`
follows with `e 1`, and a gate at `true` restores `e 0`.  Item `1` is carried twice, item `0`
once: the bound `m + 1 = 2` of the mixing lemma is attained by item `1`. -/

/-- The discrete cost on `Bool`. -/
def dBool (f g : Bool) : ℕ := if f = g then 0 else 1

instance decidableValid [DecidableEq F] (c : Cfg W F) : ∀ ev : Event W F, Decidable (c.valid ev)
  | .gate i j => show Decidable (i ≠ j ∧ c.frame i = c.frame j) from inferInstance
  | .move _ _ => show Decidable True from inferInstance

instance decidableAllValid [DecidableEq F] :
    ∀ (evs : List (Event W F)) (c : Cfg W F), Decidable (c.allValid evs)
  | [], _ => show Decidable True from inferInstance
  | ev :: evs, c =>
      haveI := decidableAllValid evs (c.step ev)
      show Decidable (c.valid ev ∧ (c.step ev).allValid evs) from inferInstance

example : hopCost dBool 0
    [.gate 0 1, .move 0 true, .move 1 true, .gate 0 1] (init (W := 2) (fun _ => false)) = 1 := by
  decide

example : hopCost dBool 1
    [.gate 0 1, .move 0 true, .move 1 true, .gate 0 1] (init (W := 2) (fun _ => false)) = 2 := by
  decide

example : (init (W := 2) (fun _ => false)).allValid
    [.gate 0 1, .move 0 true, .move 1 true, .gate 0 1] := by
  decide

example : ((init (W := 2) (fun _ => false)).run [.gate 0 1, .move 0 true, .move 1 true, .gate 0 1]).vec =
    e ∧ ((init (W := 2) (fun _ => false)).run
      [.gate 0 1, .move 0 true, .move 1 true, .gate 0 1]).frame = fun _ => true := by
  decide

end Transpose.ShearFrame
