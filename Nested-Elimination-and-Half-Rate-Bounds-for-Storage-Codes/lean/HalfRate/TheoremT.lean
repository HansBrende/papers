import HalfRate.N3

/-!
# Theorem T: no transitive triangle, in-degree-≥3 vertices acyclic

If a loopless recovery relation has no transitive triangle and its vertices with at least three
in-neighbours induce an acyclic sub-relation, it satisfies the weighted half bound, with no
bound on in- or out-degrees (Theorem T of the paper). The proof follows the paper. Within the
remaining vertex set `R`:
* (a) a vertex with at most one in-neighbour in `R` is a piece by itself;
* (b) otherwise, a shortest directed cycle among the vertices with exactly two in-neighbours in
  `R` is induced, and it is a relative 2-dicolouring (a digon contraction): split it by whether
  a vertex's in-neighbour off the cycle equals that of a fixed cycle vertex;
* (c) otherwise the in-degree-two and in-degree-≥3 vertices are both acyclic: a 2-dicolouring.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

/-- No transitive triangle inside `S`. -/
def TTFreeOn (N : V → Finset V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → y ≠ z → x ≠ z → x ∈ N y → y ∈ N z → x ∈ N z → False

omit [DecidableEq V] [Fintype V] in
theorem TTFreeOn.mono {S R : Finset V} (h : TTFreeOn N S) (hRS : R ⊆ S) : TTFreeOn N R :=
  fun x hx y hy z hz => h x (hRS hx) y (hRS hy) z (hRS hz)

section DirectedCycles

/-- A directed cycle of length `ℓ` inside `W`, listed against the arcs: `f (k+1)` is an
in-neighbour of `f k` (indices mod `ℓ`). -/
structure DCyc (N : V → Finset V) (W : Finset V) (ℓ : ℕ) where
  pos : 0 < ℓ
  f : Fin ℓ → V
  inj : Function.Injective f
  mem : ∀ i, f i ∈ W
  arc : ∀ k, f (idx pos (k + 1)) ∈ N (f (idx pos k))

/-- `W` contains a directed cycle of length `ℓ ≥ 2`. -/
def HasDCyc (N : V → Finset V) (W : Finset V) (ℓ : ℕ) : Prop := 2 ≤ ℓ ∧ Nonempty (DCyc N W ℓ)

omit [DecidableEq V] [Fintype V] in
theorem HasDCyc.mono {W W' : Finset V} {ℓ : ℕ} (h : HasDCyc N W ℓ) (hW : W ⊆ W') :
    HasDCyc N W' ℓ := by
  obtain ⟨hℓ, ⟨c⟩⟩ := h
  exact ⟨hℓ, ⟨{
    pos := c.pos
    f := c.f
    inj := c.inj
    mem := fun i => hW (c.mem i)
    arc := c.arc }⟩⟩

theorem idx_succ_val {g : ℕ} (hg : 0 < g) (k : ℕ) :
    (idx hg (k + 1)).val = if (idx hg k).val + 1 = g then 0 else (idx hg k).val + 1 := by
  simp only [idx_val]
  have h3 := Nat.mod_lt k hg
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge 1 g with hg1 | hg1
  · rw [Nat.mod_eq_of_lt hg1]
    by_cases h : k % g + 1 = g
    · simp [h]
    · simp only [h, ↓reduceIte]; exact Nat.mod_eq_of_lt (by omega)
  · have : g = 1 := by omega
    subst this; simp [Nat.mod_one]

omit [DecidableEq V] [Fintype V] in
/-- A closed in-walk `p 0, …, p n` (`n ≥ 1`, `p (s+1) → p s`, `p 0 → p n`) is a directed cycle
of length `n + 1`. -/
theorem hasDCyc_of_closed {W : Finset V} (p : ℕ → V) (n : ℕ) (hn : 1 ≤ n)
    (hinj : ∀ s t, s ≤ n → t ≤ n → p s = p t → s = t)
    (harc : ∀ s < n, p (s + 1) ∈ N (p s)) (hclose : p 0 ∈ N (p n))
    (hmem : ∀ s ≤ n, p s ∈ W) : HasDCyc N W (n + 1) := by
  refine ⟨by omega, ⟨⟨by omega, fun i => p i.val, ?_,
    fun i => hmem _ (Nat.lt_succ_iff.mp i.isLt), ?_⟩⟩⟩
  · intro i j h
    exact Fin.ext (hinj _ _ (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) h)
  · intro k
    have hk := (idx (show 0 < n + 1 by omega) k).isLt
    have e := idx_succ_val (show 0 < n + 1 by omega) k
    by_cases h : (idx (show 0 < n + 1 by omega) k).val + 1 = n + 1
    · simp only [h, ↓reduceIte] at e
      show p (idx _ (k + 1)).val ∈ N (p (idx _ k).val)
      rw [e, show (idx (show 0 < n + 1 by omega) k).val = n by omega]
      exact hclose
    · simp only [h, ↓reduceIte] at e
      show p (idx _ (k + 1)).val ∈ N (p (idx _ k).val)
      rw [e]
      exact harc _ (by omega)

variable {W : Finset V} {ℓ : ℕ}

omit [DecidableEq V] [Fintype V] in
/-- Jumping from `f i` to `f (idx a)` along an arc and following the cycle for `d` steps back
to `f i` closes a directed cycle of length `d + 1`. -/
theorem DCyc.hasDCyc_short (c : DCyc N W ℓ) (i : Fin ℓ) (a d : ℕ) (hd1 : 1 ≤ d) (hd : d < ℓ)
    (hai : idx c.pos (a + d) = i) (hch : c.f (idx c.pos a) ∈ N (c.f i)) :
    HasDCyc N W (d + 1) := by
  let p : ℕ → V := fun s => if s = 0 then c.f i else c.f (idx c.pos (a + (s - 1)))
  have p0 : p 0 = c.f i := by simp [p]
  have ps : ∀ s, p (s + 1) = c.f (idx c.pos (a + s)) := fun s => by
    simp only [p, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  refine hasDCyc_of_closed p d hd1 ?_ ?_ ?_ ?_
  · intro s t hs ht hst
    rcases s with _ | s <;> rcases t with _ | t
    · rfl
    · rw [p0, ps] at hst
      have := idx_inj c.pos (a := a + t) (b := a + d) (by omega) (by omega)
        ((c.inj hst).symm.trans hai.symm)
      omega
    · rw [p0, ps] at hst
      have := idx_inj c.pos (a := a + s) (b := a + d) (by omega) (by omega)
        ((c.inj hst).trans hai.symm)
      omega
    · rw [ps, ps] at hst
      have h' := c.inj hst
      rcases le_total s t with hst' | hts'
      · have := idx_inj c.pos (by omega) (by omega) h'; omega
      · have := idx_inj c.pos (by omega) (by omega) h'.symm; omega
  · intro s _
    rcases s with _ | s
    · rw [ps, p0]; simpa using hch
    · rw [ps, ps]; exact c.arc (a + s)
  · have e : d = (d - 1) + 1 := by omega
    rw [p0, e, ps]
    have := c.arc (a + (d - 1))
    rwa [show a + (d - 1) + 1 = a + d by omega, hai] at this
  · intro s _
    rcases s with _ | s
    · rw [p0]; exact c.mem i
    · rw [ps]; exact c.mem _

omit [DecidableEq V] [Fintype V] in
/-- A shortest directed cycle is induced: the only in-neighbour of `f i` on it is `f (i+1)`. -/
theorem DCyc.chordless (c : DCyc N W ℓ) (hloop : ∀ v, v ∉ N v)
    (hmin : ∀ ℓ', HasDCyc N W ℓ' → ℓ ≤ ℓ') {i j : Fin ℓ} (h : c.f j ∈ N (c.f i)) :
    j = idx c.pos (i.val + 1) := by
  by_contra hne
  have hij : i ≠ j := by rintro rfl; exact hloop _ h
  have hiv := i.isLt
  have hjv := j.isLt
  have hne' : j.val ≠ (i.val + 1) % ℓ := fun e => hne (Fin.ext e)
  have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
  obtain ⟨d, hd1, hdl, hai⟩ : ∃ d, 1 ≤ d ∧ d + 1 < ℓ ∧ idx c.pos (j.val + d) = i := by
    rcases Nat.lt_or_ge j.val i.val with hji | hji
    · refine ⟨i.val - j.val, by omega, ?_, ?_⟩
      · rcases Nat.lt_or_ge (i.val + 1) ℓ with h1 | h1
        · omega
        · have h2 : i.val + 1 = ℓ := by omega
          rw [h2, Nat.mod_self] at hne'; omega
      · rw [show j.val + (i.val - j.val) = i.val by omega]; exact idx_self c.pos i
    · refine ⟨i.val + ℓ - j.val, by omega, ?_, ?_⟩
      · rcases Nat.lt_or_ge (i.val + 1) ℓ with h1 | h1
        · rw [Nat.mod_eq_of_lt h1] at hne'; omega
        · omega
      · rw [show j.val + (i.val + ℓ - j.val) = ℓ + i.val by omega, idx_add_self]
        exact idx_self c.pos i
  have hc := c.hasDCyc_short i j.val d hd1 (by omega) hai (by rw [idx_self]; exact h)
  have := hmin _ hc
  omega

omit [Fintype V] in
/-- A nonempty set in which every vertex has an in-neighbour contains a directed cycle. -/
theorem exists_hasDCyc_of_sourceless (hloop : ∀ v, v ∉ N v) {T : Finset V} (hne : T.Nonempty)
    (hsrc : ∀ v ∈ T, ∃ u ∈ N v, u ∈ T) : ∃ ℓ, HasDCyc N T ℓ := by
  classical
  let σ : V → V := fun v => if h : v ∈ T then (hsrc v h).choose else v
  have hσ : ∀ v ∈ T, σ v ∈ N v ∧ σ v ∈ T := fun v hv => by
    simp only [σ, hv, ↓reduceDIte]; exact (hsrc v hv).choose_spec
  obtain ⟨v₀, hv₀⟩ := hne
  let s : ℕ → V := fun k => σ^[k] v₀
  have hs_succ : ∀ k, s (k + 1) = σ (s k) := fun k => Function.iterate_succ_apply' σ k v₀
  have hsT : ∀ k, s k ∈ T := by
    intro k
    induction k with
    | zero => exact hv₀
    | succ k ih => rw [hs_succ]; exact (hσ _ ih).2
  -- a repetition exists (pigeonhole); take the first one
  have hrep : ∃ b, ∃ a < b, s a = s b := by
    obtain ⟨x, -, y, -, hxy, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := range (T.card + 1)) (t := T) (f := s) (by simp) (fun k _ => hsT k)
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, he⟩
    · exact ⟨x, y, h, he.symm⟩
  obtain ⟨b, ⟨a, hab, hsab⟩, hmin⟩ : ∃ b, (∃ a < b, s a = s b) ∧
      ∀ b' < b, ¬ ∃ a < b', s a = s b' :=
    ⟨Nat.find hrep, Nat.find_spec hrep, fun b' hb' => Nat.find_min hrep hb'⟩
  -- no loops, so the cycle has length at least two
  have hab2 : a + 1 < b := by
    by_contra hcon
    have hb : b = a + 1 := by omega
    have h2 : σ (s a) = s a := by rw [← hs_succ, ← hb, hsab]
    have h4 := (hσ _ (hsT a)).1
    rw [h2] at h4
    exact hloop _ h4
  refine ⟨b - a - 1 + 1, hasDCyc_of_closed (fun t => s (a + t)) (b - a - 1) (by omega)
    ?_ ?_ ?_ ?_⟩
  · intro t t' ht ht' he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hmin (a + t') (by omega) ⟨a + t, by omega, he⟩
    · exact hmin (a + t) (by omega) ⟨a + t', by omega, he.symm⟩
  · intro t _
    show s (a + (t + 1)) ∈ N (s (a + t))
    rw [show a + (t + 1) = a + t + 1 by omega, hs_succ]
    exact (hσ _ (hsT _)).1
  · show s (a + 0) ∈ N (s (a + (b - a - 1)))
    have e2 : s b = σ (s (b - 1)) := by
      have := hs_succ (b - 1); rwa [show b - 1 + 1 = b by omega] at this
    rw [show a + (b - a - 1) = b - 1 by omega, Nat.add_zero, hsab, e2]
    exact (hσ _ (hsT _)).1
  · intro t _; exact hsT _

omit [DecidableEq V] [Fintype V] in
/-- A set of vertices of an induced directed cycle that misses one of them is acyclic. -/
theorem DCyc.acyclic_of_missing (c : DCyc N W ℓ)
    (hch : ∀ i j : Fin ℓ, c.f j ∈ N (c.f i) → j = idx c.pos (i.val + 1))
    {X : Finset V} (hX : ∀ x ∈ X, ∃ k, c.f k = x) (k₀ : Fin ℓ) (hk₀ : c.f k₀ ∉ X) :
    IsAcyclicIn N X := by
  intro T hT hne
  by_contra hcon
  -- every cycle vertex in `T` has its cycle parent in `T`
  have hclosed : ∀ k : Fin ℓ, c.f k ∈ T → c.f (idx c.pos (k.val + 1)) ∈ T := by
    intro k hk
    by_contra hk'
    apply hcon
    refine ⟨c.f k, hk, fun u hu huT => ?_⟩
    obtain ⟨j, rfl⟩ := hX u (hT huT)
    rw [hch k j hu] at huT
    exact hk' huT
  obtain ⟨x, hx⟩ := hne
  obtain ⟨k₁, rfl⟩ := hX x (hT hx)
  have hall : ∀ n, c.f (idx c.pos (k₁.val + n)) ∈ T := by
    intro n
    induction n with
    | zero => rw [Nat.add_zero, idx_self]; exact hx
    | succ n ih =>
      have := hclosed _ ih
      rwa [show idx c.pos ((idx c.pos (k₁.val + n)).val + 1) = idx c.pos (k₁.val + (n + 1)) from
        Fin.ext (by simp only [idx_val, Nat.mod_add_mod, Nat.add_assoc])] at this
  have := hall (k₀.val + ℓ - k₁.val)
  rw [show k₁.val + (k₀.val + ℓ - k₁.val) = ℓ + k₀.val by omega, idx_add_self,
    idx_self] at this
  exact hk₀ (hT this)

end DirectedCycles

section Pieces

variable {R L : Finset V}

/-- (a) A vertex with at most one in-neighbour in `R` is a piece by itself. -/
theorem singlePiece (hloop : ∀ v, v ∉ N v) {v : V}
    (hL : ∀ u ∈ N v, u ∉ L) (h1 : (N v ∩ R).card ≤ 1) :
    Nonempty (PieceCert N (univ \ (R ∪ L)) {v}) := by
  refine bdirPiece N (univ \ (R ∪ L)) {v} {v} ∅ (disjoint_empty_right _) (union_empty _)
    (isAcyclicIn_singleton (hloop v)) (isAcyclicIn_empty N) (outPar N R {v}) ?_ ?_ ?_
  · intro x hx u hu
    rw [mem_singleton.mp hx] at hu ⊢
    by_cases huR : u ∈ R
    · right; right
      have huv : u ∉ ({v} : Finset V) := by
        rw [mem_singleton]; rintro rfl; exact hloop _ hu
      cases hp : outPar N R {v} v with
      | none => exact absurd (outPar_none hp hu huR) huv
      | some w =>
        obtain ⟨hw, hwR, -⟩ := outPar_some hp
        rw [card_le_one.mp h1 w (mem_inter.mpr ⟨hw, hwR⟩) u (mem_inter.mpr ⟨hu, huR⟩)]
    · left; simp [huR, hL u hu]
  · intro x _ w hp
    obtain ⟨-, hwR, hwv⟩ := outPar_some hp
    exact ⟨by simp [hwR], hwv⟩
  · intro x hx x' hx' w _ _
    rw [mem_singleton.mp hx, mem_singleton.mp hx']

/-- (b) **Digon contractions** ((I5)). A shortest directed cycle among the vertices with exactly
two in-neighbours in `R` is a piece: split it by whether a vertex's in-neighbour off the cycle
equals that of `f 0`. Outside vertices then have all their children in one part. -/
theorem i5Piece (hTT : TTFreeOn N R) (hL : ∀ v ∈ R, ∀ u ∈ N v, u ∉ L) {ℓ : ℕ}
    (c : DCyc N (R.filter (fun v => (N v ∩ R).card = 2)) ℓ) (hℓ : 2 ≤ ℓ)
    (hch : ∀ i j : Fin ℓ, c.f j ∈ N (c.f i) → j = idx c.pos (i.val + 1)) :
    Nonempty (PieceCert N (univ \ (R ∪ L)) (univ.image c.f)) := by
  have hCR : ∀ i, c.f i ∈ R := fun i => (mem_filter.mp (c.mem i)).1
  have hdeg2 : ∀ i, (N (c.f i) ∩ R).card = 2 := fun i => (mem_filter.mp (c.mem i)).2
  have hfC : ∀ i, c.f i ∈ univ.image c.f := fun i => mem_image_of_mem _ (mem_univ _)
  have hcp : ∀ i : Fin ℓ, c.f (idx c.pos (i.val + 1)) ∈ N (c.f i) := fun i => by
    have := c.arc i.val; rwa [idx_self] at this
  -- in-neighbours on the cycle are cycle parents
  have honC : ∀ (i : Fin ℓ) u, u ∈ N (c.f i) → u ∈ univ.image c.f →
      u = c.f (idx c.pos (i.val + 1)) := by
    intro i u hu huC
    obtain ⟨j, -, rfl⟩ := mem_image.mp huC
    rw [hch i j hu]
  -- in-neighbours in `R` off the cycle: exactly the designated parent
  have hoff : ∀ (i : Fin ℓ) u, u ∈ N (c.f i) → u ∈ R → u ∉ univ.image c.f →
      outPar N R (univ.image c.f) (c.f i) = some u := by
    intro i u hu huR huC
    cases hp : outPar N R (univ.image c.f) (c.f i) with
    | none => exact absurd (outPar_none hp hu huR) huC
    | some w =>
      obtain ⟨hw, hwR, hwC⟩ := outPar_some hp
      by_contra hwu
      have hwu' : w ≠ u := fun e => hwu (by rw [e])
      have h3 := three_le_card (s := N (c.f i) ∩ R) (mem_inter.mpr ⟨hcp i, hCR _⟩)
        (mem_inter.mpr ⟨hw, hwR⟩) (mem_inter.mpr ⟨hu, huR⟩)
        (by rintro rfl; exact hwC (hfC _)) (by rintro rfl; exact huC (hfC _)) hwu'
      rw [hdeg2 i] at h3
      omega
  -- the cycle child `f (ℓ-1)` of `f 0` has a different designated parent
  have hlast : c.f ⟨0, c.pos⟩ ∈ N (c.f ⟨ℓ - 1, by omega⟩) := by
    have := c.arc (ℓ - 1)
    rwa [show ℓ - 1 + 1 = ℓ by omega, show idx c.pos ℓ = ⟨0, c.pos⟩ from Fin.ext (by simp),
      idx_of_lt c.pos (by omega : ℓ - 1 < ℓ)] at this
  have hdiff : outPar N R (univ.image c.f) (c.f ⟨ℓ - 1, by omega⟩) ≠
      outPar N R (univ.image c.f) (c.f ⟨0, c.pos⟩) := by
    intro he
    cases hp : outPar N R (univ.image c.f) (c.f ⟨0, c.pos⟩) with
    | none =>
      have hsub : N (c.f ⟨0, c.pos⟩) ∩ R ⊆ {c.f (idx c.pos 1)} := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := mem_inter.mp hu
        rw [mem_singleton, honC _ u hu1 (outPar_none hp hu1 hu2)]
      have := card_le_card hsub
      rw [hdeg2, card_singleton] at this
      omega
    | some w =>
      rw [hp] at he
      obtain ⟨hw0, hwR, hwC⟩ := outPar_some hp
      obtain ⟨hw1, -, -⟩ := outPar_some he
      have hne01 : c.f ⟨0, c.pos⟩ ≠ c.f ⟨ℓ - 1, by omega⟩ := fun e => by
        have := congrArg Fin.val (c.inj e); simp at this; omega
      exact hTT w hwR _ (hCR _) _ (hCR _) (by rintro rfl; exact hwC (hfC _)) hne01
        (by rintro rfl; exact hwC (hfC _)) hw0 hlast hw1
  have hX : ∀ X ⊆ univ.image c.f, ∀ x ∈ X, ∃ k, c.f k = x := fun X hX x hx => by
    obtain ⟨k, -, rfl⟩ := mem_image.mp (hX hx); exact ⟨k, rfl⟩
  refine bdirPiece N (univ \ (R ∪ L)) (univ.image c.f)
    ((univ.image c.f).filter (fun v => outPar N R (univ.image c.f) v =
      outPar N R (univ.image c.f) (c.f ⟨0, c.pos⟩)))
    ((univ.image c.f).filter (fun v => ¬ outPar N R (univ.image c.f) v =
      outPar N R (univ.image c.f) (c.f ⟨0, c.pos⟩)))
    (disjoint_filter_filter_not _ _ _) (filter_union_filter_not_eq _ _)
    (c.acyclic_of_missing hch (hX _ (filter_subset _ _)) ⟨ℓ - 1, by omega⟩
      (by simp [hdiff]))
    (c.acyclic_of_missing hch (hX _ (filter_subset _ _)) ⟨0, c.pos⟩ (by simp))
    (outPar N R (univ.image c.f)) ?_ ?_ ?_
  · intro v hv u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hv
    by_cases huR : u ∈ R
    · by_cases huC : u ∈ univ.image c.f
      · exact Or.inr (Or.inl huC)
      · exact Or.inr (Or.inr (hoff i u hu huR huC))
    · exact Or.inl (by simp [huR, hL _ (hCR i) u hu])
  · intro v _ w hp
    obtain ⟨-, hwR, hwC⟩ := outPar_some hp
    exact ⟨by simp [hwR], hwC⟩
  · intro v hv v' hv' w h1 h2
    simp only [mem_filter, h1, h2, hv, hv', true_and]

end Pieces

/-- **One block.** Let the in-neighbours of the block `S` avoid the later vertices `L`, with no
transitive triangle inside `S` and the vertices with at least three in-neighbours in `S`
acyclic. A decomposition from the context `univ \ L` extends to one from `univ \ (R ∪ L)` for
every `R ⊆ S`. -/
theorem block_decomp (hloop : ∀ v, v ∉ N v) {S L : Finset V} (hSL : Disjoint S L)
    (hL : ∀ v ∈ S, ∀ u ∈ N v, u ∉ L) (hTT : TTFreeOn N S)
    (hT : IsAcyclicIn N (S.filter (fun v => 3 ≤ (N v ∩ S).card)))
    {q : List (Finset V)} (hq : Decomp N (univ \ L) q) :
    ∀ R ⊆ S, ∃ pcs, Decomp N (univ \ (R ∪ L)) pcs := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
    intro hRS
    have hRL : Disjoint R L := disjoint_of_subset_left hRS hSL
    have hLR : ∀ v ∈ R, ∀ u ∈ N v, u ∉ L := fun v hv => hL v (hRS hv)
    -- a nonempty certified piece `H ⊆ R` reduces `R` to `R \ H`
    have step : ∀ H, H ⊆ R → H.Nonempty → Nonempty (PieceCert N (univ \ (R ∪ L)) H) →
        ∃ pcs, Decomp N (univ \ (R ∪ L)) pcs := by
      intro H hHR hHne hP
      obtain ⟨rest, hrest⟩ := ih _ (sdiff_ssubset hHR hHne) (sdiff_subset.trans hRS)
      refine ⟨H :: rest, ?_⟩
      simp only [Decomp]
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' => ?_, hP, ?_⟩
      · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hx
        exact hx.1 (hHR hx')
      · have hHL : ∀ x ∈ H, x ∉ L := fun x hx hxL => Finset.disjoint_left.mp hRL (hHR hx) hxL
        have he : (univ \ (R ∪ L)) ∪ H = univ \ ((R \ H) ∪ L) := by
          ext x
          have h1 := hHL x
          have h2 : x ∈ H → x ∈ R := fun hx => hHR hx
          simp only [mem_union, mem_sdiff, mem_univ, true_and]
          tauto
        rw [he]; exact hrest
    by_cases ha : ∃ v ∈ R, (N v ∩ R).card ≤ 1
    · obtain ⟨v, hv, h1⟩ := ha
      exact step {v} (singleton_subset_iff.mpr hv) (singleton_nonempty v)
        (singlePiece hloop (hLR v hv) h1)
    have h2 : ∀ v ∈ R, 2 ≤ (N v ∩ R).card := fun v hv => by
      by_contra hcon; exact ha ⟨v, hv, by omega⟩
    by_cases hW : IsAcyclicIn N (R.filter (fun v => (N v ∩ R).card = 2))
    · -- (c) a 2-dicolouring: in-degree two versus in-degree at least three
      refine ⟨R :: q, ?_⟩
      simp only [Decomp]
      have he : (univ \ (R ∪ L)) ∪ R = univ \ L := by
        ext x
        have h1 : x ∈ R → x ∉ L := fun hx hxL => Finset.disjoint_left.mp hRL hx hxL
        simp only [mem_union, mem_sdiff, mem_univ, true_and]
        tauto
      refine ⟨Finset.disjoint_left.mpr fun x hx hx' => by simp [hx'] at hx, ?_, by rw [he]; exact hq⟩
      refine bdirPiece N (univ \ (R ∪ L)) R (R.filter (fun v => 3 ≤ (N v ∩ R).card))
        (R.filter (fun v => (N v ∩ R).card = 2)) ?_ ?_ ?_ hW (fun _ => none) ?_ ?_ ?_
      · rw [Finset.disjoint_left]; intro x hx hx'
        simp only [mem_filter] at hx hx'; omega
      · ext x; simp only [mem_union, mem_filter]
        constructor
        · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
        · intro hx
          have := h2 x hx
          by_cases h3 : 3 ≤ (N x ∩ R).card
          · exact Or.inl ⟨hx, h3⟩
          · exact Or.inr ⟨hx, by omega⟩
      · exact hT.mono fun x hx => by
          simp only [mem_filter] at hx ⊢
          exact ⟨hRS hx.1, hx.2.trans (card_le_card (inter_subset_inter_left hRS))⟩
      · intro v hv u hu
        by_cases huR : u ∈ R
        · exact Or.inr (Or.inl huR)
        · exact Or.inl (by simp [huR, hLR v hv u hu])
      · intro v _ w h; simp at h
      · intro v _ v' _ w h; simp at h
    · -- (b) a shortest directed cycle among the in-degree-two vertices
      obtain ⟨T, hTW, hTne, hTsrc⟩ : ∃ T ⊆ R.filter (fun v => (N v ∩ R).card = 2),
          T.Nonempty ∧ ∀ v ∈ T, ∃ u ∈ N v, u ∈ T := by
        by_contra hcon
        apply hW
        intro T hT hne
        by_contra hno
        exact hcon ⟨T, hT, hne, fun v hv => by
          by_contra hv'
          exact hno ⟨v, hv, fun u hu huT => hv' ⟨u, hu, huT⟩⟩⟩
      obtain ⟨ℓ₀, hℓ₀⟩ := exists_hasDCyc_of_sourceless hloop hTne hTsrc
      have hex : ∃ ℓ, HasDCyc N (R.filter (fun v => (N v ∩ R).card = 2)) ℓ :=
        ⟨ℓ₀, hℓ₀.mono hTW⟩
      classical
      obtain ⟨ℓ, ⟨hℓ, ⟨c⟩⟩, hmin⟩ : ∃ ℓ, HasDCyc N (R.filter (fun v => (N v ∩ R).card = 2)) ℓ ∧
          ∀ ℓ', HasDCyc N (R.filter (fun v => (N v ∩ R).card = 2)) ℓ' → ℓ ≤ ℓ' :=
        ⟨Nat.find hex, Nat.find_spec hex, fun ℓ' h => Nat.find_min' hex h⟩
      exact step (univ.image c.f)
        (fun x hx => by obtain ⟨i, -, rfl⟩ := mem_image.mp hx; exact (mem_filter.mp (c.mem i)).1)
        ⟨c.f ⟨0, c.pos⟩, mem_image_of_mem _ (mem_univ _)⟩
        (i5Piece (hTT.mono hRS) hLR c hℓ (fun i j h => c.chordless hloop hmin h))

/-- An ordered list of blocks (sources first): each block is disjoint from the later ones, its
in-neighbours lie in earlier blocks or in itself, and inside it there is no transitive triangle
and the vertices with at least three in-neighbours in the block induce an acyclic
sub-relation. -/
def BlockOrder (N : V → Finset V) : List (Finset V) → Prop
  | [] => True
  | S :: rest => Disjoint S (rest.foldr (· ∪ ·) ∅) ∧
      (∀ v ∈ S, ∀ u ∈ N v, u ∉ rest.foldr (· ∪ ·) ∅) ∧ TTFreeOn N S ∧
      IsAcyclicIn N (S.filter (fun v => 3 ≤ (N v ∩ S).card)) ∧ BlockOrder N rest

theorem blocks_decomp (hloop : ∀ v, v ∉ N v) : ∀ bs : List (Finset V), BlockOrder N bs →
    ∃ q, Decomp N (univ \ bs.foldr (· ∪ ·) ∅) q := by
  intro bs
  induction bs with
  | nil => intro _; exact ⟨[], by simp [Decomp]⟩
  | cons S rest ih =>
    intro hB
    obtain ⟨hSL, hL, hTT, hT, hrest⟩ := hB
    obtain ⟨q, hq⟩ := ih hrest
    exact block_decomp hloop hSL hL hTT hT hq S (subset_refl S)

/-- **Corollary T_int, block form.** If the vertex set is covered by an ordered list of blocks as
in `BlockOrder`, the weighted half bound holds. Corollary T_int in its component form
(`rateBound_Tint`, in `HalfRate.Components`) applies it to blocks made of strongly connected
components. -/
theorem rateBound_blocks (hloop : ∀ v, v ∉ N v) {bs : List (Finset V)} (hB : BlockOrder N bs)
    (hcov : bs.foldr (· ∪ ·) ∅ = univ) : RateBound N (1 / 2) := by
  obtain ⟨q, hq⟩ := blocks_decomp hloop bs hB
  rw [hcov, sdiff_self] at hq
  exact rateBound_of_decomp hq

/-- **Theorem T.** A loopless recovery relation without transitive triangles whose vertices
with at least three in-neighbours induce an acyclic sub-relation satisfies the weighted half
bound. No bound on in- or out-degrees is needed. (The one-block case.) -/
theorem rateBound_thmT (hloop : ∀ v, v ∉ N v) (hTT : TTFree N)
    (hT : IsAcyclicIn N (univ.filter (fun v => 3 ≤ (N v).card))) : RateBound N (1 / 2) := by
  refine rateBound_blocks hloop (bs := [univ])
    ⟨by simp, by simp, fun x _ y _ z _ => hTT x y z, by simpa using hT, trivial⟩ (by simp)

/-- Storage codes under the hypotheses of Theorem T have `|C|² ≤ |α|^|V|`. -/
theorem card_sq_le_thmT {α : Type*} [Fintype α] [Nonempty α] (hloop : ∀ v, v ∉ N v)
    (hTT : TTFree N) (hT : IsAcyclicIn N (univ.filter (fun v => 3 ≤ (N v).card)))
    {C : Finset (V → α)} (hC : IsStorageCode N C) :
    C.card ^ 2 ≤ Fintype.card α ^ Fintype.card V :=
  card_sq_le_of_rateBound_half (rateBound_thmT hloop hTT hT) hC

end HalfRate
