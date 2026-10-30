import MergeDepth.PairedDistance
import MergeDepth.BlockDag

/-!
# Realizing a matching of incidences (Lemma 4.9)

The relaxation has an input tape `none`, an output tape `some none` and work tapes `some (some j)`
(`Tp k`), one register, and `2w - 1` heads on every tape, which at tick `u` occupy the cells
`z c u + i - (w - 1)`, `i < 2w - 1`, around a reference walk `z c` of the tape (`nbhd`); so they cover
the whole block `⌊z c u / w⌋` of `w` cells (`nbhd_open`). The coarse work walks are
`s j = ⌊z (work j)/w⌋`, and the block DAG is the dependency DAG `DepStep s T` of the coarse walks
(Lemma 4.5(a), `blockStep_iff`).

A label follows a path `o = t₀ → t₁ → ⋯ → t_ℓ` of the block DAG read forwards in time
(`pathLoc`): it waits in its input cell until tick `t_ℓ`, then in the slot of each edge (`edgeSlot`:
the register for a state edge, the base cell `w s_j(t)` of tape `j` for a long hop of `s_j`), and from
tick `o` on in its output cell. `realize_paths` checks that this is a run (`IsRun`): transfers happen
only at the vertices of the path, between slots that are open there, and the occupancy at every
placement is at most `w B`, `B = ∑_{h ≤ D} (k + 1)^h`, if the paths have at most `D` edges, their
outputs `r j` are distinct cells of the output block of the path's first vertex and their inputs are
distinct (`card_paths_through_le`, which counts the paths through a vertex by the times from which it
is reachable, using the in-degree bound `card_blockIn_le`).

* `realizes_cone`: **Lemma 4.9.** The cone relation `N_Γ` of a genie of full depth at most `D`
  (`coneRel`) has the realization property with `K = (k + 2)(2w - 1)` heads, one register and
  occupancy `w B`.
* `realizes_ball`: the same for relations inside the balls `B^{D'}` of an oblivious schedule, at
  scale `w = 1` (the realization step of Lemma 3.14(a)).
-/

namespace MergeDepth

open Finset BoundedNesting

/-- The tapes: `none` is the input tape, `some none` the output tape, `some (some j)` work tape `j`. -/
abbrev Tp (k : ℕ) := Option (Option (Fin k))

variable {k : ℕ}

/-! ### Heads around reference walks -/

/-- The head schedule: the `2w - 1` heads of tape `c` sit at `z c u + i - (w - 1)`, `i < 2w - 1`. -/
def nbhd (w : ℕ) (z : Tp k → ℕ → ℤ) (u : ℕ) (h : Tp k × Fin (2 * w - 1)) : ℤ :=
  z h.1 u + (h.2 : ℕ) - ((w : ℤ) - 1)

/-- The heads of a tape cover the block of its reference walk. -/
theorem nbhd_open {w : ℕ} (hw : 1 ≤ w) (z : Tp k → ℕ → ℤ) (u : ℕ) {c : Tp k} {x : ℤ}
    (hx : x / w = z c u / w) :
    SlotOpen (ρ := 1) (Prod.fst : Tp k × Fin (2 * w - 1) → Tp k) (nbhd w z u) (.inl (c, x)) := by
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  obtain ⟨a1, a2⟩ := block_bounds hw' x
  obtain ⟨b1, b2⟩ := block_bounds hw' (z c u)
  rw [hx] at a1 a2
  have hi0 : 0 ≤ x - z c u + (w - 1) := by linarith
  have hi1 : x - z c u + (w - 1) < 2 * w - 1 := by linarith
  refine ⟨(c, ⟨(x - z c u + (w - 1)).toNat, by omega⟩), rfl, ?_⟩
  simp only [nbhd]
  rw [Int.toNat_of_nonneg hi0]
  ring

theorem nbhd_move {w : ℕ} {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c)) (u : ℕ)
    (h : Tp k × Fin (2 * w - 1)) : |nbhd w z (u + 1) h - nbhd w z u h| ≤ 1 := by
  simp only [nbhd]
  have := hz h.1 u
  rwa [show z h.1 (u + 1) + ((h.2 : ℕ) : ℤ) - ((w : ℤ) - 1) - (z h.1 u + ((h.2 : ℕ) : ℤ) - ((w : ℤ) - 1))
    = z h.1 (u + 1) - z h.1 u by ring]

/-! ### The block DAG -/

theorem depStep_lt_lt {s : Fin k → ℕ → ℤ} {T a b : ℕ} (h : DepStep s T a b) : b < a ∧ a < T := by
  rcases h with ⟨h1, h2⟩ | h
  · exact ⟨by omega, h2⟩
  · obtain ⟨η, hη, he⟩ := mem_image.mp h
    obtain ⟨hl, hT, -, -⟩ := mem_allHops.mp hη
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨by omega, hT⟩

theorem depStep_hop {s : Fin k → ℕ → ℤ} {T a b : ℕ} (h : DepStep s T a b) (hne : b + 1 ≠ a) :
    ∃ j, IsHop (s j) T b a := by
  rcases h with ⟨h1, -⟩ | h
  · exact absurd h1 hne
  · obtain ⟨η, hη, he⟩ := mem_image.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨η.1, mem_allHops.mp hη⟩

theorem isDepPath_lt {s : Fin k → ℕ → ℤ} {T : ℕ} :
    ∀ (a : ℕ) (π : List ℕ), IsDepPath s T (a :: π) → ∀ v ∈ π, v < a
  | _, [], _, v, hv => absurd hv List.not_mem_nil
  | a, b :: π, hp, v, hv => by
    obtain ⟨hab, hp'⟩ := hp
    have hba := (depStep_lt_lt hab).1
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hba
    · exact (isDepPath_lt b π hp' v hv).trans hba

/-! ### Trajectories along paths -/

section PathLoc

variable {α : Type*} (σ : ℕ → ℕ → α) (pin pout : α)

/-- The slot of a label that follows the path `π`, read forwards in time, before the transfers of
tick `u`: its input slot up to the last vertex, the slot `σ a b` of the edge `a → b` with
`b < u ≤ a`, and its output slot after the first vertex. -/
def pathLoc : List ℕ → ℕ → α
  | [], _ => pout
  | [a], u => if a < u then pout else pin
  | a :: b :: π, u => if a < u then pout else if b < u then σ a b else pathLoc (b :: π) u

theorem pathLoc_zero : ∀ (a : ℕ) (π : List ℕ), pathLoc σ pin pout (a :: π) 0 = pin
  | a, [] => by simp [pathLoc]
  | a, b :: π => by simp only [pathLoc, Nat.not_lt_zero, ↓reduceIte]; exact pathLoc_zero b π

theorem pathLoc_of_lt {a u : ℕ} (π : List ℕ) (h : a < u) : pathLoc σ pin pout (a :: π) u = pout := by
  cases π with
  | nil => simp [pathLoc, h]
  | cons b π => simp [pathLoc, h]

variable {s : Fin k → ℕ → ℤ} {T : ℕ}

/-- Between the vertices of the path the slot does not change. -/
theorem pathLoc_succ :
    ∀ (π : List ℕ) (u : ℕ), IsDepPath s T π → u ∉ π →
      pathLoc σ pin pout π (u + 1) = pathLoc σ pin pout π u
  | [], _, _, _ => rfl
  | [a], u, _, hu => by
    have : a ≠ u := fun h => hu (by simp [h])
    simp only [pathLoc]
    by_cases h1 : a < u
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]
  | a :: b :: π, u, hp, hu => by
    obtain ⟨-, hp'⟩ := hp
    have hau : a ≠ u := fun h => hu (by simp [h])
    have hbu : u ∉ b :: π := fun h => hu (List.mem_cons_of_mem a h)
    have hbu' : b ≠ u := fun h => hbu (by simp [h])
    simp only [pathLoc]
    by_cases h1 : a < u
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega : ¬ a < u + 1)]
      by_cases h2 : b < u
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega : ¬ b < u + 1)]
        exact pathLoc_succ (b :: π) u hp' hbu

/-- At a vertex `u`, before its transfers, a label is in its input slot (if `u` is the last vertex)
or in the slot of the edge leaving `u`. -/
theorem pathLoc_at :
    ∀ (a : ℕ) (π : List ℕ) (u : ℕ), IsDepPath s T (a :: π) → u ∈ a :: π →
      (pathLoc σ pin pout (a :: π) u = pin ∧ u = (a :: π).getLastD a) ∨
        ∃ b, DepStep s T u b ∧ pathLoc σ pin pout (a :: π) u = σ u b
  | a, [], u, _, hu => by
    left
    have : u = a := by simpa using hu
    subst this
    simp [pathLoc]
  | a, b :: π, u, hp, hu => by
    obtain ⟨hab, hp'⟩ := hp
    have hba := (depStep_lt_lt hab).1
    rcases List.mem_cons.mp hu with rfl | hu'
    · right
      refine ⟨b, hab, ?_⟩
      simp [pathLoc, hba]
    · have hub : u ≤ b := by
        rcases List.mem_cons.mp hu' with rfl | hu''
        · exact le_rfl
        · exact (isDepPath_lt b π hp' u hu'').le
      have e : pathLoc σ pin pout (a :: b :: π) u = pathLoc σ pin pout (b :: π) u := by
        simp only [pathLoc]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [e, show (a :: b :: π).getLastD a = (b :: π).getLastD b by simp only [List.getLastD_cons]]
      exact pathLoc_at b π u hp' hu'

/-- At a vertex `u`, after its transfers, a label is in its output slot (if `u` is the first vertex)
or in the slot of the edge entering `u`. -/
theorem pathLoc_at_succ :
    ∀ (a : ℕ) (π : List ℕ) (u : ℕ), IsDepPath s T (a :: π) → u ∈ a :: π →
      (pathLoc σ pin pout (a :: π) (u + 1) = pout ∧ u = a) ∨
        ∃ a', DepStep s T a' u ∧ pathLoc σ pin pout (a :: π) (u + 1) = σ a' u
  | a, [], u, _, hu => by
    left
    have : u = a := by simpa using hu
    subst this
    exact ⟨pathLoc_of_lt σ pin pout [] (Nat.lt_succ_self u), rfl⟩
  | a, b :: π, u, hp, hu => by
    obtain ⟨hab, hp'⟩ := hp
    have hba := (depStep_lt_lt hab).1
    rcases List.mem_cons.mp hu with rfl | hu'
    · left
      exact ⟨pathLoc_of_lt σ pin pout _ (Nat.lt_succ_self u), rfl⟩
    · have hua : u < a := by
        rcases List.mem_cons.mp hu' with rfl | hu''
        · exact hba
        · exact (isDepPath_lt b π hp' u hu'').trans hba
      rcases List.mem_cons.mp hu' with rfl | hu''
      · right
        refine ⟨a, hab, ?_⟩
        simp only [pathLoc]
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      · have hub : u < b := isDepPath_lt b π hp' u hu''
        have e : pathLoc σ pin pout (a :: b :: π) (u + 1) = pathLoc σ pin pout (b :: π) (u + 1) := by
          simp only [pathLoc]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [e]
        rcases pathLoc_at_succ b π u hp' hu' with ⟨-, hb⟩ | h
        · omega
        · exact Or.inr h

/-- At every tick a label is in its input slot, in its output slot, or in the slot of the edge
`a → b` of its path with `b < u ≤ a`. -/
theorem pathLoc_cases :
    ∀ (a : ℕ) (π : List ℕ) (u : ℕ), IsDepPath s T (a :: π) →
      pathLoc σ pin pout (a :: π) u = pin ∨ pathLoc σ pin pout (a :: π) u = pout ∨
        ∃ a' b, a' ∈ a :: π ∧ DepStep s T a' b ∧ b < u ∧ u ≤ a' ∧
          pathLoc σ pin pout (a :: π) u = σ a' b
  | a, [], u, _ => by
    simp only [pathLoc]
    by_cases h : a < u
    · right; left; rw [ite_eq_left h]
    · left; rw [ite_eq_right h]
  | a, b :: π, u, hp => by
    obtain ⟨hab, hp'⟩ := hp
    by_cases h1 : a < u
    · right; left; exact pathLoc_of_lt σ pin pout _ h1
    by_cases h2 : b < u
    · right; right
      refine ⟨a, b, List.mem_cons_self .., hab, h2, by omega, ?_⟩
      simp only [pathLoc]
      rw [ite_eq_right h1, ite_eq_left h2]
    · have e : pathLoc σ pin pout (a :: b :: π) u = pathLoc σ pin pout (b :: π) u := by
        simp only [pathLoc]
        rw [ite_eq_right h1, ite_eq_right h2]
      rw [e]
      rcases pathLoc_cases b π u hp' with h | h | ⟨a', b', ha', h'⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨a', b', List.mem_cons_of_mem a ha', h'⟩)

end PathLoc

/-! ### Edge slots -/

open Classical in
/-- The slot of an edge `a → b` of the block DAG: the register for a state edge, and for a long hop
`(b, a)` of the coarse walk `s j` the base cell `w s_j(a)` of work tape `j`. -/
noncomputable def edgeSlot (w : ℕ) (s : Fin k → ℕ → ℤ) (T a b : ℕ) : Slot (Tp k) 1 :=
  if b + 1 = a then .inr 0
  else if h : ∃ j, IsHop (s j) T b a then .inl (some (some h.choose), w * s h.choose a)
  else .inr 0

theorem edgeSlot_cases (w : ℕ) (s : Fin k → ℕ → ℤ) (T a b : ℕ) :
    edgeSlot w s T a b = .inr 0 ∨
      ∃ j, IsHop (s j) T b a ∧ edgeSlot w s T a b = .inl (some (some j), w * s j a) := by
  unfold edgeSlot
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr ⟨h2.choose, h2.choose_spec, rfl⟩
  · exact Or.inl rfl

theorem edgeSlot_reg {w : ℕ} {s : Fin k → ℕ → ℤ} {T a b : ℕ} (hab : DepStep s T a b)
    (h : edgeSlot w s T a b = .inr 0) : b + 1 = a := by
  by_contra hne
  unfold edgeSlot at h
  rw [ite_eq_right hne, dite_eq_left (depStep_hop hab hne)] at h
  exact Sum.inl_ne_inr h

/-- The slot of an edge is open at both of its ends. -/
theorem edgeSlot_open {w : ℕ} (hw : 1 ≤ w) {z : Tp k → ℕ → ℤ} {T a b : ℕ}
    (hab : DepStep (fun j => skel w (z (some (some j)))) T a b) {u : ℕ} (hu : u = a ∨ u = b) :
    SlotOpen (Prod.fst : Tp k × Fin (2 * w - 1) → Tp k) (nbhd w z u)
      (edgeSlot w (fun j => skel w (z (some (some j)))) T a b) := by
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  rcases edgeSlot_cases w (fun j => skel w (z (some (some j)))) T a b with h | ⟨j, hj, h⟩
  · rw [h]; trivial
  · rw [h]
    apply nbhd_open hw
    rw [Int.mul_ediv_cancel_left _ hw'.ne']
    rcases hu with rfl | rfl
    · rfl
    · exact hj.2.2.1

/-! ### Paths through a vertex -/

open Classical in
/-- The times below `T` from which `t` is reached by a dependency path of exactly `h` edges. -/
noncomputable def levelSet (s : Fin k → ℕ → ℤ) (T h t : ℕ) : Finset ℕ :=
  (range T).filter fun o => ∃ π : List ℕ, IsDepPath s T (o :: π) ∧ π.length = h ∧
    (o :: π).getLastD o = t

open Classical in
/-- In-degrees at most `k + 1` give at most `(k + 1)^h` such times. -/
theorem card_levelSet_le (s : Fin k → ℕ → ℤ) (T : ℕ) : ∀ h t, (levelSet s T h t).card ≤ (k + 1) ^ h
  | 0, t => by
    refine (card_le_card (show levelSet s T 0 t ⊆ {t} from fun o ho => ?_)).trans (by simp)
    obtain ⟨-, π, -, hπ, ht⟩ := mem_filter.mp ho
    rw [List.length_eq_zero_iff] at hπ
    subst hπ
    simp only [List.getLastD_cons, List.getLastD_nil] at ht
    exact mem_singleton.mpr ht
  | h + 1, t => by
    classical
    have hsub : levelSet s T (h + 1) t ⊆
        (levelSet s T h t).biUnion fun o' => (range T).filter (BlockStep s T · o') := by
      intro o ho
      obtain ⟨hoT, π, hπ, hlen, ht⟩ := mem_filter.mp ho
      cases π with
      | nil => simp at hlen
      | cons o' π =>
        obtain ⟨hstep, hπ'⟩ := hπ
        refine mem_biUnion.mpr ⟨o', mem_filter.mpr ⟨?_, π, hπ', by simpa using hlen, ?_⟩, ?_⟩
        · exact mem_range.mpr ((depStep_lt_lt hstep).1.trans (mem_range.mp hoT))
        · simp only [List.getLastD_cons] at ht ⊢; exact ht
        · exact mem_filter.mpr ⟨hoT, (blockStep_iff s T o o').mpr hstep⟩
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ o' ∈ levelSet s T h t, ((range T).filter (BlockStep s T · o')).card
        ≤ ∑ _o' ∈ levelSet s T h t, (k + 1) := sum_le_sum fun o' _ => card_blockIn_le s T o'
      _ = (levelSet s T h t).card * (k + 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ (k + 1) ^ h * (k + 1) := Nat.mul_le_mul_right _ (card_levelSet_le s T h t)
      _ = (k + 1) ^ (h + 1) := by ring

/-- A vertex of a dependency path is reached from its first vertex along a prefix. -/
theorem exists_prefix {s : Fin k → ℕ → ℤ} {T : ℕ} :
    ∀ (a : ℕ) (π : List ℕ) (t : ℕ), IsDepPath s T (a :: π) → t ∈ a :: π →
      ∃ π', IsDepPath s T (a :: π') ∧ π'.length ≤ π.length ∧ (a :: π').getLastD a = t
  | a, [], t, _, ht => ⟨[], trivial, le_rfl, by
      simp only [List.getLastD_cons, List.getLastD_nil]; exact (List.mem_singleton.mp ht).symm⟩
  | a, b :: π, t, hp, ht => by
    rcases List.mem_cons.mp ht with rfl | ht'
    · exact ⟨[], trivial, Nat.zero_le _, rfl⟩
    · obtain ⟨hab, hp'⟩ := hp
      obtain ⟨π', h1, h2, h3⟩ := exists_prefix b π t hp' ht'
      refine ⟨b :: π', ⟨hab, h1⟩, by simp only [List.length_cons]; omega, ?_⟩
      simp only [List.getLastD_cons] at h3 ⊢
      exact h3

/-- **Paths through a vertex.** Paths of at most `D` edges whose first vertices `o j < T` carry distinct
outputs `r j` in the blocks `⌊z_out(o j)/w⌋` pass through every vertex at most `w B` times,
`B = ∑_{h ≤ D} (k + 1)^h`. -/
theorem card_paths_through_le {w : ℕ} (hw : 1 ≤ w) (s : Fin k → ℕ → ℤ) (zo : ℕ → ℤ) {T D m : ℕ}
    (o : Fin m → ℕ) (π : Fin m → List ℕ) (r : Fin m → ℤ) (hr : Function.Injective r)
    (hpath : ∀ j, IsDepPath s T (o j :: π j)) (hlen : ∀ j, (π j).length ≤ D) (hoT : ∀ j, o j < T)
    (hout : ∀ j, r j / w = zo (o j) / w) (t : ℕ) :
    (univ.filter fun j => t ∈ o j :: π j).card ≤ w * ∑ h ∈ range (D + 1), (k + 1) ^ h := by
  classical
  have hw' : (0 : ℤ) < w := by exact_mod_cast hw
  set Back := (range (D + 1)).biUnion fun h => levelSet s T h t
  have hsub : (univ.filter fun j => t ∈ o j :: π j) ⊆ univ.filter fun j => o j ∈ Back := by
    intro j hj
    obtain ⟨π', h1, h2, h3⟩ := exists_prefix (o j) (π j) t (hpath j) (mem_filter.mp hj).2
    refine mem_filter.mpr ⟨mem_univ _, mem_biUnion.mpr ⟨π'.length, ?_, ?_⟩⟩
    · exact mem_range.mpr (by have := hlen j; omega)
    · exact mem_filter.mpr ⟨mem_range.mpr (hoT j), π', h1, rfl, h3⟩
  have hper : ∀ o' ∈ Back, ((univ.filter fun j => o j ∈ Back).filter fun j => o j = o').card ≤ w := by
    intro o' _
    set q := zo o' / w
    have hmaps : ∀ j ∈ (univ.filter fun j => o j ∈ Back).filter (fun j => o j = o'),
        r j ∈ Ico (w * q) (w * q + w) := by
      intro j hj
      have hjo := (mem_filter.mp hj).2
      obtain ⟨b1, b2⟩ := block_bounds hw' (r j)
      rw [hout j, hjo] at b1 b2
      exact mem_Ico.mpr ⟨b1, b2⟩
    refine (card_le_card_of_injOn r hmaps (hr.injOn)).trans ?_
    simp
  have hBack : Back.card ≤ ∑ h ∈ range (D + 1), (k + 1) ^ h :=
    card_biUnion_le.trans (sum_le_sum fun h _ => card_levelSet_le s T h t)
  calc (univ.filter fun j => t ∈ o j :: π j).card
      ≤ (univ.filter fun j => o j ∈ Back).card := card_le_card hsub
    _ = ∑ o' ∈ Back, ((univ.filter fun j => o j ∈ Back).filter fun j => o j = o').card :=
        card_eq_sum_card_fiberwise fun j hj => (mem_filter.mp hj).2
    _ ≤ ∑ _o' ∈ Back, w := sum_le_sum hper
    _ = Back.card * w := by rw [sum_const, smul_eq_mul]
    _ ≤ w * ∑ h ∈ range (D + 1), (k + 1) ^ h := by rw [mul_comm]; exact Nat.mul_le_mul_left w hBack

/-! ### The realization -/

/-- **The realization along paths.** Let the reference walks `z c` be walks, let label `j` follow the
dependency path `o j :: π j` of the coarse work walks, of at most `D` edges, with `o j < T`, from the
input cell `p j` in the input block at its last vertex to the output cell `r j` in the output block
at its first vertex, the `p j` and the `r j` distinct. Then these trajectories form a run of `T`
ticks with the heads `nbhd w z` and occupancy at most `w B`, `B = ∑_{h ≤ D} (k + 1)^h`. -/
theorem realize_paths {w : ℕ} (hw : 1 ≤ w) {z : Tp k → ℕ → ℤ} (hz : ∀ c, IsWalk (z c))
    {T D m : ℕ} (o : Fin m → ℕ) (π : Fin m → List ℕ) (p r : Fin m → ℤ)
    (hpath : ∀ j, IsDepPath (fun i => skel w (z (some (some i)))) T (o j :: π j))
    (hlen : ∀ j, (π j).length ≤ D) (hoT : ∀ j, o j < T)
    (hin : ∀ j, p j / w = z none ((o j :: π j).getLastD (o j)) / w)
    (hout : ∀ j, r j / w = z (some none) (o j) / w)
    (hp : Function.Injective p) (hr : Function.Injective r) :
    ∃ loc : ℕ → Fin m → Slot (Tp k) 1,
      IsRun (Prod.fst : Tp k × Fin (2 * w - 1) → Tp k) (nbhd w z) loc T
          (w * ∑ h ∈ range (D + 1), (k + 1) ^ h) ∧
        (∀ j, loc 0 j = .inl (none, p j)) ∧ ∀ j, loc T j = .inl (some none, r j) := by
  classical
  set s : Fin k → ℕ → ℤ := fun i => skel w (z (some (some i)))
  set B := ∑ h ∈ range (D + 1), (k + 1) ^ h
  let loc : ℕ → Fin m → Slot (Tp k) 1 := fun u j =>
    pathLoc (edgeSlot w s T) (.inl (none, p j)) (.inl (some none, r j)) (o j :: π j) u
  have hB : 1 ≤ w * B := by
    have : 1 ≤ B := by
      have := single_le_sum (f := fun h => (k + 1) ^ h) (fun _ _ => Nat.zero_le _)
        (mem_range.mpr (Nat.succ_pos D) : 0 ∈ range (D + 1))
      simpa [B] using this
    nlinarith
  have hthrough := card_paths_through_le hw s (z (some none)) o π r hr hpath hlen hoT hout
  refine ⟨loc, ⟨fun u _ h => nbhd_move hz u h, ?_, ?_⟩, fun j => pathLoc_zero (edgeSlot w s T) _ _ _ _,
    fun j => pathLoc_of_lt (edgeSlot w s T) _ _ _ (hoT j)⟩
  · -- transfers happen at path vertices, between open slots
    intro u _ j hne
    have hmem : u ∈ o j :: π j := by
      by_contra hu
      exact hne (pathLoc_succ (edgeSlot w s T) _ _ _ u (hpath j) hu)
    constructor
    · rcases pathLoc_at (edgeSlot w s T) (.inl (none, p j)) (.inl (some none, r j)) (o j) (π j) u (hpath j) hmem
        with ⟨h1, h2⟩ | ⟨b, hb, h1⟩
      · simp only [loc]; rw [h1]
        exact nbhd_open hw z u (by rw [hin j, h2])
      · simp only [loc]; rw [h1]
        exact edgeSlot_open hw hb (Or.inl rfl)
    · rcases pathLoc_at_succ (edgeSlot w s T) (.inl (none, p j)) (.inl (some none, r j)) (o j) (π j) u (hpath j)
        hmem with ⟨h1, h2⟩ | ⟨a', ha', h1⟩
      · simp only [loc]; rw [h1]
        exact nbhd_open hw z u (by rw [hout j, h2])
      · simp only [loc]; rw [h1]
        exact edgeSlot_open hw ha' (Or.inr rfl)
  · -- occupancy
    intro u _ sl
    have hcase := fun j => pathLoc_cases (edgeSlot w s T) (.inl (none, p j)) (.inl (some none, r j)) (o j) (π j) u
      (hpath j)
    rcases sl with ⟨c, x⟩ | reg
    · rcases c with _ | _ | i
      · -- an input cell holds at most its own label
        refine (card_le_one.mpr fun j hj j' hj' => ?_).trans hB
        have key : ∀ j, loc u j = .inl (none, x) → p j = x := by
          intro j hj
          rcases hcase j with h | h | ⟨a', b, -, hab, -, -, h⟩
          · simp only [loc] at hj; rw [h] at hj; simpa using hj
          · simp only [loc] at hj; rw [h] at hj; simp at hj
          · simp only [loc] at hj; rw [h] at hj
            rcases edgeSlot_cases w s T a' b with h' | ⟨i, -, h'⟩ <;> rw [h'] at hj <;> simp at hj
        exact hp ((key j (mem_filter.mp hj).2).trans (key j' (mem_filter.mp hj').2).symm)
      · -- an output cell holds at most its own label
        refine (card_le_one.mpr fun j hj j' hj' => ?_).trans hB
        have key : ∀ j, loc u j = .inl (some none, x) → r j = x := by
          intro j hj
          rcases hcase j with h | h | ⟨a', b, -, hab, -, -, h⟩
          · simp only [loc] at hj; rw [h] at hj; simp at hj
          · simp only [loc] at hj; rw [h] at hj; simpa using hj
          · simp only [loc] at hj; rw [h] at hj
            rcases edgeSlot_cases w s T a' b with h' | ⟨i, -, h'⟩ <;> rw [h'] at hj <;> simp at hj
        exact hr ((key j (mem_filter.mp hj).2).trans (key j' (mem_filter.mp hj').2).symm)
      · -- a base cell holds labels of one hop, which pass through its end
        rcases (univ.filter fun j => loc u j = .inl (some (some i), x)).eq_empty_or_nonempty
          with he | ⟨j₀, hj₀⟩
        · rw [he]; exact Nat.zero_le _
        have key : ∀ j, loc u j = .inl (some (some i), x) →
            ∃ a' b, a' ∈ o j :: π j ∧ IsHop (s i) T b a' ∧ b < u ∧ u ≤ a' ∧ x = w * s i a' := by
          intro j hj
          rcases hcase j with h | h | ⟨a', b, ha', hab, hbu, hua, h⟩
          · simp only [loc] at hj; rw [h] at hj; simp at hj
          · simp only [loc] at hj; rw [h] at hj; simp at hj
          · simp only [loc] at hj; rw [h] at hj
            rcases edgeSlot_cases w s T a' b with h' | ⟨i', hi', h'⟩ <;> rw [h'] at hj
            · simp at hj
            · simp only [Sum.inl.injEq, Prod.mk.injEq, Option.some.injEq] at hj
              obtain ⟨rfl, rfl⟩ := hj
              exact ⟨a', b, ha', hi', hbu, hua, rfl⟩
        obtain ⟨a₀, b₀, -, hop₀, hb₀, ha₀, hx₀⟩ := key j₀ (mem_filter.mp hj₀).2
        refine (card_le_card fun j hj => ?_).trans (hthrough a₀)
        obtain ⟨a', b, ha', hop, hbu, hua, hx⟩ := key j (mem_filter.mp hj).2
        have hw' : (0 : ℤ) < w := by exact_mod_cast hw
        have hsa : s i a' = s i a₀ := by
          have := hx.symm.trans hx₀
          exact Int.eq_of_mul_eq_mul_left hw'.ne' this
        have hsb : s i b = s i b₀ := by
          rw [← hop.2.2.1, ← hop₀.2.2.1, hsa]
        have := hop_unique hop hop₀ hsb ⟨hbu, hua⟩ ⟨hb₀, ha₀⟩
        rw [← this.2]
        exact mem_filter.mpr ⟨mem_univ _, ha'⟩
    · -- the register holds labels of one state edge, which pass through its end `u`
      refine (card_le_card fun j hj => ?_).trans (hthrough u)
      have hj := (mem_filter.mp hj).2
      rcases hcase j with h | h | ⟨a', b, ha', hab, hbu, hua, h⟩
      · simp only [loc] at hj; rw [h] at hj; simp at hj
      · simp only [loc] at hj; rw [h] at hj; simp at hj
      · simp only [loc] at hj; rw [h] at hj
        have hreg : edgeSlot w s T a' b = .inr 0 := by rw [hj]; exact congrArg Sum.inr (Subsingleton.elim _ _)
        have := edgeSlot_reg hab hreg
        have : u = a' := by omega
        subst this
        exact mem_filter.mpr ⟨mem_univ _, ha'⟩

end MergeDepth
