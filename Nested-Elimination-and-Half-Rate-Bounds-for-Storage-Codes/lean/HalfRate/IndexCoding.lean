import HalfRate.Matching

/-!
# Index coding

An index code for side information `N` broadcasts a message from which every vertex `v`, knowing
the symbols on `N v`, recovers its own symbol. The words sharing a message form a storage code
(`IndexCode.isStorageCode_fibre`). Hence on triangle-free graphs of maximum degree three every
index code needs `log |M| ≥ (|V| − ν*) log |α|` (`log_card_message_ge`), and over every alphabet
`β × β` with `β` a finite additive group this is attained (`exists_indexCode`, which holds on
every graph): broadcast, along a double-cover matching `g`, the difference between the second
half at `v` and the first half at `g v`, and the halves that are not shared. The broadcast rate is
`|V| − ν*(G)`.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- An index code for side information `N` over the alphabet `α` with message set `M`. -/
structure IndexCode (N : V → Finset V) (α M : Type*) where
  enc : (V → α) → M
  dec : V → M → (V → α) → α
  dec_local : ∀ v m x x', (∀ u ∈ N v, x u = x' u) → dec v m x = dec v m x'
  correct : ∀ x v, dec v (enc x) x = x v

/-- The words with a common message form a storage code. -/
theorem IndexCode.isStorageCode_fibre {N : V → Finset V} {α M : Type*} [Fintype α]
    [DecidableEq M] (c : IndexCode N α M) (m : M) :
    IsStorageCode N (univ.filter (fun x => c.enc x = m)) := by
  intro x hx y hy v hxy
  have hx' := (mem_filter.mp hx).2
  have hy' := (mem_filter.mp hy).2
  rw [← c.correct x v, ← c.correct y v, hx', hy']
  exact c.dec_local v m x y hxy

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Index coding converse.** On a triangle-free graph of maximum degree three, every index code
over `α` with message set `M` has `log |M| ≥ (|V| − ν*) log |α|`. -/
theorem log_card_message_ge {α M : Type*} [Fintype α] [Nonempty α] [Fintype M] [DecidableEq M]
    (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) (c : IndexCode (nbhd G) α M) :
    ((Fintype.card V : ℝ) - fracMatchingNumber G) * Real.log (Fintype.card α) ≤
      Real.log (Fintype.card M) := by
  classical
  set K := Real.exp (fracMatchingNumber G * Real.log (Fintype.card α)) with hKdef
  have hK : ∀ m, ((univ.filter (fun x => c.enc x = m)).card : ℝ) ≤ K := by
    intro m
    rcases (univ.filter (fun x => c.enc x = m)).eq_empty_or_nonempty with he | hne
    · rw [he, card_empty, Nat.cast_zero]; exact (Real.exp_pos _).le
    · have h := log_card_le_fracMatchingNumber hcf hdeg (c.isStorageCode_fibre m)
      have hpos : (0 : ℝ) < (univ.filter (fun x => c.enc x = m)).card := by
        exact_mod_cast hne.card_pos
      calc ((univ.filter (fun x => c.enc x = m)).card : ℝ)
          = Real.exp (Real.log (univ.filter (fun x => c.enc x = m)).card) :=
            (Real.exp_log hpos).symm
        _ ≤ K := Real.exp_le_exp.mpr h
  have hsum : ((Fintype.card α : ℝ) ^ Fintype.card V) =
      ∑ m, ((univ.filter (fun x => c.enc x = m)).card : ℝ) := by
    have := card_eq_sum_card_fiberwise (f := c.enc) (s := (univ : Finset (V → α))) (t := univ)
      (fun x _ => mem_univ _)
    rw [card_univ, Fintype.card_fun] at this
    exact_mod_cast this
  have hle : ((Fintype.card α : ℝ) ^ Fintype.card V) ≤ Fintype.card M * K := by
    rw [hsum]
    calc ∑ m, ((univ.filter (fun x => c.enc x = m)).card : ℝ) ≤ ∑ _m : M, K :=
          sum_le_sum fun m _ => hK m
      _ = Fintype.card M * K := by simp
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  have hM : (0 : ℝ) < Fintype.card M := by
    have : Nonempty M := ⟨c.enc fun _ => a⟩
    exact_mod_cast Fintype.card_pos
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h := Real.log_le_log (by positivity) hle
  rw [Real.log_pow, Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  linarith

/-- **Index codes from double-cover matchings.** On every graph and over every alphabet `β × β`
with `β` a finite additive group, there is an index code with
`log |M| = (|V| − ν*) log |β × β|`. -/
theorem exists_indexCode (β : Type*) [AddCommGroup β] [Fintype β] [DecidableEq β] :
    ∃ (T : Finset V) (_ : IndexCode (nbhd G) (β × β) ((V → β) × ({v : V // v ∉ T} → β))),
      Real.log (Fintype.card ((V → β) × ({v : V // v ∉ T} → β))) =
        ((Fintype.card V : ℝ) - fracMatchingNumber G) * Real.log (Fintype.card (β × β)) := by
  classical
  obtain ⟨D, g, S, hadj, hinj, heq, -, -⟩ := fracMatchingNumber_spec G
  have hadjN : ∀ v ∈ D, g v ∈ nbhd G v := fun v hv => by simpa [nbhd] using hadj v hv
  have hadjN' : ∀ v ∈ D, v ∈ nbhd G (g v) := fun v hv => by simpa [nbhd] using (hadj v hv).symm
  have hpre : ∀ v (h : v ∈ D.image g), (Classical.choose (mem_image.mp h)) ∈ D ∧
      g (Classical.choose (mem_image.mp h)) = v := fun v h =>
    Classical.choose_spec (mem_image.mp h)
  refine ⟨D.image g, {
    enc := fun x => (fun v => if v ∈ D then (x v).2 - (x (g v)).1 else (x v).2,
      fun w => (x w.1).1)
    dec := fun v m x =>
      (if h : v ∈ D.image g then (x (Classical.choose (mem_image.mp h))).2 -
          m.1 (Classical.choose (mem_image.mp h)) else m.2 ⟨v, h⟩,
       if v ∈ D then m.1 v + (x (g v)).1 else m.1 v)
    dec_local := ?_
    correct := ?_ }, ?_⟩
  · intro v m x x' hxx'
    apply Prod.ext
    · by_cases h : v ∈ D.image g
      · have hp := hpre v h
        have hmem : Classical.choose (mem_image.mp h) ∈ nbhd G v := by
          have := hadjN' _ hp.1; rwa [hp.2] at this
        simp only [h, ↓reduceDIte]
        rw [hxx' _ hmem]
      · simp only [h, ↓reduceDIte]
    · by_cases h : v ∈ D
      · simp only [h, ↓reduceIte]
        rw [hxx' _ (hadjN v h)]
      · simp only [h, ↓reduceIte]
  · intro x v
    apply Prod.ext
    · by_cases h : v ∈ D.image g
      · have hp := hpre v h
        simp only [h, ↓reduceDIte, hp.1, ↓reduceIte, hp.2]
        abel
      · simp only [h, ↓reduceDIte]
    · by_cases h : v ∈ D
      · simp only [h, ↓reduceIte]
        abel
      · simp only [h, ↓reduceIte]
  · -- counting the message set
    have hT : (D.image g).card = D.card := card_image_of_injOn hinj
    have hsub : Fintype.card {v : V // v ∉ D.image g} = Fintype.card V - D.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hT]
    have hDle : D.card ≤ Fintype.card V := card_le_univ D
    have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, hsub, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      heq, Fintype.card_prod, Nat.cast_mul, Real.log_mul hβ.ne' hβ.ne',
      Nat.cast_sub hDle]
    ring

end HalfRate
