import HalfRate.Blocks

/-!
# Sweeps of digon cycles and Proposition CC

A block indexed by `Fin m`, eliminated in the order `f 0, …, f (m-1)`, has an elimination
certificate as soon as a colouring of the positions places every later in-neighbour of a position
in the record of the next position (`elimOn_ofFn`). Two colourings are used:
* `elimOn_cycle`: chordless digon cycles of length at least four (the colouring of Theorem N3);
* `elimOn_circulant`: digon cycles with chords `i → i + k`, the sweep of Proposition CC, valid
  unless `δ ∣ m - 1` or `δ ∣ m - 3` with `δ = m - 1 - k`.
`circulant_sweep` is the arithmetic of Proposition CC: when `3 ≤ k ≤ m - 3` and
`2k ≢ ±1 (mod m)`, the sweep is valid for the offset `k` or for the offset `m - k` (the mirror
image, `j ↦ -j`), and `elimOn_circulant_mirror` combines the two into a certificate.
-/

namespace HalfRate

open Finset MotionDepthCodes

variable {V : Type*} [DecidableEq V] [Fintype V] {N : V → Finset V}

omit [Fintype V] in
/-- **Positional certificates.** -/
theorem elimOn_ofFn {m c : ℕ} (hm : 0 < m) (f : Fin m → V) (hf : Function.Injective f)
    (col bcol : ℕ → Fin c) (hab : ∀ j < m, col j ≠ bcol j)
    (hstep : ∀ i j (hi : i < m) (hj : j < m), f ⟨i, hi⟩ ∈ N (f ⟨j, hj⟩) →
      i < j ∨ col i = bcol j) :
    Nonempty (ElimOn N (univ.image f)) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpos : ∀ t : Fin m, Function.invFun f (f t) = t := fun t =>
    Function.leftInverse_invFun hf t
  refine ⟨{
    l := List.ofFn f
    nodup := List.nodup_ofFn.mpr hf
    hl := by ext x; simp [List.mem_ofFn]
    m := c
    P := fun k => (univ.filter (fun i : Fin m => col i.val = k)).image f
    disj := ?_
    cover := ?_
    a := fun v => col (Function.invFun f v).val
    b := fun v => bcol (Function.invFun f v).val
    own := ?_
    ab := ?_
    step := ?_ }⟩
  · intro k k' hkk'
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [mem_image, mem_filter, mem_univ, true_and] at hx hx'
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨i', hi', he⟩ := hx'
    have := hf he; subst this; exact hkk' (hi.symm.trans hi')
  · ext x; simp only [mem_biUnion, mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, i, _, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨_, i, rfl, rfl⟩
  · intro v hv
    obtain ⟨t, -, rfl⟩ := mem_image.mp hv
    simp only [hpos]
    exact mem_image_of_mem _ (by simp)
  · intro v hv
    obtain ⟨t, -, rfl⟩ := mem_image.mp hv
    simp only [hpos]
    exact hab t.val t.isLt
  · intro j hj u hu
    have hj' : j < m := by simpa using hj
    obtain ⟨hu1, hu2⟩ := mem_inter.mp hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu2
    simp only [List.getElem_ofFn] at hu1 ⊢
    simp only [hpos]
    rcases hstep i.val j i.isLt hj' hu1 with h | h
    · exact mem_union_left _ (mem_rev_ofFn f i h)
    · exact mem_union_right _ (mem_image_of_mem _ (by simpa using h))

theorem bcol_of_ne {g t : ℕ} (h : t + 1 ≠ g) : bcol g t = ccol g (t + 1) := by
  simp [bcol, h]

theorem succ_mod_cases {m j : ℕ} (hj : j < m) :
    ((j + 1) % m = j + 1 ∧ j + 1 < m) ∨ ((j + 1) % m = 0 ∧ j + 1 = m) := by
  rcases Nat.lt_or_ge (j + 1) m with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have h' : j + 1 = m := by omega
    exact Or.inr ⟨by rw [h', Nat.mod_self], h'⟩

omit [Fintype V] in
/-- **Chordless digon cycles** of length at least four: the colouring of Theorem N3. -/
theorem elimOn_cycle {m : ℕ} (hm : 4 ≤ m) (f : Fin m → V) (hf : Function.Injective f)
    (hpar : ∀ i j (hi : i < m) (hj : j < m), f ⟨i, hi⟩ ∈ N (f ⟨j, hj⟩) →
      i = (j + 1) % m ∨ j = (i + 1) % m) :
    Nonempty (ElimOn N (univ.image f)) := by
  refine elimOn_ofFn (by omega) f hf (ccol m) (bcol m) (fun j hj => ccol_ne_bcol hm hj) ?_
  intro i j hi hj h
  rcases hpar i j hi hj h with h1 | h1
  · rcases succ_mod_cases hj with ⟨e, hlt⟩ | ⟨e, heq⟩
    · right; rw [h1, e, bcol_of_ne (by omega)]
    · left; omega
  · rcases succ_mod_cases hi with ⟨e, hlt⟩ | ⟨e, heq⟩
    · left; omega
    · right
      have hj0 : j = 0 := by omega
      have hi1 : i = m - 1 := by omega
      rw [hj0, hi1]; exact ccol_last hm

/-- The colours of the circulant sweep: position `0` is special (record `δ`); every other
position gets its residue mod `δ = m - 1 - k`, with the residue of `m - 1` merged into `1`. -/
def circCol (m k p : ℕ) : Fin (m - 1 - k + 1) :=
  if p = 0 then ⟨m - 1 - k, by omega⟩
  else if p % (m - 1 - k) = (m - 1) % (m - 1 - k) then ⟨1 % (m - 1 - k + 1), Nat.mod_lt _ (by omega)⟩
  else ⟨p % (m - 1 - k) % (m - 1 - k + 1), Nat.mod_lt _ (by omega)⟩

/-- The supplying record of the circulant sweep: the colour of the next position, and the
special record at the last position. -/
def circB (m k p : ℕ) : Fin (m - 1 - k + 1) :=
  if p + 1 = m then ⟨m - 1 - k, by omega⟩ else circCol m k (p + 1)

theorem circB_of_ne {m k p : ℕ} (h : p + 1 ≠ m) : circB m k p = circCol m k (p + 1) := by
  simp [circB, h]

theorem circCol_val_of_ne {m k p : ℕ} (hk : k + 3 ≤ m) (hp : p ≠ 0) :
    (circCol m k p).val =
      if p % (m - 1 - k) = (m - 1) % (m - 1 - k) then 1 else p % (m - 1 - k) := by
  have hδ : 2 ≤ m - 1 - k := by omega
  have hr := Nat.mod_lt p (show 0 < m - 1 - k by omega)
  simp only [circCol, hp, ↓reduceIte]
  split_ifs with h
  · simp only; exact Nat.mod_eq_of_lt (by omega)
  · simp only; exact Nat.mod_eq_of_lt (by omega)

omit [Fintype V] in
/-- **The circulant sweep.** A digon cycle `f 0 ↔ f 1 ↔ ⋯ ↔ f (m-1) ↔ f 0` whose other internal
arcs are chords `f i → f (i + k)` has an elimination certificate (the sweep from `0` in direction
`+1`), provided `3 ≤ k ≤ m - 3` and `δ = m - 1 - k` divides neither `m - 1` nor `m - 3`. -/
theorem elimOn_circulant {m k : ℕ} (hk : 3 ≤ k) (hkm : k + 3 ≤ m) (f : Fin m → V)
    (hf : Function.Injective f) (h1 : ¬ (m - 1 - k) ∣ (m - 1)) (h3 : ¬ (m - 1 - k) ∣ (m - 3))
    (hpar : ∀ i j (hi : i < m) (hj : j < m), f ⟨i, hi⟩ ∈ N (f ⟨j, hj⟩) →
      i = (j + 1) % m ∨ j = (i + 1) % m ∨ j = (i + k) % m) :
    Nonempty (ElimOn N (univ.image f)) := by
  set δ := m - 1 - k with hδdef
  have hδ : 2 ≤ δ := by omega
  have hδ0 : 0 < δ := by omega
  have hspecial : ∀ p, p ≠ 0 → (circCol m k p).val < δ := by
    intro p hp
    rw [circCol_val_of_ne hkm hp]
    split_ifs
    · omega
    · exact Nat.mod_lt _ hδ0
  have hcol0 : (circCol m k 0).val = δ := by simp [circCol, hδdef]
  -- consecutive positions have different residues
  have hres : ∀ p, p % δ ≠ (p + 1) % δ := by
    intro p h
    have := (Nat.modEq_iff_dvd' (show p ≤ p + 1 by omega)).mp h
    rw [show p + 1 - p = 1 by omega] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- the colours of consecutive inner positions differ
  have hinner : ∀ p, p ≠ 0 → p + 1 < m → circCol m k p ≠ circCol m k (p + 1) := by
    intro p hp hpm he
    have hv := congrArg Fin.val he
    rw [circCol_val_of_ne hkm hp, circCol_val_of_ne hkm (by omega)] at hv
    have hr := hres p
    split_ifs at hv with ha hb hb
    · exact hr (ha.trans hb.symm)
    · -- `p ≡ m - 1`, so `p + 1 ≡ m ≡ 1`: `δ ∣ m - 1`
      apply h1
      have e1 : p + 1 ≡ m [MOD δ] := by
        have := Nat.ModEq.add_right 1 (show p ≡ m - 1 [MOD δ] from ha)
        rwa [show m - 1 + 1 = m by omega] at this
      have e2 : 1 ≡ m [MOD δ] := by
        have h1' : (p + 1) % δ = 1 % δ := by rw [← hv, Nat.mod_eq_of_lt (by omega : 1 < δ)]
        exact (show 1 % δ = (p + 1) % δ from h1'.symm).trans e1
      exact (Nat.modEq_iff_dvd' (by omega)).mp e2
    · -- `p + 1 ≡ m - 1` and `p ≡ 1`, so `2 ≡ m - 1`: `δ ∣ m - 3`
      apply h3
      have e1 : p ≡ 1 [MOD δ] := by
        show p % δ = 1 % δ
        rw [hv, Nat.mod_eq_of_lt (by omega : 1 < δ)]
      have e2 : p + 1 ≡ 2 [MOD δ] := Nat.ModEq.add_right 1 e1
      have e3 : 2 ≡ m - 1 [MOD δ] := e2.symm.trans hb
      have := (Nat.modEq_iff_dvd' (by omega)).mp e3
      rwa [show m - 1 - 2 = m - 3 by omega] at this
    · exact hr hv
  refine elimOn_ofFn (by omega) f hf (circCol m k) (circB m k) ?_ ?_
  · intro p hp
    unfold circB
    split_ifs with h
    · intro he
      have := congrArg Fin.val he
      have := hspecial p (by omega)
      simp at *; omega
    · by_cases hp0 : p = 0
      · subst hp0
        intro he
        have h' := congrArg Fin.val he
        rw [hcol0] at h'
        have := hspecial (0 + 1) (by omega)
        omega
      · exact hinner p hp0 (by omega)
  · intro i j hi hj h
    rcases hpar i j hi hj h with h1' | h1' | h1'
    · -- `f i` is the successor of `f j`
      rcases succ_mod_cases hj with ⟨e, hlt⟩ | ⟨e, heq⟩
      · right; rw [h1', e, circB_of_ne (by omega)]
      · left; omega
    · -- `f j` is the successor of `f i`
      rcases succ_mod_cases hi with ⟨e, hlt⟩ | ⟨e, heq⟩
      · left; omega
      · right
        have hj0 : j = 0 := by omega
        have hi1 : i = m - 1 := by omega
        subst hj0; subst hi1
        rw [circB_of_ne (by omega)]
        apply Fin.ext
        rw [circCol_val_of_ne hkm (by omega), circCol_val_of_ne hkm (by omega)]
        simp only [↓reduceIte]
        split_ifs <;> simp [Nat.mod_eq_of_lt (show 1 < m - 1 - k by omega)]
    · -- a chord `f i → f j` with `j ≡ i + k`
      rcases Nat.lt_or_ge (i + k) m with hik | hik
      · left; rw [h1', Nat.mod_eq_of_lt hik]; omega
      · right
        have hj' : j = i + k - m := by
          rw [h1', Nat.mod_eq_sub_mod hik, Nat.mod_eq_of_lt (by omega)]
        rw [circB_of_ne (by omega)]
        apply Fin.ext
        rw [circCol_val_of_ne hkm (by omega), circCol_val_of_ne hkm (by omega)]
        have hmod : i % δ = (j + 1) % δ := by
          rw [show i = (j + 1) + δ by omega, Nat.add_mod_right]
        rw [hmod]

/-- **Proposition CC, arithmetic.** If `3 ≤ k ≤ m - 3` and `2k ≢ ±1 (mod m)`, the sweep
condition holds for the offset `k` or for the mirror offset `m - k`. -/
theorem circulant_sweep {m k : ℕ} (hk : 3 ≤ k) (hkm : k + 3 ≤ m)
    (hp : 2 * k ≠ m + 1) (hn : 2 * k + 1 ≠ m) :
    (¬ (m - 1 - k) ∣ (m - 1) ∧ ¬ (m - 1 - k) ∣ (m - 3)) ∨
      (¬ (m - 1 - (m - k)) ∣ (m - 1) ∧ ¬ (m - 1 - (m - k)) ∣ (m - 3)) := by
  obtain ⟨a, ha⟩ : ∃ a, m - 1 - k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, m - 1 - (m - k) = b := ⟨_, rfl⟩
  rw [ha, hb]
  have hm1 : m - 1 = a + (b + 1) := by omega
  have hm3 : m - 3 = a + (b - 1) := by omega
  have hm1' : m - 1 = b + (a + 1) := by omega
  have hm3' : m - 3 = b + (a - 1) := by omega
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hA' : a ∣ b + 1 ∨ a ∣ b - 1 := by
    by_contra h
    rw [not_or] at h
    exact hA ⟨fun hd => h.1 ((Nat.dvd_add_right (dvd_refl a)).mp (hm1 ▸ hd)),
      fun hd => h.2 ((Nat.dvd_add_right (dvd_refl a)).mp (hm3 ▸ hd))⟩
  have hB' : b ∣ a + 1 ∨ b ∣ a - 1 := by
    by_contra h
    rw [not_or] at h
    exact hB ⟨fun hd => h.1 ((Nat.dvd_add_right (dvd_refl b)).mp (hm1' ▸ hd)),
      fun hd => h.2 ((Nat.dvd_add_right (dvd_refl b)).mp (hm3' ▸ hd))⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · rcases hB' with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega
  · subst hab
    rcases hA' with h | h
    · have h' : a ∣ 1 := (Nat.dvd_add_right (dvd_refl a)).mp h
      have := Nat.le_of_dvd (by norm_num) h'; omega
    · have := Nat.le_of_dvd (by omega) h; omega
  · rcases hA' with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega

omit [DecidableEq V] [Fintype V] in
theorem neg_mod_eq {m x : ℕ} (hx : x < m) : (m - x) % m = if x = 0 then 0 else m - x := by
  split_ifs with h
  · subst h; simp
  · exact Nat.mod_eq_of_lt (by omega)

omit [DecidableEq V] [Fintype V] in
theorem add_mod_eq {m a c : ℕ} (ha : a < m) (hc : c ≤ m) :
    (a + c) % m = if a + c < m then a + c else a + c - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

omit [Fintype V] in
/-- **Proposition CC with the mirror sweep.** If `3 ≤ k ≤ m - 3` and `2k ≢ ±1 (mod m)`, a block
listed as `f 0, …, f (m-1)` whose arcs are `j ± 1 → j` and `j - k → j` (indices mod `m`) has an
elimination certificate: the sweep of `elimOn_circulant` for the offset `k`, or, along the
reversed listing `j ↦ -j`, for the offset `m - k`. -/
theorem elimOn_circulant_mirror {m k : ℕ} (hk : 3 ≤ k) (hkm : k + 3 ≤ m)
    (hp : 2 * k ≠ m + 1) (hn : 2 * k + 1 ≠ m) (f : Fin m → V) (hf : Function.Injective f)
    (hpar : ∀ i j (hi : i < m) (hj : j < m), f ⟨i, hi⟩ ∈ N (f ⟨j, hj⟩) →
      i = (j + 1) % m ∨ j = (i + 1) % m ∨ j = (i + k) % m) :
    Nonempty (ElimOn N (univ.image f)) := by
  rcases circulant_sweep hk hkm hp hn with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · exact elimOn_circulant hk hkm f hf h1 h3 hpar
  · have hm : 0 < m := by omega
    let σ : Fin m → Fin m := fun j => ⟨(m - j.val) % m, Nat.mod_lt _ hm⟩
    have hσ : Function.Involutive σ := by
      intro j
      apply Fin.ext
      show (m - (m - j.val) % m) % m = j.val
      have hj := j.isLt
      rw [neg_mod_eq hj]
      split_ifs with h0
      · rw [h0]; simp
      · rw [neg_mod_eq (by omega)]
        split_ifs <;> omega
    have himg : univ.image (f ∘ σ) = univ.image f := by
      ext x
      simp only [mem_image, mem_univ, true_and, Function.comp]
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨σ j, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨σ j, by rw [hσ j]⟩
    rw [← himg]
    refine elimOn_circulant (k := m - k) (by omega) (by omega) (f ∘ σ) (hf.comp hσ.injective)
      h1 h3 ?_
    intro i j hi hj h
    have h' := hpar ((m - i) % m) ((m - j) % m) (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) h
    obtain ⟨a, ha⟩ : ∃ a, (m - i) % m = a := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, (m - j) % m = b := ⟨_, rfl⟩
    have ha' : (i = 0 ∧ a = 0) ∨ (i ≠ 0 ∧ a = m - i) := by
      rw [← ha, neg_mod_eq hi]; split_ifs with h0 <;> simp [h0]
    have hb' : (j = 0 ∧ b = 0) ∨ (j ≠ 0 ∧ b = m - j) := by
      rw [← hb, neg_mod_eq hj]; split_ifs with h0 <;> simp [h0]
    have hal : a < m := ha ▸ Nat.mod_lt _ hm
    have hbl : b < m := hb ▸ Nat.mod_lt _ hm
    rw [ha, hb] at h'
    rw [add_mod_eq (c := 1) hbl (by omega), add_mod_eq (c := 1) hal (by omega),
      add_mod_eq (c := k) hal (by omega)] at h'
    rw [add_mod_eq (c := 1) hj (by omega), add_mod_eq (c := 1) hi (by omega),
      add_mod_eq (c := m - k) hi (by omega)]
    split_ifs at h' ⊢ <;> omega

end HalfRate
