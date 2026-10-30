import MergeDepth.RowEntropy
import MergeDepth.SkeletonWalk

/-!
# The geometric relaxation and transport with several heads per tape (Lemma 4.8)

The relaxation of the fifth paper, with several heads allowed on one tape. Tapes `τ` have cells
indexed by `ℤ`, the heads `η` have tapes `tape h`, and there are `ρ` registers without addresses.
The *slots* are the cells and the registers (`Slot τ ρ`). A run (`IsRun`) consists of the head
positions `H u` and the slots `loc u` of the labels `ι` before the transfers of tick `u`: tick `u`
moves labels only between *open* slots, the registers and the cells under heads at `H u`
(`loc u → loc (u + 1)`), and then moves every head by at most one cell (`H u → H (u + 1)`); moving a
head does not move labels. The placements are the configurations `loc u`, `u ≤ U`, and the occupancy
of a slot is the number of labels in it. Labels are arbitrary and may share a slot.

For an offset `θ ∈ [0, W)` the bins of every tape are the sets `⌊(z - θ)/W⌋ = i` (`bin`); the
*active class* consists of the registers and of the bins that contain a head, and every other bin is
a class of its own (`binClass`). With rows `A`, the potential `pot` is `∑_θ |ι| H(A | class at θ)` for a
uniformly random label, in nats (`condEnt`).

* `pot_transfer`: transfers do not change the potential.
* `pot_move_one`: a unit move of one head raises it by at most `κ (K W + ρ) log 2`, `K = |η|`, if
  every slot holds at most `κ` labels; `pot_move`: a move of all heads, by at most `K` times that.
* `pot_run`: along a run of `U` ticks the potential changes by at most `U K κ (K W + ρ) log 2`, in
  both directions; this is what allows reversed runs to be chained without being built.
* `pot_start_le`, `pot_end_ge`: the potential when the labels lie in input cells and the input heads
  lie in `W` consecutive cells, and when the labels lie in distinct output cells whose row is
  `W`-periodic with `b` cells of each row per period.
* `transport_sharp`, `transport`: **Lemma 4.8**, `m log₂ d ≤ κ K (K + ρ) U + 3L`, and the sharp form
  `m log₂ d ≤ m log₂ 3 + m log₂ ((L + W)/m) + U K κ (K + ρ/W)`; `transport_tpos` states it with the
  transposition permutation `tpos`.
-/

namespace MergeDepth

open Finset Real

/-! ### The transposition permutation -/

/-- The transposition permutation of positions, `(d i + j) b + s ↦ (d j + i) b + s`. -/
def tpos (d b p : ℕ) : ℕ := (p % (d * b) / b * d + p / (d * b)) * b + p % b

theorem tpos_digits {d b i j s : ℕ} (hj : j < d) (hs : s < b) :
    tpos d b ((d * i + j) * b + s) = (d * j + i) * b + s := by
  have hb : 0 < b := by omega
  have hjs : j * b + s < d * b := by nlinarith
  have hdb : 0 < d * b := Nat.mul_pos (by omega) hb
  have h1 := (Nat.div_mod_unique hdb).mpr
    ⟨(by ring : (j * b + s) + d * b * i = (d * i + j) * b + s), hjs⟩
  have h2 := (Nat.div_mod_unique hb).mpr ⟨(by ring : s + b * j = j * b + s), hs⟩
  have h3 := (Nat.div_mod_unique hb).mpr
    ⟨(by ring : s + b * (d * i + j) = (d * i + j) * b + s), hs⟩
  unfold tpos
  rw [h1.1, h1.2, h2.1, h3.2]
  ring

theorem exists_digits {d b p : ℕ} (hb : 0 < b) (hp : p < d * d * b) :
    ∃ i j s, i < d ∧ j < d ∧ s < b ∧ p = (d * i + j) * b + s := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hp
    · exact h
  refine ⟨p / (d * b), p % (d * b) / b, p % b, ?_, ?_, Nat.mod_lt _ hb, ?_⟩
  · exact Nat.div_lt_of_lt_mul (by nlinarith)
  · exact Nat.div_lt_of_lt_mul (by have := Nat.mod_lt p (by positivity : 0 < d * b); nlinarith)
  · have e1 := Nat.div_add_mod p (d * b)
    have e2 := Nat.div_add_mod (p % (d * b)) b
    have e3 : p % (d * b) % b = p % b := Nat.mod_mod_of_dvd p (dvd_mul_left b d)
    rw [e3] at e2
    calc p = d * b * (p / (d * b)) + p % (d * b) := e1.symm
      _ = d * b * (p / (d * b)) + (b * (p % (d * b) / b) + p % b) := by rw [e2]
      _ = (d * (p / (d * b)) + p % (d * b) / b) * b + p % b := by ring

theorem tpos_lt {d b p : ℕ} (hb : 0 < b) (hp : p < d * d * b) : tpos d b p < d * d * b := by
  obtain ⟨i, j, s, hi, hj, hs, rfl⟩ := exists_digits hb hp
  rw [tpos_digits hj hs]
  have : d * j + i + 1 ≤ d * d := by nlinarith
  nlinarith

theorem tpos_tpos {d b p : ℕ} (hb : 0 < b) (hp : p < d * d * b) : tpos d b (tpos d b p) = p := by
  obtain ⟨i, j, s, hi, hj, hs, rfl⟩ := exists_digits hb hp
  rw [tpos_digits hj hs, tpos_digits hi hs]

/-- The source row `⌊p/W⌋` of `p` is read off its image: `⌊(tpos p mod W)/b⌋`, `W = d b`. -/
theorem tpos_row {d b p : ℕ} (hb : 0 < b) (hp : p < d * d * b) :
    tpos d b p % (d * b) / b = p / (d * b) := by
  obtain ⟨i, j, s, hi, hj, hs, rfl⟩ := exists_digits hb hp
  rw [tpos_digits hj hs]
  have his : i * b + s < d * b := by nlinarith
  have hdb : 0 < d * b := Nat.mul_pos (by omega) hb
  have h1 := (Nat.div_mod_unique hdb).mpr
    ⟨(by ring : (i * b + s) + d * b * j = (d * j + i) * b + s), his⟩
  have h2 := (Nat.div_mod_unique hdb).mpr
    ⟨(by ring : (j * b + s) + d * b * i = (d * i + j) * b + s),
      (by nlinarith : j * b + s < d * b)⟩
  have h3 := (Nat.div_mod_unique hb).mpr ⟨(by ring : s + b * i = i * b + s), hs⟩
  rw [h1.2, h2.1, h3.1]

/-! ### The model -/

/-- The slots of the relaxation: the cells `(t, z)` of the tapes and the registers. -/
abbrev Slot (τ : Type*) (ρ : ℕ) := (τ × ℤ) ⊕ Fin ρ

variable {τ η ι : Type*} [DecidableEq τ] [Fintype η] {ρ : ℕ}

/-- A slot is *open* at the head positions `P` if it is a register or a cell under a head. -/
def SlotOpen (tape : η → τ) (P : η → ℤ) : Slot τ ρ → Prop
  | .inl c => ∃ h, tape h = c.1 ∧ P h = c.2
  | .inr _ => True

/-- A run of the relaxation for `U` ticks with occupancy at most `κ`. Tick `u` transfers labels between
open slots at the head positions `H u` (`loc u → loc (u + 1)`) and then moves every head by at most
one cell (`H u → H (u + 1)`). Every placement `loc u`, `u ≤ U`, puts at most `κ` labels in a slot. -/
structure IsRun [Fintype ι] (tape : η → τ) (H : ℕ → η → ℤ) (loc : ℕ → ι → Slot τ ρ) (U κ : ℕ) :
    Prop where
  move : ∀ u < U, ∀ h, |H (u + 1) h - H u h| ≤ 1
  transfer : ∀ u < U, ∀ i, loc (u + 1) i ≠ loc u i →
    SlotOpen tape (H u) (loc u i) ∧ SlotOpen tape (H u) (loc (u + 1) i)
  occ : ∀ u ≤ U, ∀ s, (univ.filter fun i => loc u i = s).card ≤ κ

omit [Fintype η] in
theorem IsRun.mono [Fintype ι] {tape : η → τ} {H : ℕ → η → ℤ} {loc : ℕ → ι → Slot τ ρ} {U κ : ℕ}
    (hR : IsRun tape H loc U κ) {U' : ℕ} (h : U' ≤ U) : IsRun tape H loc U' κ :=
  ⟨fun u hu => hR.move u (by omega), fun u hu => hR.transfer u (by omega),
    fun u hu => hR.occ u (by omega)⟩

/-- The bin of the cell `z` at offset `θ`: `⌊(z - θ)/W⌋`. -/
def bin (W θ z : ℤ) : ℤ := (z - θ) / W

/-- The class of a slot at offset `θ`: `none`, the active class, for the registers and the cells of
the bins that contain a head; otherwise the bin, with its tape. -/
def binClass (tape : η → τ) (W θ : ℤ) (P : η → ℤ) : Slot τ ρ → Option (τ × ℤ)
  | .inl c => if ∃ h, tape h = c.1 ∧ bin W θ (P h) = bin W θ c.2 then none else some (c.1, bin W θ c.2)
  | .inr _ => none

/-- The potential `∑_{θ < W} |ι| H(A | class at θ)`, in nats. -/
noncomputable def pot [Fintype ι] (tape : η → τ) (W : ℕ) (A : ι → ℤ) (P : η → ℤ)
    (ℓ : ι → Slot τ ρ) : ℝ :=
  ∑ θ ∈ range W, condEnt univ A (fun i => binClass tape (W : ℤ) (θ : ℤ) P (ℓ i))

theorem binClass_of_open {tape : η → τ} {P : η → ℤ} {s : Slot τ ρ} (W θ : ℤ) (hs : SlotOpen tape P s) :
    binClass tape W θ P s = none := by
  cases s with
  | inl c =>
    obtain ⟨h, h1, h2⟩ := hs
    simp only [binClass]
    rw [ite_eq_left ⟨h, h1, by rw [h2]⟩]
  | inr r => rfl

/-- **Transfers.** Both ends of every transfer are open, hence in the active class. -/
theorem pot_transfer [Fintype ι] (tape : η → τ) (W : ℕ) (A : ι → ℤ) (P : η → ℤ)
    {ℓ ℓ' : ι → Slot τ ρ} (h : ∀ i, ℓ' i ≠ ℓ i → SlotOpen tape P (ℓ i) ∧ SlotOpen tape P (ℓ' i)) :
    pot tape W A P ℓ' = pot tape W A P ℓ := by
  unfold pot
  refine sum_congr rfl fun θ _ => ?_
  congr 1
  funext i
  by_cases hi : ℓ' i = ℓ i
  · rw [hi]
  · obtain ⟨h1, h2⟩ := h i hi
    rw [binClass_of_open _ _ h1, binClass_of_open _ _ h2]

/-! ### Integer arithmetic of bins -/

theorem ediv_succ_dvd {W n : ℤ} (hW : 0 < W) (h : n / W ≠ (n + 1) / W) : W ∣ n + 1 := by
  by_contra hd
  apply h
  have hr := Int.emod_nonneg (n + 1) hW.ne'
  have hr' := Int.emod_lt_of_pos (n + 1) hW
  have hne : (n + 1) % W ≠ 0 := fun h0 => hd (Int.dvd_of_emod_eq_zero h0)
  have e := Int.emod_add_mul_ediv (n + 1) W
  exact ((Int.ediv_emod_unique hW (a := n) (q := (n + 1) / W) (r := (n + 1) % W - 1)).mpr
    ⟨by linarith, by omega, by omega⟩).1

/-- A unit move changes the bin of a cell for at most one offset in `[0, W)`. -/
theorem bin_change_unique {W : ℤ} (hW : 0 < W) {x x' θ θ' : ℤ} (hx : |x' - x| ≤ 1)
    (hθ : 0 ≤ θ) (hθW : θ < W) (hθ' : 0 ≤ θ') (hθ'W : θ' < W)
    (h1 : bin W θ x ≠ bin W θ x') (h2 : bin W θ' x ≠ bin W θ' x') : θ = θ' := by
  unfold bin at h1 h2
  have hcases : x' = x + 1 ∨ x' = x ∨ x' = x - 1 := by
    have := abs_le.mp hx; omega
  rcases hcases with rfl | rfl | rfl
  · have d1 := ediv_succ_dvd hW (n := x - θ) (by rwa [show x - θ + 1 = x + 1 - θ by ring])
    have d2 := ediv_succ_dvd hW (n := x - θ') (by rwa [show x - θ' + 1 = x + 1 - θ' by ring])
    have hd : W ∣ θ' - θ := by
      have := dvd_sub d1 d2
      rwa [show x - θ + 1 - (x - θ' + 1) = θ' - θ by ring] at this
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith
  · exact absurd rfl h1
  · have d1 := ediv_succ_dvd hW (n := x - 1 - θ) (by
      rw [show x - 1 - θ + 1 = x - θ by ring]; exact fun h => h1 h.symm)
    have d2 := ediv_succ_dvd hW (n := x - 1 - θ') (by
      rw [show x - 1 - θ' + 1 = x - θ' by ring]; exact fun h => h2 h.symm)
    have hd : W ∣ θ' - θ := by
      have := dvd_sub d1 d2
      rwa [show x - 1 - θ + 1 - (x - 1 - θ' + 1) = θ' - θ by ring] at this
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
    linarith

/-- `W` consecutive integers meet at most two blocks of `W`. -/
theorem ediv_window {W a y : ℤ} (hW : 0 < W) (h1 : a ≤ y) (h2 : y ≤ a + W - 1) :
    a / W ≤ y / W ∧ y / W ≤ a / W + 1 := by
  obtain ⟨a1, a2⟩ := block_bounds hW a
  obtain ⟨y1, y2⟩ := block_bounds hW y
  refine ⟨Int.ediv_le_ediv hW h1, ?_⟩
  by_contra hc
  push Not at hc
  have := block_gap hW hc
  rw [mul_add, mul_one] at this
  linarith

/-- The row `⌊x/W⌋` of a cell is its bin or the next one. -/
theorem ediv_near_bin {W θ x : ℤ} (hW : 0 < W) (hθ : 0 ≤ θ) (hθW : θ < W) :
    bin W θ x ≤ x / W ∧ x / W ≤ bin W θ x + 1 :=
  ediv_window hW (by linarith) (by linarith)

/-! ### Moves -/

/-- At most `κ (K W + ρ)` labels lie in the active class. -/
theorem card_binClass_none_le [Fintype ι] (tape : η → τ) {W : ℕ} (hW : 0 < W) (θ : ℤ) (P : η → ℤ)
    (ℓ : ι → Slot τ ρ) {κ : ℕ} (hocc : ∀ s, (univ.filter fun i => ℓ i = s).card ≤ κ) :
    (univ.filter fun i => binClass tape W θ P (ℓ i) = none).card ≤ κ * (Fintype.card η * W + ρ) := by
  classical
  have hW' : (0 : ℤ) < W := by exact_mod_cast hW
  set S : Finset (Slot τ ρ) := (univ : Finset (Fin ρ)).image Sum.inr ∪
    univ.biUnion fun h => (Ico (θ + W * bin W θ (P h)) (θ + W * bin W θ (P h) + W)).image
      fun z => Sum.inl (tape h, z)
  have hsub : (univ.filter fun i => binClass tape W θ P (ℓ i) = none) ⊆
      univ.filter fun i => ℓ i ∈ S := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    revert hi
    cases ℓ i with
    | inr r => intro _; exact mem_union_left _ (mem_image_of_mem _ (mem_univ r))
    | inl c =>
      intro hc
      simp only [binClass] at hc
      split_ifs at hc with hex
      obtain ⟨h, h1, h2⟩ := hex
      refine mem_union_right _ (mem_biUnion.mpr ⟨h, mem_univ _, mem_image.mpr ⟨c.2, ?_, ?_⟩⟩)
      · obtain ⟨b1, b2⟩ := block_bounds hW' (c.2 - θ)
        rw [mem_Ico, h2]
        unfold bin
        constructor <;> linarith
      · rw [h1]
  have hS : S.card ≤ ρ + Fintype.card η * W := by
    refine (card_union_le _ _).trans (add_le_add ?_ ?_)
    · exact card_image_le.trans (by simp)
    · refine card_biUnion_le.trans ?_
      calc ∑ h, ((Ico (θ + W * bin W θ (P h)) (θ + W * bin W θ (P h) + W)).image
              fun z => (Sum.inl (tape h, z) : Slot τ ρ)).card
          ≤ ∑ _h : η, W := sum_le_sum fun h _ => card_image_le.trans (by simp)
        _ = Fintype.card η * W := by simp
  calc (univ.filter fun i => binClass tape W θ P (ℓ i) = none).card
      ≤ (univ.filter fun i => ℓ i ∈ S).card := card_le_card hsub
    _ = ∑ s ∈ S, ((univ.filter fun i => ℓ i ∈ S).filter fun i => ℓ i = s).card :=
        card_eq_sum_card_fiberwise fun i hi => (mem_filter.mp hi).2
    _ ≤ ∑ _s ∈ S, κ := sum_le_sum fun s _ =>
        (card_le_card fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact hi.2).trans (hocc s)
    _ = S.card * κ := by simp
    _ ≤ κ * (Fintype.card η * W + ρ) := by
        rw [mul_comm]; exact Nat.mul_le_mul_left κ (by omega)

/-- **A unit move of one head** raises the potential by at most `κ (K W + ρ) log 2`. -/
theorem pot_move_one [Fintype ι] [DecidableEq η] (tape : η → τ) {W : ℕ} (hW : 0 < W) (A : ι → ℤ) (P : η → ℤ)
    (h : η) (x' : ℤ) (hx : |x' - P h| ≤ 1) (ℓ : ι → Slot τ ρ) {κ : ℕ}
    (hocc : ∀ s, (univ.filter fun i => ℓ i = s).card ≤ κ) :
    pot tape W A (Function.update P h x') ℓ ≤
      pot tape W A P ℓ + κ * (Fintype.card η * W + ρ) * Real.log 2 := by
  classical
  have hW' : (0 : ℤ) < W := by exact_mod_cast hW
  set P' := Function.update P h x' with hP'
  set B : ℝ := κ * (Fintype.card η * W + ρ) * Real.log 2
  have hB : 0 ≤ B := by positivity
  have hPh : P' h = x' := by simp [P']
  have hPo : ∀ h', h' ≠ h → P' h' = P h' := fun h' hh => by simp [P', hh]
  -- offsets whose classes do not change
  have hsame : ∀ θ : ℕ, bin W θ (P h) = bin W θ x' →
      condEnt univ A (fun i => binClass tape W θ P' (ℓ i)) =
        condEnt univ A (fun i => binClass tape W θ P (ℓ i)) := by
    intro θ hb
    have hP : ∀ h', bin W θ (P' h') = bin W θ (P h') := by
      intro h'
      by_cases hh : h' = h
      · rw [hh, hPh, hb]
      · rw [hPo h' hh]
    congr 1
    funext i
    cases ℓ i with
    | inl c => simp only [binClass, hP]
    | inr r => rfl
  -- the offset whose classes change
  have hchg : ∀ θ : ℕ, θ < W →
      condEnt univ A (fun i => binClass tape W θ P' (ℓ i)) ≤
        condEnt univ A (fun i => binClass tape W θ P (ℓ i)) + B := by
    intro θ _
    have hloc := condEnt_local univ A (fun i => binClass tape W θ P (ℓ i))
      (fun i => binClass tape W θ P' (ℓ i)) none none (some (tape h, bin W θ x'))
      (fun o => o.bind fun p => if p.1 = tape h ∧ p.2 = bin W θ (P h) then none else some p)
      ?_ ?_
    · refine hloc.trans (add_le_add_right ?_ _)
      have := card_binClass_none_le tape hW θ P' ℓ hocc
      have hc : ((univ.filter fun i => binClass tape W θ P' (ℓ i) = none).card : ℝ) ≤
          κ * (Fintype.card η * W + ρ) := by exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hc (Real.log_nonneg (by norm_num))
    · intro i _ hi
      generalize ℓ i = s at hi ⊢
      cases s with
      | inr r => exact absurd rfl hi
      | inl c =>
        simp only [binClass] at hi ⊢
        by_cases hex' : ∃ h'', tape h'' = c.1 ∧ bin W θ (P' h'') = bin W θ c.2
        · rw [ite_eq_left hex'] at hi; exact absurd rfl hi
        rw [ite_eq_right hex', Option.bind_some]
        dsimp only
        have hiff : (∃ h'', tape h'' = c.1 ∧ bin W θ (P h'') = bin W θ c.2) ↔
            (c.1 = tape h ∧ bin W θ c.2 = bin W θ (P h)) := by
          constructor
          · rintro ⟨h'', h1, h2⟩
            by_cases hh : h'' = h
            · rw [hh] at h1 h2; exact ⟨h1.symm, h2.symm⟩
            · exact absurd ⟨h'', h1, by rw [hPo h'' hh]; exact h2⟩ hex'
          · rintro ⟨h1, h2⟩; exact ⟨h, h1.symm, h2.symm⟩
        by_cases hc : c.1 = tape h ∧ bin W θ c.2 = bin W θ (P h)
        · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
        · rw [ite_eq_right (fun hex => hc (hiff.mp hex)), ite_eq_right hc]
    · intro i _ hi
      generalize ℓ i = s at hi ⊢
      cases s with
      | inr r => left; rfl
      | inl c =>
        simp only [binClass] at hi ⊢
        by_cases hex' : ∃ h'', tape h'' = c.1 ∧ bin W θ (P' h'') = bin W θ c.2
        swap
        · rw [ite_eq_right hex'] at hi; exact absurd hi (by simp)
        obtain ⟨h'', h1, h2⟩ := hex'
        by_cases hh : h'' = h
        · rw [hh, hPh] at h2
          rw [hh] at h1
          by_cases hex : ∃ h₀, tape h₀ = c.1 ∧ bin W θ (P h₀) = bin W θ c.2
          · left; rw [ite_eq_left hex]
          · right; rw [ite_eq_right hex, ← h1, ← h2]
        · left
          rw [ite_eq_left ⟨h'', h1, by rw [← hPo h'' hh]; exact h2⟩]
  -- at most one offset changes
  set ch := (range W).filter fun θ : ℕ => bin W θ (P h) ≠ bin W θ x'
  have hcard : ch.card ≤ 1 := card_le_one.mpr fun a ha b hb => by
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    obtain ⟨hb1, hb2⟩ := mem_filter.mp hb
    have := bin_change_unique hW' hx (by positivity) (by exact_mod_cast mem_range.mp ha1)
      (by positivity) (by exact_mod_cast mem_range.mp hb1) ha2 hb2
    exact_mod_cast this
  unfold pot
  rw [← sum_filter_add_sum_filter_not (range W) (fun θ : ℕ => bin W θ (P h) ≠ bin W θ x'),
    ← sum_filter_add_sum_filter_not (range W) (fun θ : ℕ => bin W θ (P h) ≠ bin W θ x')]
  have e2 : ∑ θ ∈ (range W).filter (fun θ : ℕ => ¬ bin W θ (P h) ≠ bin W θ x'),
      condEnt univ A (fun i => binClass tape W θ P' (ℓ i)) =
      ∑ θ ∈ (range W).filter (fun θ : ℕ => ¬ bin W θ (P h) ≠ bin W θ x'),
      condEnt univ A (fun i => binClass tape W θ P (ℓ i)) :=
    sum_congr rfl fun θ hθ => hsame θ (not_not.mp (mem_filter.mp hθ).2)
  have e1 : ∑ θ ∈ ch, condEnt univ A (fun i => binClass tape W θ P' (ℓ i)) ≤
      ∑ θ ∈ ch, condEnt univ A (fun i => binClass tape W θ P (ℓ i)) + B := by
    calc ∑ θ ∈ ch, condEnt univ A (fun i => binClass tape W θ P' (ℓ i))
        ≤ ∑ θ ∈ ch, (condEnt univ A (fun i => binClass tape W θ P (ℓ i)) + B) :=
          sum_le_sum fun θ hθ => hchg θ (mem_range.mp (mem_filter.mp hθ).1)
      _ = ∑ θ ∈ ch, condEnt univ A (fun i => binClass tape W θ P (ℓ i)) + ch.card * B := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ ∑ θ ∈ ch, condEnt univ A (fun i => binClass tape W θ P (ℓ i)) + B := by
          have : (ch.card : ℝ) ≤ 1 := by exact_mod_cast hcard
          nlinarith
  rw [e2]
  linarith

/-- **A move of all heads** by at most one cell each raises the potential by at most
`K κ (K W + ρ) log 2`. -/
theorem pot_move [Fintype ι] (tape : η → τ) {W : ℕ} (hW : 0 < W) (A : ι → ℤ) (P P' : η → ℤ)
    (hP : ∀ h, |P' h - P h| ≤ 1) (ℓ : ι → Slot τ ρ) {κ : ℕ}
    (hocc : ∀ s, (univ.filter fun i => ℓ i = s).card ≤ κ) :
    pot tape W A P' ℓ ≤
      pot tape W A P ℓ + Fintype.card η * (κ * (Fintype.card η * W + ρ) * Real.log 2) := by
  classical
  set B : ℝ := κ * (Fintype.card η * W + ρ) * Real.log 2
  let Q : Finset η → η → ℤ := fun S h => if h ∈ S then P' h else P h
  have key : ∀ S : Finset η, pot tape W A (Q S) ℓ ≤ pot tape W A P ℓ + S.card * B := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · have : Q ∅ = P := funext fun h => by simp [Q]
      rw [this]; simp
    · intro a S ha ih
      have hQ : Q (insert a S) = Function.update (Q S) a (P' a) := by
        funext h
        by_cases hh : h = a
        · rw [hh]; simp [Q]
        · simp [Q, hh]
      have hstep := pot_move_one tape hW A (Q S) a (P' a) (by simpa [Q, ha] using hP a) ℓ hocc
      rw [hQ, card_insert_of_notMem ha]
      push_cast
      linarith
  have := key univ
  have hQ : Q univ = P' := funext fun h => by simp [Q]
  rw [hQ, card_univ] at this
  exact this

/-- **Runs.** Along a run of `U` ticks the potential changes by at most `U K κ (K W + ρ) log 2`, in
either direction. -/
theorem pot_run [Fintype ι] {tape : η → τ} {H : ℕ → η → ℤ} {loc : ℕ → ι → Slot τ ρ} {U κ : ℕ}
    (hR : IsRun tape H loc U κ) {W : ℕ} (hW : 0 < W) (A : ι → ℤ) :
    pot tape W A (H U) (loc U) ≤ pot tape W A (H 0) (loc 0) +
        U * (Fintype.card η * (κ * (Fintype.card η * W + ρ) * Real.log 2)) ∧
      pot tape W A (H 0) (loc 0) ≤ pot tape W A (H U) (loc U) +
        U * (Fintype.card η * (κ * (Fintype.card η * W + ρ) * Real.log 2)) := by
  induction U with
  | zero => simp
  | succ U ih =>
    obtain ⟨ih1, ih2⟩ := ih (hR.mono (Nat.le_succ U))
    have htr := pot_transfer tape W A (H U) (ℓ := loc U) (ℓ' := loc (U + 1))
      (hR.transfer U (by omega))
    have hocc := hR.occ (U + 1) le_rfl
    have hfw := pot_move tape hW A (H U) (H (U + 1)) (fun h => hR.move U (by omega) h)
      (loc (U + 1)) hocc
    have hbw := pot_move tape hW A (H (U + 1)) (H U)
      (fun h => by rw [abs_sub_comm]; exact hR.move U (by omega) h) (loc (U + 1)) hocc
    push_cast
    constructor <;> linarith

/-! ### The two ends -/

/-- **The start.** If every label lies in its input cell and the input heads lie in `W` consecutive
cells, every class meets at most three rows, so the potential is at most `W |ι| log 3`. -/
theorem pot_start_le [Fintype ι] (tape : η → τ) {W : ℕ} (hW : 0 < W) (P : η → ℤ) (inp : τ)
    (src : ι → ℤ) (a : ℤ) (hwin : ∀ h, tape h = inp → a ≤ P h ∧ P h ≤ a + W - 1) :
    pot tape W (fun i => src i / W) P (fun i => (Sum.inl (inp, src i) : Slot τ ρ)) ≤
      W * (Fintype.card ι * Real.log 3) := by
  have hW' : (0 : ℤ) < W := by exact_mod_cast hW
  unfold pot
  rw [show (W : ℝ) * (Fintype.card ι * Real.log 3) = ∑ _θ ∈ range W, (Fintype.card ι * Real.log 3) by
    rw [sum_const, card_range, nsmul_eq_mul]]
  refine sum_le_sum fun θ hθ => ?_
  have hθ0 : (0 : ℤ) ≤ θ := by positivity
  have hθW : (θ : ℤ) < W := by exact_mod_cast mem_range.mp hθ
  have := condEnt_le_of_card_image univ (fun i => src i / W)
    (fun i => binClass tape W θ P (Sum.inl (inp, src i) : Slot τ ρ)) (R := 3) ?_
  · simpa [card_univ] using this
  intro z
  -- every class lies in three consecutive rows
  have hsub : ∃ lo : ℤ, ((univ.filter fun i => binClass tape W θ P (Sum.inl (inp, src i) : Slot τ ρ) = z).image
      fun i => src i / W) ⊆ Icc lo (lo + 2) := by
    cases z with
    | none =>
      refine ⟨bin W θ a, fun r hr => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      have hi := (mem_filter.mp hi).2
      simp only [binClass] at hi
      split_ifs at hi with hex
      obtain ⟨h, h1, h2⟩ := hex
      obtain ⟨hp1, hp2⟩ := hwin h h1
      have hw := ediv_window hW' (a := a - θ) (y := P h - θ) (by linarith) (by linarith)
      have hn := ediv_near_bin hW' hθ0 hθW (x := src i)
      unfold bin at h2 hn ⊢
      rw [mem_Icc]
      constructor <;> linarith
    | some p =>
      refine ⟨p.2, fun r hr => ?_⟩
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      have hi := (mem_filter.mp hi).2
      simp only [binClass] at hi
      split_ifs at hi
      obtain rfl := Option.some.inj hi
      have hn := ediv_near_bin hW' hθ0 hθW (x := src i)
      rw [mem_Icc]
      constructor <;> linarith
  obtain ⟨lo, hlo⟩ := hsub
  refine (card_le_card hlo).trans ?_
  rw [Int.card_Icc]
  omega

/-- **The end.** If the labels lie in distinct output cells of `[0, dW)`, `W = d b`, and the row of a
label is `⌊(cell mod W)/b⌋`, then at every offset the potential is at least
`|ι| log |ι| - |ι| log (d + 1) - |ι| log b`. -/
theorem pot_end_ge [Fintype ι] (tape : η → τ) {d b W : ℕ} (hb : 1 ≤ b) (hWdb : W = d * b)
    (P : η → ℤ) (out : τ) (dst A : ι → ℤ) (hinj : Function.Injective dst)
    (hdst : ∀ i, 0 ≤ dst i ∧ dst i < d * W) (hrow : ∀ i, A i = dst i % W / b) :
    (W : ℝ) * (Fintype.card ι * Real.log (Fintype.card ι) - Fintype.card ι * Real.log (d + 1) -
        Fintype.card ι * Real.log b) ≤
      pot tape W A P (fun i => (Sum.inl (out, dst i) : Slot τ ρ)) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- no labels at all
    have hι : IsEmpty ι := ⟨fun i => by have := hdst i; subst hd0; simp at this; omega⟩
    simp [Fintype.card_eq_zero, pot, condEnt, fs]
  have hW : 0 < W := by rw [hWdb]; positivity
  have hW' : (0 : ℤ) < W := by exact_mod_cast hW
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  unfold pot
  rw [show (W : ℝ) * (Fintype.card ι * Real.log (Fintype.card ι) - Fintype.card ι * Real.log (d + 1) -
      Fintype.card ι * Real.log b) = ∑ _θ ∈ range W, (Fintype.card ι * Real.log (Fintype.card ι) -
      Fintype.card ι * Real.log (d + 1) - Fintype.card ι * Real.log b) by
    rw [sum_const, card_range, nsmul_eq_mul]]
  refine sum_le_sum fun θ hθ => ?_
  have hθ0 : (0 : ℤ) ≤ θ := by positivity
  have hθW : (θ : ℤ) < W := by exact_mod_cast mem_range.mp hθ
  set binf : ι → ℤ := fun i => bin W θ (dst i)
  set g : ℤ → Option (τ × ℤ) := fun β =>
    if ∃ h, tape h = out ∧ bin W θ (P h) = β then none else some (out, β)
  have hcomp := condEnt_le_comp univ A binf g
  refine le_trans ?_ (le_of_le_of_eq hcomp rfl)
  have hr : (univ.image binf).card ≤ d + 1 := by
    have hsub : univ.image binf ⊆ Icc (-1) ((d : ℤ) - 1) := by
      intro β hβ
      obtain ⟨i, -, rfl⟩ := mem_image.mp hβ
      obtain ⟨h1, h2⟩ := hdst i
      obtain ⟨q1, q2⟩ := block_bounds hW' (dst i - θ)
      rw [mem_Icc]
      simp only [binf, bin]
      constructor
      · by_contra hc
        push Not at hc
        have : (W : ℤ) * ((dst i - θ) / W) ≤ W * (-2) :=
          mul_le_mul_of_nonneg_left (by omega) hW'.le
        linarith
      · have : (W : ℤ) * ((dst i - θ) / W) < W * d := by nlinarith
        have := Int.lt_of_mul_lt_mul_left this hW'.le
        omega
    refine (card_le_card hsub).trans ?_
    simp [Int.card_Icc]
  have hfib : ∀ i ∈ (univ : Finset ι), fcard univ (fun x => (binf x, A x)) i ≤ b := by
    intro i _
    unfold fcard
    have hmaps : ∀ j ∈ univ.filter (fun y => (binf y, A y) = (binf i, A i)),
        dst j % W ∈ Ico (A i * b) (A i * b + b) := by
      intro j hj
      obtain ⟨-, hj⟩ := mem_filter.mp hj
      simp only [Prod.mk.injEq] at hj
      obtain ⟨-, hA⟩ := hj
      rw [hrow j] at hA
      obtain ⟨r1, r2⟩ := block_bounds hb' (dst j % W)
      rw [mem_Ico, ← hA]
      constructor <;> linarith
    have hinjOn : Set.InjOn (fun j => dst j % W)
        (univ.filter (fun y => (binf y, A y) = (binf i, A i)) : Set ι) := by
      intro j hj j' hj' he
      have hj := (mem_filter.mp (mem_coe.mp hj)).2
      have hj' := (mem_filter.mp (mem_coe.mp hj')).2
      simp only [Prod.mk.injEq] at hj hj'
      simp only at he
      apply hinj
      have hdvd : (W : ℤ) ∣ dst j' - dst j := Int.ModEq.dvd he
      have hbin : bin W θ (dst j) = bin W θ (dst j') := hj.1.trans hj'.1.symm
      obtain ⟨u1, u2⟩ := block_bounds hW' (dst j - θ)
      obtain ⟨v1, v2⟩ := block_bounds hW' (dst j' - θ)
      unfold bin at hbin
      rw [hbin] at u1 u2
      have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> linarith)
      linarith
    refine (card_le_card_of_injOn _ hmaps hinjOn).trans ?_
    simp
  have hge := condEnt_ge univ A binf hr hfib
  simp only [card_univ] at hge
  push_cast at hge ⊢
  linarith

/-! ### Lemma 4.8 -/

theorem log_le_div_exp {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have := Real.log_le_sub_one_of_pos (show 0 < x / Real.exp 1 by positivity)
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
  linarith

/-- `y log (a/y) ≤ a/e`. -/
theorem mul_log_div_le {a y : ℝ} (ha : 0 < a) (hy : 0 < y) : y * Real.log (a / y) ≤ a / Real.exp 1 := by
  have := log_le_div_exp (show 0 < a / y by positivity)
  calc y * Real.log (a / y) ≤ y * (a / y / Real.exp 1) := mul_le_mul_of_nonneg_left this hy.le
    _ = a / Real.exp 1 := by field_simp

/-- The arithmetic that turns the potential bounds into Lemma 4.8. -/
theorem transport_of_pot {m d b W : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) (hW : W = d * b) (hm : 0 < m)
    {X : ℝ} (h : (W : ℝ) * (m * Real.log m - m * Real.log (d + 1) - m * Real.log b) ≤
      W * (m * Real.log 3) + X) :
    m * Real.logb 2 d ≤ m * Real.logb 2 3 + m * Real.logb 2 (((d + 1) * d * b : ℕ) / m) +
      X / (W * Real.log 2) := by
  have hWpos : (0 : ℝ) < W := by rw [hW]; push_cast; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h' : m * Real.log m - m * Real.log (d + 1) - m * Real.log b ≤ m * Real.log 3 + X / W := by
    have e : m * Real.log 3 + X / W = (W * (m * Real.log 3) + X) / W := by field_simp
    rw [e, le_div_iff₀ hWpos]
    linarith
  have hsplit : Real.log d = Real.log m - Real.log (d + 1) - Real.log b +
      Real.log (((d + 1) * d * b : ℕ) / m) := by
    push_cast
    rw [Real.log_div (by positivity) hm'.ne', Real.log_mul (by positivity) hb'.ne',
      Real.log_mul (by positivity) hd'.ne']
    ring
  have hmain : m * Real.log d ≤ m * Real.log 3 + m * Real.log (((d + 1) * d * b : ℕ) / m) + X / W := by
    rw [hsplit, mul_add, mul_sub, mul_sub]
    linarith
  simp only [Real.logb]
  have e : m * (Real.log 3 / Real.log 2) + m * (Real.log (((d + 1) * d * b : ℕ) / m) / Real.log 2) +
      X / (W * Real.log 2) =
      (m * Real.log 3 + m * Real.log (((d + 1) * d * b : ℕ) / m) + X / W) / Real.log 2 := by
    field_simp
  rw [e, show (m : ℝ) * (Real.log d / Real.log 2) = m * Real.log d / Real.log 2 by ring]
  exact div_le_div_of_nonneg_right hmain hl2.le

/-- `log₂ 3 + 3/(2 e log 2) ≤ 3`, in the form used below. -/
theorem log_three_add_le : Real.log 3 + 3 / (2 * Real.exp 1) ≤ 3 * Real.log 2 := by
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have he := Real.exp_one_gt_d9
  have hl := Real.log_two_gt_d9
  have : 3 / (2 * Real.exp 1) ≤ Real.log 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Lemma 4.8, sharp form.** Let `W = d b`, let the labels start in the input cells `src i` and end
in distinct output cells `dst i ∈ [0, dW)` with `⌊(dst i mod W)/b⌋ = ⌊src i/W⌋`, let the heads of the
input tape start in `W` consecutive cells, and let a run of `U` ticks have occupancy at most `κ`. Then
with `m = |ι|` and `K = |η|`,
`m log₂ d ≤ m log₂ 3 + m log₂ ((d + 1) d b/m) + U K κ (K + ρ/W)`. -/
theorem transport_sharp [Fintype ι] (tape : η → τ) (inp out : τ) {H : ℕ → η → ℤ}
    {loc : ℕ → ι → Slot τ ρ} {U κ : ℕ} (hR : IsRun tape H loc U κ) {d b W : ℕ} (hd : 1 ≤ d)
    (hb : 1 ≤ b) (hW : W = d * b) (src dst : ι → ℤ) (hinj : Function.Injective dst)
    (hdst : ∀ i, 0 ≤ dst i ∧ dst i < d * W) (hrow : ∀ i, dst i % W / b = src i / W)
    (h0 : ∀ i, loc 0 i = .inl (inp, src i)) (hU : ∀ i, loc U i = .inl (out, dst i)) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1) (hm : 0 < Fintype.card ι) :
    Fintype.card ι * Real.logb 2 d ≤ Fintype.card ι * Real.logb 2 3 +
      Fintype.card ι * Real.logb 2 (((d + 1) * d * b : ℕ) / Fintype.card ι) +
      U * Fintype.card η * κ * (Fintype.card η + ρ / W) := by
  have hWpos : 0 < W := by rw [hW]; positivity
  have hW' : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ι → ℤ := fun i => src i / W
  obtain ⟨hrun, -⟩ := pot_run hR hWpos A
  have hloc0 : loc 0 = fun i => (Sum.inl (inp, src i) : Slot τ ρ) := funext h0
  have hlocU : loc U = fun i => (Sum.inl (out, dst i) : Slot τ ρ) := funext hU
  rw [hloc0] at hrun
  rw [hlocU] at hrun
  have hst := pot_start_le tape hWpos (H 0) inp src a hwin (ρ := ρ)
  have hen := pot_end_ge tape hb hW (H U) out dst A hinj hdst (fun i => (hrow i).symm) (ρ := ρ)
  have key := transport_of_pot hd hb hW hm (X := U * (Fintype.card η *
    (κ * (Fintype.card η * W + ρ) * Real.log 2))) (by linarith)
  refine key.trans_eq ?_
  congr 1
  field_simp

/-- `m log₂ 3 + m log₂ ((d + 1) d b/m) ≤ 3 d² b` for `0 < m ≤ d² b` and `d ≥ 2`. -/
theorem sharp_terms_le {m d b : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b) (hm : 0 < m) (hmL : m ≤ d * d * b) :
    m * Real.logb 2 3 + m * Real.logb 2 (((d + 1) * d * b : ℕ) / m) ≤ 3 * (d * d * b) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmL' : (m : ℝ) ≤ d * d * b := by exact_mod_cast hmL
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : m * Real.log (((d + 1) * d * b : ℕ) / m) ≤ 3 / (2 * Real.exp 1) * (d * d * b) := by
    have := mul_log_div_le (a := (((d + 1) * d * b : ℕ) : ℝ)) (by push_cast; positivity) hm'
    refine this.trans ?_
    push_cast
    rw [div_le_iff₀ (Real.exp_pos 1)]
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have : ((d : ℝ) + 1) * d * b ≤ 3 / 2 * (d * d * b) := by nlinarith
    calc ((d : ℝ) + 1) * d * b ≤ 3 / 2 * (d * d * b) := this
      _ = 3 / (2 * Real.exp 1) * (d * d * b) * Real.exp 1 := by field_simp
  have h2 : m * Real.log 3 ≤ (d * d * b) * Real.log 3 :=
    mul_le_mul_of_nonneg_right hmL' (Real.log_nonneg (by norm_num))
  have h3 := log_three_add_le
  simp only [Real.logb]
  rw [← sub_nonneg]
  have : 3 * ((d : ℝ) * d * b) - (m * (Real.log 3 / Real.log 2) +
      m * (Real.log (((d + 1) * d * b : ℕ) / m) / Real.log 2)) =
      (3 * Real.log 2 * (d * d * b) - m * Real.log 3 - m * Real.log (((d + 1) * d * b : ℕ) / m)) /
        Real.log 2 := by field_simp; ring
  rw [this]
  apply div_nonneg _ hl2.le
  have hL : (0 : ℝ) ≤ d * d * b := by positivity
  nlinarith

/-- Distinct cells of `[0, dW)` number at most `d W`. -/
theorem card_le_of_cells [Fintype ι] {d W : ℕ} (dst : ι → ℤ) (hinj : Function.Injective dst)
    (hdst : ∀ i, 0 ≤ dst i ∧ dst i < d * W) : Fintype.card ι ≤ d * W := by
  have : (univ.image dst) ⊆ Ico (0 : ℤ) (d * W) := fun z hz => by
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    exact mem_Ico.mpr (hdst i)
  have h1 := card_le_card this
  rw [card_image_of_injective _ hinj, card_univ, Int.card_Ico, sub_zero] at h1
  have : ((d : ℤ) * W).toNat = d * W := by exact_mod_cast Int.toNat_natCast (d * W)
  rwa [this] at h1

/-- **Lemma 4.8.** Under the hypotheses of `transport_sharp`, with `d ≥ 2` and `L = d² b`,
`m log₂ d ≤ κ K (K + ρ) U + 3 L`. -/
theorem transport [Fintype ι] (tape : η → τ) (inp out : τ) {H : ℕ → η → ℤ}
    {loc : ℕ → ι → Slot τ ρ} {U κ : ℕ} (hR : IsRun tape H loc U κ) {d b W : ℕ} (hd : 2 ≤ d)
    (hb : 1 ≤ b) (hW : W = d * b) (src dst : ι → ℤ) (hinj : Function.Injective dst)
    (hdst : ∀ i, 0 ≤ dst i ∧ dst i < d * W) (hrow : ∀ i, dst i % W / b = src i / W)
    (h0 : ∀ i, loc 0 i = .inl (inp, src i)) (hU : ∀ i, loc U i = .inl (out, dst i)) (a : ℤ)
    (hwin : ∀ h, tape h = inp → a ≤ H 0 h ∧ H 0 h ≤ a + W - 1) :
    Fintype.card ι * Real.logb 2 d ≤ κ * Fintype.card η * (Fintype.card η + ρ) * U + 3 * (d * d * b) := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hm0 | hm
  · rw [hm0]; push_cast; simp only [zero_mul]; positivity
  have hs := transport_sharp tape inp out hR (by omega) hb hW src dst hinj hdst hrow h0 hU a hwin hm
  have hmL : Fintype.card ι ≤ d * d * b := by
    have := card_le_of_cells dst hinj hdst; rw [hW] at this; linarith [mul_assoc d d b]
  have hsum := sharp_terms_le hd hb hm hmL
  have hWr : (1 : ℝ) ≤ W := by
    have : 1 ≤ W := by rw [hW]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hρ : (ρ : ℝ) / W ≤ ρ := div_le_self (by positivity) hWr
  have hK : (U : ℝ) * Fintype.card η * κ * (Fintype.card η + ρ / W) ≤
      κ * Fintype.card η * (Fintype.card η + ρ) * U := by
    have : (0 : ℝ) ≤ U * Fintype.card η * κ := by positivity
    nlinarith
  linarith

/-- **Lemma 4.8 with the transposition permutation.** Labels start at distinct input cells
`p ∈ [0, L)`, `L = d² b`, and end at the output cells `tpos p`; the heads of the input tape start in
`[-ω, ω]` with `2ω + 1 ≤ W = d b`. -/
theorem transport_tpos [Fintype ι] (tape : η → τ) (inp out : τ) {H : ℕ → η → ℤ}
    {loc : ℕ → ι → Slot τ ρ} {U κ : ℕ} (hR : IsRun tape H loc U κ) {d b ω : ℕ} (hd : 2 ≤ d)
    (hb : 1 ≤ b) (hω : 2 * ω + 1 ≤ d * b) (src : ι → ℕ) (hinj : Function.Injective src)
    (hsrc : ∀ i, src i < d * d * b) (h0 : ∀ i, loc 0 i = .inl (inp, (src i : ℤ)))
    (hU : ∀ i, loc U i = .inl (out, (tpos d b (src i) : ℤ)))
    (hwin : ∀ h, tape h = inp → -(ω : ℤ) ≤ H 0 h ∧ H 0 h ≤ ω) :
    Fintype.card ι * Real.logb 2 d ≤ κ * Fintype.card η * (Fintype.card η + ρ) * U + 3 * (d * d * b) := by
  have hb0 : 0 < b := by omega
  refine transport tape inp out hR hd hb rfl (fun i => (src i : ℤ)) (fun i => (tpos d b (src i) : ℤ))
    ?_ ?_ ?_ h0 hU (-(ω : ℤ)) ?_
  · intro i j h
    simp only at h
    have h' : tpos d b (src i) = tpos d b (src j) := by exact_mod_cast h
    have := congrArg (tpos d b) h'
    rw [tpos_tpos hb0 (hsrc i), tpos_tpos hb0 (hsrc j)] at this
    exact hinj this
  · intro i
    refine ⟨by positivity, ?_⟩
    have := tpos_lt hb0 (hsrc i)
    push_cast
    have : (tpos d b (src i) : ℤ) < (d * d * b : ℕ) := by exact_mod_cast this
    push_cast at this
    linarith
  · intro i
    have := tpos_row hb0 (hsrc i)
    have h' : ((tpos d b (src i) % (d * b) / b : ℕ) : ℤ) = ((src i / (d * b) : ℕ) : ℤ) := by
      rw [this]
    push_cast at h'
    exact h'
  · intro h hh
    obtain ⟨h1, h2⟩ := hwin h hh
    constructor
    · exact h1
    · push_cast
      have : (2 * ω + 1 : ℤ) ≤ (d * b : ℕ) := by exact_mod_cast hω
      push_cast at this
      linarith

end MergeDepth
