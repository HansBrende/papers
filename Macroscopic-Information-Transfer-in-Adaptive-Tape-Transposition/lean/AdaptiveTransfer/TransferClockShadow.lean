import AdaptiveTransfer.TransferClock

/-! Point and interval shadows for every head of the actual aligned native
simulation. Closed interval endpoints, the final source step, the extra
terminal batch and the stationary drain are included.
-/

namespace AdaptiveTransfer.TransferClock
open Transpose Transpose.Tape MergeDepth BoundedNesting
open TapeStorageRates TapeStorageRates.Native

private theorem walk_index_bounds {x : ℕ → ℤ} (hx : IsWalk x) {i r s : ℕ}
    (h₁ : r ≤ i + s) (h₂ : i ≤ r + s) :
    -(s : ℤ) ≤ x r - x i ∧ x r - x i ≤ s := by
  rcases le_total i r with hir | hri
  · have hh := hx.lip hir
    omega
  · have hh := hx.lip hri
    omega

/-- Source positions within s source steps of a genuine batch boundary
share that batch's physical three-block window. -/
theorem actual_source_batch_window {M : TM} {s t j r : ℕ} {w : List Bool}
    (hs : 0 < s) (H : HaltsAt M w t) (hj : j ≤ t / s)
    (hr₁ : r ≤ j * s + s) (hr₂ : j * s ≤ r + s) (h : Option (Fin M.k)) :
    let anchor := headPosition (trace (machine M hs) w) h (batchLength s * j)
    anchor - s ≤ headPosition (trace M w) h r ∧
      headPosition (trace M w) h r < anchor + 2 * s := by
  have ho := actual_batch_source_offset hs H hj h
  have hw := walk_index_bounds (headPosition_isWalk (trace M w) h) hr₁ hr₂
  dsimp only
  omega

theorem sourceClock_drain {s t u : ℕ} (hs : 0 < s)
    (hu : batchLength s * (t / s + 1) ≤ u) : sourceClock s t u = t - 1 := by
  have hj : t / s + 1 ≤ u / batchLength s :=
    (Nat.le_div_iff_mul_le (batchLength_pos s)).mpr (by simpa only [Nat.mul_comm] using hu)
  have ht : t < (t / s + 1) * s := by
    have hm := Nat.mod_lt t hs
    have he := Nat.div_add_mod' t s
    nlinarith
  have hjm := Nat.mul_le_mul_right s hj
  unfold sourceClock
  apply min_eq_right
  exact (Nat.sub_le t 1).trans (ht.le.trans (hjm.trans
    (Nat.mul_le_mul_right s (Nat.le_succ _))))

/-- The drain has the stronger radius s around the last live source step. -/
theorem actual_drain_shadow {M : TM} {s t u : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (hu : batchLength s * (t / s + 1) ≤ u) (h : Option (Fin M.k)) :
    |headPosition (trace (machine M hs) w) h u -
      headPosition (trace M w) h (sourceClock s t u)| ≤ s := by
  rw [sourceClock_drain hs hu]
  have he := actual_drain_stationary hs H h (u - batchLength s * (t / s + 1))
  rw [Nat.add_sub_of_le hu] at he
  rw [he]
  have ho := boundary_head_offset hs (actual_terminal_boundary hs H) h
  rw [← headPosition_eq_config M w h t] at ho
  have hw := (headPosition_isWalk (trace M w) h).lip (Nat.sub_le t 1)
  have hd : t - (t - 1) = 1 := by omega
  rw [hd] at hw
  rw [abs_le]
  omega

/-- The exact actual-machine point shadow, for every live physical step
and every corresponding head, including the input head. -/
theorem actual_head_shadow {M : TM} {s t u : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (_hu : u < alignedTime s t) (h : Option (Fin M.k)) :
    |headPosition (trace (machine M hs) w) h u -
      headPosition (trace M w) h (sourceClock s t u)| ≤ 3 * s := by
  by_cases hb : u < batchLength s * (t / s + 1)
  · let j := u / batchLength s
    let i := u % batchLength s
    have hj : j ≤ t / s := by
      have hh := (Nat.div_lt_iff_lt_mul (batchLength_pos s)).mpr
        (by simpa only [Nat.mul_comm] using hb)
      dsimp [j]
      omega
    have hi : i < batchLength s := Nat.mod_lt _ (batchLength_pos s)
    have he : batchLength s * j + i = u := Nat.div_add_mod u (batchLength s)
    have hclock : sourceClock s t u = min ((j + 1) * s) (t - 1) := by
      rw [← he]
      exact sourceClock_batch hi
    have hjs : j * s ≤ t := (Nat.mul_le_mul_right s hj).trans (Nat.div_mul_le_self t s)
    have h₁ : sourceClock s t u ≤ j * s + s := by rw [hclock]; nlinarith [min_le_left ((j + 1) * s) (t - 1)]
    have h₂ : j * s ≤ sourceClock s t u + s := by
      rw [hclock, Nat.add_mul, Nat.one_mul]
      omega
    have hsource := actual_source_batch_window hs H hj h₁ h₂ h
    have hphysical := actual_batch_window hs H hj hi h
    rw [he] at hphysical
    dsimp only at hsource hphysical
    rw [abs_le]
    omega
  · have hh := actual_drain_shadow (u := u) hs ht H (by omega) h
    have hsz : (0 : ℤ) ≤ s := by positivity
    omega

/-- Every source time between the projected endpoints is shadowed inside
the closed physical interval. This is stronger than endpoint shadow alone. -/
theorem actual_interval_shadow {M : TM} {s t v u r : ℕ} {w : List Bool}
    (hs : 0 < s) (ht : 1 ≤ t) (H : HaltsAt M w t)
    (hvu : v ≤ u) (hu : u < alignedTime s t)
    (hrv : sourceClock s t v ≤ r) (hru : r ≤ sourceClock s t u)
    (h : Option (Fin M.k)) :
    ∃ z : ℕ, v ≤ z ∧ z ≤ u ∧
      |headPosition (trace (machine M hs) w) h z - headPosition (trace M w) h r| ≤ 3 * s := by
  by_cases hev : r = sourceClock s t v
  · refine ⟨v, le_rfl, hvu, ?_⟩
    rw [hev]
    exact actual_head_shadow hs ht H (hvu.trans_lt hu) h
  by_cases heu : r = sourceClock s t u
  · refine ⟨u, hvu, le_rfl, ?_⟩
    rw [heu]
    exact actual_head_shadow hs ht H hu h
  have hvstrict : sourceClock s t v < r := by omega
  have hustrict : r < sourceClock s t u := by omega
  have hrpos : 1 ≤ r := by omega
  have hrt : r ≤ t - 1 := hru.trans (min_le_right _ _)
  let j := (r - 1) / s
  have hjs : j * s ≤ r - 1 := Nat.div_mul_le_self _ _
  have hrjs : r ≤ j * s + s := by
    have hm := Nat.mod_lt (r - 1) hs
    have he := Nat.div_add_mod' (r - 1) s
    dsimp [j]
    omega
  have hj : j ≤ t / s := Nat.div_le_div_right (by omega : r - 1 ≤ t)
  have hvstart : (v / batchLength s + 1) * s < r := by
    unfold sourceClock at hvstrict
    omega
  have hvj : v / batchLength s + 1 ≤ j :=
    (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have hvend : v < (v / batchLength s + 1) * batchLength s := by
    have hm := Nat.mod_lt v (batchLength_pos s)
    have he := Nat.div_add_mod' v (batchLength s)
    nlinarith
  have hvz : v ≤ batchLength s * j := by
    have hh := Nat.mul_le_mul_right (batchLength s) hvj
    nlinarith
  have hur : r ≤ (u / batchLength s + 1) * s := hru.trans (min_le_left _ _)
  have hju : j ≤ u / batchLength s := by
    have hh := (Nat.div_lt_iff_lt_mul hs).mpr (show r - 1 < (u / batchLength s + 1) * s by omega)
    dsimp [j]
    omega
  have hzu : batchLength s * j ≤ u := by
    exact (Nat.mul_le_mul_left (batchLength s) hju).trans (Nat.mul_div_le u (batchLength s))
  refine ⟨batchLength s * j, hvz, hzu, ?_⟩
  have hw := actual_source_batch_window hs H hj hrjs (show j * s ≤ r + s by omega) h
  dsimp only at hw
  rw [abs_le]
  omega

end AdaptiveTransfer.TransferClock
