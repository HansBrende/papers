import Transpose.Tape.Passes

/-! Counting moves that meet a bounded old-cell envelope in a monotone pass. -/

namespace PassMemo

open Finset Transpose.Tape Transpose.Tape.Impl

def Marked (h : ℕ → ℤ) (R : ℕ) (t : ℕ) : Prop :=
  h t ≠ h (t + 1) ∧ (|h t| ≤ R ∨ |h (t + 1)| ≤ R)

instance (h : ℕ → ℤ) (R t : ℕ) : Decidable (Marked h R t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem card_marked_up {h : ℕ → ℤ} {a e R : ℕ}
    (hm : ∀ x y, a ≤ x → x ≤ y → y ≤ e → h x ≤ h y)
    (hu : ∀ t, a ≤ t → t < e → |h (t + 1) - h t| ≤ 1) :
    ((Ico a e).filter (Marked h R)).card ≤ 2 * R + 2 := by
  let S := (Ico a e).filter (Marked h R)
  have hinj : Set.InjOn h S := by
    intro x hx y hy heq
    obtain ⟨hxa, hxe⟩ := mem_Ico.mp (mem_filter.mp hx).1
    obtain ⟨hya, hye⟩ := mem_Ico.mp (mem_filter.mp hy).1
    have hxmove := (mem_filter.mp hx).2.1
    have hymove := (mem_filter.mp hy).2.1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · have h1 := hm x (x + 1) hxa (by omega) (by omega)
      have h2 := hm (x + 1) y (by omega) (by omega) (by omega)
      omega
    · have h1 := hm y (y + 1) hya (by omega) (by omega)
      have h2 := hm (y + 1) x (by omega) (by omega) (by omega)
      omega
  have hsub : S.image h ⊆ Icc (-(R : ℤ) - 1) (R : ℤ) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
    obtain ⟨hta, hte⟩ := mem_Ico.mp (mem_filter.mp ht).1
    obtain ⟨hne, hnear⟩ := (mem_filter.mp ht).2
    have hinc := hm t (t + 1) hta (by omega) (by omega)
    have hunit := abs_le.mp (hu t hta hte)
    rw [mem_Icc]
    rcases hnear with hn | hn <;> have hn' := abs_le.mp hn <;> omega
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj, Int.card_Icc] at hc
  change S.card ≤ _
  omega

theorem card_marked {h : ℕ → ℤ} {a e R : ℕ}
    (hm : MonoOn h a e)
    (hu : ∀ t, a ≤ t → t < e → |h (t + 1) - h t| ≤ 1) :
    ((Ico a e).filter (Marked h R)).card ≤ 2 * R + 2 := by
  rcases monoOn_cases hm with hup | hdn
  · exact card_marked_up hup hu
  · have hneg := card_marked_up (h := fun t => -h t) (R := R)
      (fun x y hx hxy hy => neg_le_neg (hdn x y hx hxy hy))
      (fun t ht hte => by
        rw [show -h (t + 1) - -h t = -(h (t + 1) - h t) by ring, abs_neg]
        exact hu t ht hte)
    have heq : (Ico a e).filter (Marked (fun t => -h t) R) =
        (Ico a e).filter (Marked h R) := by
      ext t
      simp [Marked]
    rwa [heq] at hneg

/-- If every unmarked interval has length at most `S`, `m` marked steps
divide the whole interval into at most `m+1` such pieces. -/
theorem interval_length_le {a e S : ℕ} (marks : Finset ℕ)
    (hmarks : marks ⊆ Ico a e) (hae : a ≤ e)
    (hgap : ∀ u v, a ≤ u → u ≤ v → v ≤ e →
      (∀ t ∈ Ico u v, t ∉ marks) → v - u ≤ S) :
    e - a ≤ (marks.card + 1) * S + marks.card := by
  induction marks using Finset.strongInduction generalizing a with
  | H marks ih =>
    by_cases hne : marks.Nonempty
    · let m := marks.min' hne
      have hm : m ∈ marks := min'_mem _ _
      obtain ⟨hma, hme⟩ := mem_Ico.mp (hmarks hm)
      have hfirst : ∀ t ∈ marks, m ≤ t := fun t ht => min'_le _ _ ht
      have hleft : m - a ≤ S := hgap a m le_rfl hma (by omega) (by
        intro t ht htm
        have := hfirst t htm
        have := (mem_Ico.mp ht).2
        omega)
      have htail : marks.erase m ⊆ Ico (m + 1) e := by
        intro t ht
        obtain ⟨htm, htmk⟩ := mem_erase.mp ht
        have htlo := hfirst t htmk
        have hthi := (mem_Ico.mp (hmarks htmk)).2
        exact mem_Ico.mpr ⟨by omega, hthi⟩
      have hbound := ih (marks.erase m) (erase_ssubset hm) htail (by omega) (by
        intro u v hu huv hve hg
        apply hgap u v (by omega) huv hve
        intro t ht htmk
        have htu := (mem_Ico.mp ht).1
        exact hg t ht (mem_erase.mpr ⟨by omega, htmk⟩))
      rw [card_erase_of_mem hm] at hbound
      have hc : 0 < marks.card := card_pos.mpr hne
      have heq : (marks.card - 1 + 1) * S = marks.card * S := by congr 1; omega
      rw [heq] at hbound
      rw [Nat.add_mul, one_mul]
      omega
    · have hempty : marks = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst marks
      simpa using hgap a e le_rfl hae le_rfl (by simp)

end PassMemo
