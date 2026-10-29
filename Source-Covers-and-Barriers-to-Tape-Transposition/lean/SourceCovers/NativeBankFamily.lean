import SourceCovers.NativeBankReturns
import SourceCovers.ShadowInvariants

set_option autoImplicit false

/-! Each turn's complete actual family follows from the bank walk.
Only that family's outer return must lie before the horizon. -/

namespace SourceCovers.NativeBank

open Finset BoundedNesting
noncomputable section

variable {h D n k T : ℕ} [NeZero h] {xs : Fin k → ℕ → ℤ}

/-- The outer return witnesses the canonical key. -/
def family (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) : ActualFamily xs T :=
  ⟨(head, decide (q.val = 0), turnOwner h D r q), mem_image.mpr
    ⟨(head, turnOwner h D r q - h, turnOwner h D r q + h), mem_allHops.mpr (by
      rw [hx]
      exact turn_hop r.isLt q (NeZero.pos h) le_rfl hT),
      turn_key hx r.isLt q (NeZero.pos h) le_rfl hT⟩⟩

theorem family_hops (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) :
    (family head hx r q hT).hops =
      univ.image (fun a : Fin h =>
        (head, turnOwner h D r q - (a.val + 1), turnOwner h D r q + (a.val + 1))) := by
  ext η
  constructor
  · intro hη
    obtain ⟨hHop, hhead, _, howner⟩ := mem_fam.mp hη
    have hh := mem_allHops.mp hHop
    change η.1 = head at hhead
    rw [hhead, hx, hop_iff_radius] at hh
    obtain ⟨ht, r', q', a, hp, hu⟩ := hh
    change actualOwner xs η = turnOwner h D r q at howner
    have ho : turnOwner h D r' q' = turnOwner h D r q := by
      rw [actualOwner, hhead, hx, hp, hu,
        turn_owner r'.isLt q' (by omega) (by have := a.isLt; omega) (hu ▸ ht)] at howner
      exact howner
    have he := @turnOwner_injective h D (NeZero.pos h) (r'.val, q') (r.val, q) ho
    have hr' : r' = r := Fin.ext (congrArg Prod.fst he)
    have hq' : q' = q := congrArg Prod.snd he
    subst r' q'
    exact mem_image.mpr ⟨a, mem_univ a, Prod.ext hhead.symm (Prod.ext hp.symm hu.symm)⟩
  · rintro hη
    obtain ⟨a, _, rfl⟩ := mem_image.mp hη
    have ha : a.val + 1 ≤ h := by have := a.isLt; omega
    have ht : turnOwner h D r q + (a.val + 1) < T := by omega
    apply mem_filter.mpr
    refine ⟨mem_allHops.mpr ?_, turn_key hx r.isLt q (by omega) ha ht⟩
    rw [hx]
    exact turn_hop r.isLt q (by omega) ha ht

theorem family_card (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) : (family head hx r q hT).hops.card = h := by
  rw [family_hops, card_image_of_injective]
  · simp
  · intro a b he
    have he' := congrArg (fun η : Fin k × ℕ × ℕ => η.2.2) he
    exact Fin.ext (by dsimp only at he'; omega)

theorem mem_family (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) (a : Fin h) :
    (head, turnOwner h D r q - (a.val + 1), turnOwner h D r q + (a.val + 1)) ∈
      (family head hx r q hT).hops := by
  rw [family_hops]
  exact mem_image.mpr ⟨a, mem_univ _, rfl⟩

theorem mem_family_outer (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) :
    (head, turnOwner h D r q - h, turnOwner h D r q + h) ∈
      (family head hx r q hT).hops := by
  let a : Fin h := ⟨h - 1, by have := NeZero.pos h; omega⟩
  have he : a.val + 1 = h := by have := NeZero.pos h; dsimp only [a]; omega
  simpa only [he] using mem_family head hx r q hT a

theorem family_start (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) :
    (family head hx r q hT).start = turnOwner h D r q - h := by
  change (family head hx r q hT).hops.inf' (family head hx r q hT).nonempty
    (fun η : Fin k × ℕ × ℕ => η.2.1) = _
  apply le_antisymm
  · exact inf'_le (fun η : Fin k × ℕ × ℕ => η.2.1) (mem_family_outer head hx r q hT)
  · apply le_inf'
    intro η hη
    rw [family_hops] at hη
    obtain ⟨a, _, rfl⟩ := mem_image.mp hη
    have := a.isLt
    dsimp only
    omega

theorem family_stop (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) :
    (family head hx r q hT).stop = turnOwner h D r q + h := by
  change (family head hx r q hT).hops.sup (fun η : Fin k × ℕ × ℕ => η.2.2) = _
  apply le_antisymm
  · apply Finset.sup_le
    intro η hη
    rw [family_hops] at hη
    obtain ⟨a, _, rfl⟩ := mem_image.mp hη
    have := a.isLt
    dsimp only
    omega
  · exact Finset.le_sup (s := (family head hx r q hT).hops) (f := fun η => η.2.2)
      (mem_family_outer head hx r q hT)

@[simp] theorem family_owner (head : Fin k) (hx : xs head = walk h D n) (r : Fin n) (q : Fin 2)
    (hT : turnOwner h D r q + h < T) : (family head hx r q hT).owner = turnOwner h D r q := rfl

/-- Every time on the active half-span is a return endpoint, so its
strictly clipped shadow has the exact reflection formula. -/
theorem family_shadow_active (head : Fin k) (hx : xs head = walk h D n)
    (r : Fin n) (q : Fin 2) (hT : turnOwner h D r q + h < T)
    (hxs : ∀ i, IsWalk (xs i)) {t : ℕ}
    (ht : turnOwner h D r q < t) (hu : t ≤ turnOwner h D r q + h) :
    (family head hx r q hT).shadow t =
      max (turnOwner h D r q - h + 1) (2 * turnOwner h D r q - t) := by
  let a : Fin h := ⟨t - turnOwner h D r q - 1, by omega⟩
  have he : turnOwner h D r q + (a.val + 1) = t := by dsimp only [a]; omega
  have hp : turnOwner h D r q - (a.val + 1) = 2 * turnOwner h D r q - t := by
    dsimp only [a]
    omega
  have hs := (family head hx r q hT).shadow_at_hop hxs (mem_family head hx r q hT a)
  simpa only [family_start, he, hp] using hs

/-- Exhaustiveness holds once all outer returns of this head have occurred. -/
theorem family_exhaustive (head : Fin k) (hx : xs head = walk h D n)
    (hT : ∀ r : Fin n, ∀ q : Fin 2, turnOwner h D r q + h < T)
    (F : ActualFamily xs T) (hhead : F.val.1 = head) :
    ∃ r : Fin n, ∃ q : Fin 2, F = family head hx r q (hT r q) := by
  obtain ⟨η, hη⟩ := F.nonempty
  obtain ⟨hHop, hηhead, _, _⟩ := mem_fam.mp hη
  have hh := mem_allHops.mp hHop
  have he : η.1 = head := hηhead.trans hhead
  rw [he, hx, hop_iff_radius] at hh
  obtain ⟨ht, r, q, a, hp, hu⟩ := hh
  refine ⟨r, q, Subtype.ext ?_⟩
  have hk := (mem_filter.mp hη).2
  rw [show η = (head, turnOwner h D r q - (a.val + 1), turnOwner h D r q + (a.val + 1))
    from Prod.ext he (Prod.ext hp hu),
    turn_key hx r.isLt q (by omega) (by have := a.isLt; omega) (hu ▸ ht)] at hk
  exact hk.symm

end
end SourceCovers.NativeBank
