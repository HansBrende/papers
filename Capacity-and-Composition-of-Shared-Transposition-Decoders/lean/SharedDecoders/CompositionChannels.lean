import SharedDecoders.CompositionLinear

/-! # Common messages in an actual cyclic channel space -/

namespace SharedDecoders

open Module

variable {F A Z I κ : Type*} [Field F] [AddCommGroup A] [Module F A]
  [AddCommGroup Z] [Module F Z] {d : ℕ} [NeZero d]

def channelRotation (s : ZMod d) : (I → ZMod d → A) →ₗ[F] (I → ZMod d → A) where
  toFun x i j := x i (j + s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero d] in
theorem channelRotation_add (s t : ZMod d) (x : I → ZMod d → A) :
    channelRotation (F := F) s (channelRotation (F := F) t x) =
      channelRotation (F := F) (s + t) x := by
  funext i j
  simp [channelRotation, add_assoc]

omit [NeZero d] in
theorem channelRotation_pow (s : ZMod d) (n : ℕ) (x : I → ZMod d → A) :
    (channelRotation (F := F) s ^ n) x =
      channelRotation (F := F) ((n : ZMod d) * s) x := by
  induction n with
  | zero => funext i j; simp [channelRotation]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, channelRotation_add]
      have he : s + (n : ZMod d) * s = ((n + 1 : ℕ) : ZMod d) * s := by
        push_cast
        ring
      rw [he]

def channelFixedRestriction (s : ℕ) :
    LinearMap.ker (channelRotation (F := F) (I := I) (A := A) (s : ZMod d) -
      LinearMap.id) →ₗ[F] (I → Fin s → A) where
  toFun x i j := x.val i (j.val : ZMod d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem channelFixedRestriction_injective {s : ℕ} (hs : 0 < s) :
    Function.Injective (channelFixedRestriction (F := F) (I := I) (A := A)
      (d := d) s) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hf : channelRotation (F := F) (s : ZMod d) x.val = x.val :=
    sub_eq_zero.mp x.property
  apply Subtype.ext
  funext i
  apply fixed_word_zero_of_prefix hs
  · intro j
    exact congrFun (congrFun hf i) j
  · intro j hj
    exact congrFun (congrFun hx i) ⟨j, hj⟩

theorem channel_fixed_finrank_le [Fintype I] [FiniteDimensional F A]
    {s : ℕ} (hs : 0 < s) :
    finrank F (LinearMap.ker (channelRotation (F := F) (I := I) (A := A)
      (d := d) (s : ZMod d) - LinearMap.id)) ≤
      Fintype.card I * s * finrank F A := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (channelFixedRestriction_injective (F := F) (I := I) (A := A) (d := d) hs)
  simpa [Module.finrank_pi_fintype, mul_assoc] using h

/-- A finite Ramsey interval bounds the actual common-message source. The
message decoder need not extend to an injective map on the whole ambient. -/
theorem commonMessage_interval_bound [Fintype I] [FiniteDimensional F A]
    (N ell : ℕ) (hell : 0 < ell)
    (hRamsey : ∀ C : ℕ → κ, ∃ a s : ℕ, 0 < s ∧
      ∀ j < ell, a + s * j < N ∧ C (a + s * j) = C a)
    (p : ZMod d → κ) (W : Submodule F (I → ZMod d → A))
    (B : W →ₗ[F] Z) (hB : Function.Injective B)
    (f : κ → (I → ZMod d → A) →ₗ[F] Z)
    (hcorrect : ∀ c (x : W), f (p c) (channelRotation (F := F) c x.val) = B x) :
    ell * finrank F W ≤ (Fintype.card I * finrank F A) * (d + (N - 1)) := by
  classical
  obtain ⟨a, s, hs, hprog⟩ := hRamsey (fun n => p (n : ZMod d))
  let R := channelRotation (F := F) (I := I) (A := A) (s : ZMod d)
  let L := (f (p (a : ZMod d))).comp (channelRotation (a : ZMod d))
  have hmono (j : ℕ) (hj : j < ell) :
      p ((a : ZMod d) + (j : ZMod d) * (s : ZMod d)) = p (a : ZMod d) := by
    simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using (hprog j hj).2
  have hobs (j : ℕ) (hj : j < ell) (x : W) : L ((R ^ j) x.val) = B x := by
    change f (p (a : ZMod d)) (channelRotation (F := F) (a : ZMod d)
      ((channelRotation (F := F) (s : ZMod d) ^ j) x.val)) = B x
    rw [channelRotation_pow, channelRotation_add]
    rw [← hmono j hj]
    exact hcorrect _ x
  have hinj : ∀ x ∈ W, L x = 0 → x = 0 := by
    intro x hx hz
    have hb : B (⟨x, hx⟩ : W) = 0 := by simpa using (hobs 0 hell ⟨x, hx⟩).symm.trans hz
    have he : (⟨x, hx⟩ : W) = 0 := hB (hb.trans (map_zero B).symm)
    exact congrArg Subtype.val he
  have hmsg : ∀ j < ell, ∀ x ∈ W, L ((R ^ j) x) = L x := by
    intro j hj x hx
    exact (hobs j hj ⟨x, hx⟩).trans (by simpa using (hobs 0 hell ⟨x, hx⟩).symm)
  have hg := commonMessage_finrank_le R W L ell hell hinj hmsg
  have hfixed := channel_fixed_finrank_le (F := F) (I := I) (A := A) (d := d) hs
  have hlast := (hprog (ell - 1) (by omega)).1
  have hstep : (ell - 1) * s ≤ N - 1 := by
    have : s * (ell - 1) ≤ N - 1 := by omega
    simpa [mul_comm] using this
  have hstep' := Nat.mul_le_mul_left (Fintype.card I * finrank F A) hstep
  have hbound := Nat.add_le_add_left (Nat.mul_le_mul_left (ell - 1) hfixed)
    (finrank F (I → ZMod d → A))
  have htotal := hg.trans hbound
  simp [Module.finrank_pi_fintype, ZMod.card] at htotal
  nlinarith

end SharedDecoders
