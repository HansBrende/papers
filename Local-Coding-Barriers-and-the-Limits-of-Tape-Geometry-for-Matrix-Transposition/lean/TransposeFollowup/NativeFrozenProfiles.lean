import TransposeFollowup.FrozenLocalProfiles

/-! Exact local/global physical scaling and representation-independent frozen
profiles of actual integer-time stages. Charged volumes may be positive reals. -/
namespace TransposeFollowup.RegularMotion
open Classical Set Filter Topology
set_option autoImplicit false

theorem frozenProfile_physicalPath {P V : ℝ} (hP : P ≠ 0) (hV : V ≠ 0)
    (f : ℝ → ℝ) (A ell s : ℝ) :
    frozenProfile (physicalPath P f) (A/P) (V/P) ell s =
      (f (A+V*min s ell)-f A)/V := by
  have harg : P*(A/P+(V/P)*min s ell)=A+V*min s ell := by field_simp
  have hbase : P*(A/P)=A := by field_simp
  simp only [frozenProfile,physicalPath,harg,hbase]
  field_simp

theorem native_frozen_profile_sample_error {P V : ℝ} (hP : 0 < P) (hV : 0 < V)
    {h : ℕ → ℤ} {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (he : ∀ m : ℕ, f m=(h m : ℝ)) (A L : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    |frozenProfile (physicalPath P f) ((A : ℝ)/P) (V/P) ((L : ℝ)/V) s -
      ((h (A+min ⌊V*s⌋₊ L)-h A : ℤ) : ℝ)/V| ≤ 1/V := by
  have hn : 0 ≤ V*min s ((L : ℝ)/V) :=
    mul_nonneg hV.le (le_min hs (div_nonneg (Nat.cast_nonneg _) hV.le))
  have hc : V*((L : ℝ)/V)=(L : ℝ) := by field_simp
  have hfloor : ⌊(A : ℝ)+V*min s ((L : ℝ)/V)⌋₊=A+min ⌊V*s⌋₊ L := by
    rw [add_comm,Nat.floor_add_natCast hn,mul_min_of_nonneg _ _ hV.le,hc,
      Nat.floor_mono.map_min,Nat.floor_natCast,add_comm]
  have herr := real_walk_floor_error hf he (add_nonneg (Nat.cast_nonneg A) hn)
  rw [hfloor] at herr
  rw [frozenProfile_physicalPath hP.ne' hV.ne',he A]
  push_cast
  rw [← sub_div,
    show (f ((A : ℝ)+V*min s ((L : ℝ)/V))-(h A : ℝ))-
      ((h (A+min ⌊V*s⌋₊ L) : ℝ)-(h A : ℝ))=
      f ((A : ℝ)+V*min s ((L : ℝ)/V))-(h (A+min ⌊V*s⌋₊ L) : ℝ) by ring,
    abs_div,abs_of_pos hV]
  exact div_le_div_of_nonneg_right herr hV.le

theorem native_frozen_profile_distance {P V : ℝ} (hP : 0 < P) (hV : 0 < V)
    {h : ℕ → ℤ} {f g : ℝ → ℝ} (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (he : ∀ m : ℕ, f m=(h m : ℝ)) (he' : ∀ m : ℕ, g m=(h m : ℝ))
    (A L : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    dist (frozenProfile (physicalPath P f) ((A : ℝ)/P) (V/P) ((L : ℝ)/V) s)
      (frozenProfile (physicalPath P g) ((A : ℝ)/P) (V/P) ((L : ℝ)/V) s) ≤ 2/V := by
  let q : ℝ := ((h (A+min ⌊V*s⌋₊ L)-h A : ℤ) : ℝ)/V
  calc
    _ ≤ dist (frozenProfile (physicalPath P f) ((A : ℝ)/P) (V/P) ((L : ℝ)/V) s) q +
        dist q (frozenProfile (physicalPath P g) ((A : ℝ)/P) (V/P) ((L : ℝ)/V) s) :=
      dist_triangle _ q _
    _ ≤ 1/V+1/V := add_le_add
      (native_frozen_profile_sample_error hP hV hf he A L hs)
      (by rw [dist_comm]; exact native_frozen_profile_sample_error hP hV hg he' A L hs)
    _ = 2/V := by ring

theorem native_frozen_limit_independent {Ps Vs : ℕ → ℝ}
    (hP : ∀ i, 0 < Ps i) (hV : ∀ i, 0 < Vs i) (hVinf : Tendsto Vs atTop atTop)
    {hs : ℕ → ℕ → ℤ} {fs gs : ℕ → ℝ → ℝ}
    (hf : ∀ i, LipschitzWith 1 (fs i)) (hg : ∀ i, LipschitzWith 1 (gs i))
    (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (he' : ∀ i (m : ℕ), gs i m=(hs i m : ℝ)) (A L : ℕ → ℕ)
    {a : ℝ} {q : ℝ → ℝ}
    (hconv : TendstoUniformlyOn (fun i => frozenProfile (physicalPath (Ps i) (fs i))
      ((A i : ℝ)/Ps i) (Vs i/Ps i) ((L i : ℝ)/Vs i)) q atTop (Icc 0 a)) :
    TendstoUniformlyOn (fun i => frozenProfile (physicalPath (Ps i) (gs i))
      ((A i : ℝ)/Ps i) (Vs i/Ps i) ((L i : ℝ)/Vs i)) q atTop (Icc 0 a) := by
  apply uniform_limit_of_vanishing_error hconv (e:=fun i => 2/Vs i)
    (tendsto_const_nhds.div_atTop hVinf)
  exact Eventually.of_forall fun i s hs =>
    native_frozen_profile_distance (hP i) (hV i) (hf i) (hg i) (he i) (he' i) (A i) (L i) hs.1

theorem native_frozen_sampled_limit_iff {Ps Vs : ℕ → ℝ}
    (hP : ∀ i, 0 < Ps i) (hV : ∀ i, 0 < Vs i) (hVinf : Tendsto Vs atTop atTop)
    {hs : ℕ → ℕ → ℤ} {fs : ℕ → ℝ → ℝ}
    (hf : ∀ i, LipschitzWith 1 (fs i)) (he : ∀ i (m : ℕ), fs i m=(hs i m : ℝ))
    (A L : ℕ → ℕ) {a : ℝ} {q : ℝ → ℝ} :
    TendstoUniformlyOn (fun i => frozenProfile (physicalPath (Ps i) (fs i))
      ((A i : ℝ)/Ps i) (Vs i/Ps i) ((L i : ℝ)/Vs i)) q atTop (Icc 0 a) ↔
    TendstoUniformlyOn (fun i s =>
      ((hs i (A i+min ⌊Vs i*s⌋₊ (L i))-hs i (A i) : ℤ) : ℝ)/Vs i)
      q atTop (Icc 0 a) := by
  have he0 : Tendsto (fun i => 1/Vs i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hVinf
  have hd : ∀ᶠ i in atTop, ∀ s ∈ Icc (0 : ℝ) a,
      dist (frozenProfile (physicalPath (Ps i) (fs i))
        ((A i : ℝ)/Ps i) (Vs i/Ps i) ((L i : ℝ)/Vs i) s)
        (((hs i (A i+min ⌊Vs i*s⌋₊ (L i))-hs i (A i) : ℤ) : ℝ)/Vs i) ≤ 1/Vs i :=
    Eventually.of_forall fun i s hs =>
      native_frozen_profile_sample_error (hP i) (hV i) (hf i) (he i) (A i) (L i) hs.1
  exact ⟨fun h => uniform_limit_of_vanishing_error h he0 hd,
    fun h => uniform_limit_of_vanishing_error h he0
      (hd.mono fun i hi s hs => by simpa only [dist_comm] using hi s hs)⟩

end TransposeFollowup.RegularMotion
