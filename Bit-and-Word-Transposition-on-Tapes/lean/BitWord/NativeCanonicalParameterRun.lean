import BitWord.NativeCanonicalParameterCalls

namespace BitWord.NativeCanonicalParameters
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def bank (h : ℕ) (u base wide zero inc half double total diff : Tape Bool) : Bank
  | .h => Counter.marked (hword h) | .u => u | .base => base | .wide => wide
  | .zero => zero | .inc => inc | .half => half | .double => double | .total => total | .diff => diff
  | _ => ⟨[],[]⟩

@[simp] theorem initial_bank (h : ℕ) : initial h=bank h ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ := by
  funext p; cases p <;> rfl

@[simp] theorem update_u (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .u x=bank h x base wide zero inc half double total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_base (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .base x=bank h u x wide zero inc half double total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_wide (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .wide x=bank h u base x zero inc half double total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_zero (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .zero x=bank h u base wide x inc half double total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_inc (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .inc x=bank h u base wide zero x half double total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_half (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .half x=bank h u base wide zero inc x double total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_double (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .double x=bank h u base wide zero inc half x total diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_total (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .total x=bank h u base wide zero inc half double x diff := by
  funext p; cases p <;> rfl
@[simp] theorem update_diff (h : ℕ) (u base wide zero inc half double total diff x : Tape Bool) :
    Function.update (bank h u base wide zero inc half double total diff) .diff x=bank h u base wide zero inc half double total x := by
  funext p; cases p <;> rfl

def prepared (h : ℕ) := bank h (Counter.marked (uword h)) (Counter.marked (H h))
  (Counter.marked (U h)) (Counter.marked (zero h)) ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩

theorem prepare_trace (h : ℕ) (hh : 2 ≤ h) (pos : Port → ℤ) :
    ∃ t ≤ 80*h+30*laneBits h+200, Trace t (cfg start (initial h) pos)
      (cfg (.init .increment (.erase 0)) (prepared h) pos) := by
  let e : Tape Bool := ⟨[],[]⟩
  let b1 := bank h (Counter.marked (uword h)) e e e e e e e e
  let b2 := bank h (Counter.marked (uword h)) (Counter.marked (H h)) e e e e e e e
  let b3 := bank h (Counter.marked (uword h)) (Counter.marked (H h)) (Counter.marked (U h)) e e e e e e
  obtain ⟨a,ha,ta⟩ := entry_call h hh (initial h) pos rfl rfl rfl rfl
  simp only [initial_bank,update_u] at ta
  rw [←initial_bank] at ta
  have ja := jump (.entry .done) (.pad false (NativeCrossPad.start 2)) b1 pos rfl
  obtain ⟨b,hb,tb⟩ := pad_call false (hword h) (uword h) b1 pos rfl rfl rfl
  change Trace b (cfg (.pad false (NativeCrossPad.start 2)) b1 pos)
    (cfg (.pad false (.tail (.seal .done))) (Function.update b1 .base (Counter.marked (H h))) pos) at tb
  simp only [b1,update_base] at tb
  have jb := jump (.pad false (.tail (.seal .done))) (.pad true (NativeCrossPad.start 3)) b2 pos rfl
  obtain ⟨c,hc,tc⟩ := pad_call true (uword h) (hword h) b2 pos rfl rfl rfl
  change Trace c (cfg (.pad true (NativeCrossPad.start 3)) b2 pos)
    (cfg (.pad true (.tail (.seal .done))) (Function.update b2 .wide (Counter.marked (U h))) pos) at tc
  simp only [b2,update_wide] at tc
  have jc := jump (.pad true (.tail (.seal .done))) (.copy false (.init (.erase 0))) b3 pos rfl
  obtain ⟨d,hd,td⟩ := copy_call false (U h) b3 pos rfl rfl
  change Trace d (cfg (.copy false (.init (.erase 0))) b3 pos)
    (cfg (.copy false (.seal .done)) (Function.update b3 .zero (Counter.marked (zero h))) pos) at td
  simp only [b3,update_zero] at td
  have jd := jump (.copy false (.seal .done)) (.init .increment (.erase 0)) (prepared h) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb
    (trace_trans tc (trace_trans jc (trace_trans td jd))))))⟩
  simp only [hword_length,uword_length,padding,Bool.false_eq_true,↓reduceIte,U_length,width] at hb hc hd
  omega

theorem compute_call (o : Op) (xs ys : List Bool) (hlen : xs.length=ys.length)
    (s : Bank) (pos : Port → ℤ)
    (hx : s (operands o 0)=Counter.marked xs)
    (hy : s (operands o 1)=Counter.marked ys)
    (hz : s (output o)=⟨[],[]⟩) :
    ∃ t ≤ 5*xs.length+11, Trace t (cfg (.init o (.erase 0)) s pos)
      (cfg (after o) (Function.update s (output o)
        (Counter.marked (BinaryCarry.result (sub o) (carry o) xs ys).1)) pos) := by
  let s1 := Function.update s (output o) (NativeSealBack.openWord [])
  obtain ⟨a,ha,ta⟩ := NativeTapeCalls.initialize_call program (output o) (Label.init o) (init_code o) s pos hz
  have ja := jump (.init o .done) (.arithmetic o (.scan (sub o) (carry o))) s1 pos rfl
  obtain ⟨b,hb,tb⟩ := arithmetic_call o xs ys hlen s1 pos
    (by cases o <;> simpa [s1,operands,output] using hx)
    (by cases o <;> simpa [s1,operands,output] using hy)
    (by cases o <;> simp [s1,operands,output])
  have ho : operands o 2=output o := by cases o <;> rfl
  rw [ho] at tb
  simp only [s1,Function.update_idem] at tb
  have jb := jump (.arithmetic o (.done (BinaryCarry.result (sub o) (carry o) xs ys).2))
    (after o) (Function.update s (output o) (Counter.marked (BinaryCarry.result (sub o) (carry o) xs ys).1)) pos rfl
  exact ⟨_,by omega,trace_trans ta (trace_trans ja (trace_trans tb jb))⟩

def shifted (pos : Port → ℤ) := Function.update pos .inc (pos .inc+1)
def halved (h : ℕ) := bank h (Counter.marked (uword h)) (Counter.marked (H h))
  (Counter.marked (U h)) (Counter.marked (zero h)) (Counter.marked (V h)) (Counter.marked (V h))
  ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩

theorem halve_increment_call (h : ℕ) (s : Bank) (pos : Port → ℤ)
    (hs : s .inc=Counter.marked (increment h)) :
    ∃ t ≤ 3, Trace t (cfg (.halve .left) s pos)
      (cfg (.halve .done) (Function.update s .inc (Counter.marked (V h))) (shifted pos)) := by
  have hn : increment h ≠ [] := by intro hz; have := increment_length h; simp [hz] at this
  cases he : increment h with
  | nil => exact False.elim (hn he)
  | cons a xs =>
    have hv : V h=xs := by simp [V,he]
    simpa only [hv,shifted] using half_call a xs s pos (by simpa only [he] using hs)

theorem halved_trace (h : ℕ) (pos : Port → ℤ) :
    ∃ t ≤ 11*width h+35, Trace t (cfg (.init .increment (.erase 0)) (prepared h) pos)
      (cfg (.init .double (.erase 0)) (halved h) (shifted pos)) := by
  let b1 := Function.update (prepared h) .inc (Counter.marked (increment h))
  let b2 := Function.update b1 .inc (Counter.marked (V h))
  obtain ⟨a,ha,ta⟩ := compute_call .increment (U h) (zero h) (by simp) (prepared h) pos rfl rfl rfl
  change Trace a (cfg (.init .increment (.erase 0)) (prepared h) pos) (cfg (.halve .left) b1 pos) at ta
  obtain ⟨b,hb,tb⟩ := halve_increment_call h b1 pos (by simp [b1])
  have jb := jump (.halve .done) (.copy true (.init (.erase 0))) b2 (shifted pos) rfl
  obtain ⟨c,hc,tc⟩ := copy_call true (V h) b2 (shifted pos) (by simp [b2,copyBinding,pairBinding]) (by simp [b2,b1,prepared,copyBinding,pairBinding,bank])
  have he : Function.update b2 ((copyBinding true).ports 1) (Counter.marked ((V h).map (copyMap true)))=halved h := by
    simp [b2,b1,prepared,copyBinding,pairBinding,copyMap,halved]
  rw [he] at tc
  have jc := jump (.copy true (.seal .done)) (.init .double (.erase 0)) (halved h) (shifted pos) rfl
  refine ⟨_,?_,trace_trans ta (trace_trans tb (trace_trans jb (trace_trans tc jc)))⟩
  simp only [U_length,V_length] at ha hc
  omega

def calculated (h : ℕ) := bank h (Counter.marked (uword h)) (Counter.marked (H h))
  (Counter.marked (U h)) (Counter.marked (zero h)) (Counter.marked (V h)) (Counter.marked (V h))
  (Counter.marked (W h)) (Counter.marked (N h)) (Counter.marked (R h))

theorem calculate_trace (h : ℕ) (pos : Port → ℤ) :
    ∃ t ≤ 15*width h+33, Trace t
      (cfg (.init .double (.erase 0)) (halved h) pos)
      (cfg (.eraseInc 2) (calculated h) pos) := by
  let b1 := Function.update (halved h) .double (Counter.marked (W h))
  let b2 := Function.update b1 .total (Counter.marked (N h))
  obtain ⟨a,ha,ta⟩ := compute_call .double (V h) (V h) rfl (halved h) pos rfl rfl rfl
  change Trace a (cfg (.init .double (.erase 0)) (halved h) pos) (cfg (.init .total (.erase 0)) b1 pos) at ta
  obtain ⟨b,hb,tb⟩ := compute_call .total (H h) (V h) (by simp) b1 pos rfl rfl rfl
  change Trace b (cfg (.init .total (.erase 0)) b1 pos) (cfg (.init .diff (.erase 0)) b2 pos) at tb
  obtain ⟨c,hc,tc⟩ := compute_call .diff (H h) (V h) (by simp) b2 pos rfl rfl rfl
  have he : Function.update b2 .diff (Counter.marked (R h))=calculated h := by
    simp [b2,b1,halved,calculated]
  change Trace c (cfg (.init .diff (.erase 0)) b2 pos)
    (cfg (.eraseInc 2) (Function.update b2 .diff (Counter.marked (R h))) pos) at tc
  rw [he] at tc
  refine ⟨_,?_,trace_trans ta (trace_trans tb tc)⟩
  simp only [V_length,H_length] at ha hb hc
  omega

theorem resetInc_step (s : Bank) (pos : Port → ℤ) (hs : s .inc=⟨[],[]⟩) :
    NativeMicrocode.step program (cfg .resetInc s (shifted pos))=
      cfg (.erase (NativeBatchErase.entry 4 0)) s pos := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,cfg,workCfg]
  congr 1
  · congr 1
    funext p; cases p <;>
      simp [Microcode.single,Microcode.Action.actual,hs,Tape.denote,Turing.Tape.mk₂]
    exact congrArg (Turing.Tape.mk' (Turing.ListBlank.mk [])) (EraseStream.blanks_eq_nil 1)
  · funext p; cases p <;>
      simp [Microcode.single,shifted,NativeMicrocode.direction,Transpose.Dir.shift]

theorem resetInc_trace (s : Bank) (pos : Port → ℤ) (hs : s .inc=⟨[],[]⟩) :
    Trace 1 (cfg .resetInc s (shifted pos)) (cfg (.erase (NativeBatchErase.entry 4 0)) s pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,workCfg,program]
  · rw [resetInc_step s pos hs]
    exact .refl _

theorem cleanup_trace (h : ℕ) (pos : Port → ℤ) :
    ∃ t ≤ 20*width h+35, Trace t (cfg (.eraseInc 2) (calculated h) (shifted pos))
      (cfg .done (final h) pos) := by
  let s := Function.update (calculated h) .inc (⟨[],[]⟩ : Tape Bool)
  let words : Fin 4 → List Bool := ![H h,U h,zero h,V h]
  obtain ⟨a,ha,ta⟩ := NativeTapeCalls.erase program .inc Label.eraseInc eraseInc_code
    (calculated h) (shifted pos) (V h) rfl
  have ja := jump (.eraseInc 0) .resetInc s (shifted pos) rfl
  have tb := resetInc_trace s pos (by simp [s])
  obtain ⟨c,hc,tc⟩ := batch_erase_call words s pos (by
    intro j; fin_cases j <;> simp [s,words,erasePorts,calculated,bank])
  have hf : NativeBatchErase.stage erasePorts s 4=final h := by
    funext p; cases p <;> simp [NativeBatchErase.stage,erasePorts,Fin.exists_fin_succ,s,calculated,bank,final]
  rw [hf] at tc
  have jc := jump (.erase .done) .done (final h) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans tc jc)))⟩
  simp only [V_length] at ha
  simp [words,Fin.sum_univ_succ] at hc
  omega

def budget (h : ℕ) := 130*h+80*laneBits h+400

theorem complete_trace (h : ℕ) (hh : 2 ≤ h) (pos : Port → ℤ) :
    ∃ t ≤ budget h, Trace t (cfg start (initial h) pos) (cfg .done (final h) pos) := by
  obtain ⟨a,ha,ta⟩ := prepare_trace h hh pos
  obtain ⟨b,hb,tb⟩ := halved_trace h pos
  obtain ⟨c,hc,tc⟩ := calculate_trace h (shifted pos)
  obtain ⟨d,hd,td⟩ := cleanup_trace h pos
  refine ⟨_,?_,trace_trans ta (trace_trans tb (trace_trans tc td))⟩
  unfold budget width at *
  omega

end BitWord.NativeCanonicalParameters
