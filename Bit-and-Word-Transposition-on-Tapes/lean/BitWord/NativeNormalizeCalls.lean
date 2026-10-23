import BitWord.NativeNormalize

namespace BitWord.NativeNormalize
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls
set_option autoImplicit false

private theorem values_changed {T : Type*} [DecidableEq T] (b : FinitePortBinding T Port)
    (s : Bank) (i : T) (x : Tape Bool) :
    b.values (Function.update (fun t => s (b.ports t)) i x) s=
      Function.update s (b.ports i) x := by
  rw [←b.values_update,b.values_project]

theorem resize_call (expand : Bool) (a e : ℕ) (ha : 0<a)
    (rows : List (List Bool × List Bool))
    (hlen : ∀ r∈rows,r.1.length=a ∧ r.2.length=e)
    (s : Bank) (pos : Port → ℤ)
    (hs : s (resizePorts expand 0)=Counter.marked (NativeResizeScan.inputRows expand rows))
    (hz : s (resizePorts expand 1)=⟨[],[]⟩)
    (ha' : s 3=NativeResizeScan.markedRuler a)
    (hb' : s 4=NativeResizeScan.markedRuler (a+e)) :
    ∃ t≤24*(rows.length*(a+e))+20, Trace expand t
      (cfg (.resize NativeResize.start) s pos)
      (cfg (.resize .done) (Function.update s (resizePorts expand 1)
        (Counter.marked (NativeResizeScan.outputRows expand rows))) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeResize.complete_trace expand a e ha rows hlen
    (fun p => pos ((resizeBinding expand).ports p))
  have h2 : resizePorts expand 2=(3:Port) := by cases expand <;> rfl
  have h3 : resizePorts expand 3=(4:Port) := by cases expand <;> rfl
  have hi : (![Counter.marked (NativeResizeScan.inputRows expand rows),⟨[],[]⟩,
      NativeResizeScan.markedRuler a,NativeResizeScan.markedRuler (a+e)] : Fin 4 → Tape Bool)=
      fun p => s ((resizeBinding expand).ports p) := by
    funext p; fin_cases p <;> simp [h2,h3,hs,hz,ha',hb']
  have hf : (![Counter.marked (NativeResizeScan.inputRows expand rows),
      Counter.marked (NativeResizeScan.outputRows expand rows),
      NativeResizeScan.markedRuler a,NativeResizeScan.markedRuler (a+e)] : Fin 4 → Tape Bool)=
      Function.update (fun p => s ((resizeBinding expand).ports p)) 1
        (Counter.marked (NativeResizeScan.outputRows expand rows)) := by
    funext p; fin_cases p <;> simp [h2,h3,hs,ha',hb']
  have he := NativeBindingCalls.restoring_call (resizeBinding expand) Label.resize
    (NativeResize.program expand) (program expand) (resize_code expand) _ _ s pos _ t
      (by simpa only [NativeResize.cfg,workCfg,hi,hf] using htr)
  rw [values_changed] at he
  exact ⟨t,ht,by simpa only [resizeBinding_ports] using he⟩

theorem square_call (expand : Bool) (a e : ℕ) (hb : 0<a+e)
    (rows : List (List Bool × List Bool)) (extras : List (List Bool))
    (hr : ∀ r∈rows,r.1.length=a ∧ r.2.length=e)
    (he : ∀ r∈extras,r.length=a+e) (s : Bank) (pos : Port → ℤ)
    (hs : s (squarePorts expand 0)=Counter.marked (NativeSquare.inputSquare expand rows extras))
    (hz : s (squarePorts expand 1)=⟨[],[]⟩)
    (ha' : s 7=NativeResizeScan.markedRuler a)
    (hb' : s 8=NativeResizeScan.markedRuler (a+e))
    (hn : s 5=NativeResizeScan.markedRuler rows.length)
    (hN : s 6=NativeResizeScan.markedRuler (rows.length+extras.length)) :
    ∃ t≤40*((rows.length+extras.length)*(a+e))+40, Trace expand t
      (cfg (.square NativeSquare.start) s pos)
      (cfg (.square .done) (Function.update s (squarePorts expand 1)
        (Counter.marked (NativeSquare.outputSquare expand rows extras))) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeSquare.complete_trace expand a e hb rows extras hr he
    (fun p => pos ((squareBinding expand).ports p))
  have hi : NativeSquare.bank (Counter.marked (NativeSquare.inputSquare expand rows extras)) ⟨[],[]⟩
      a (a+e) (NativeResizeScan.markedRuler rows.length)
        (NativeResizeScan.markedRuler (rows.length+extras.length))=
      fun p => s ((squareBinding expand).ports p) := by
    funext p; cases expand <;> fin_cases p <;> simp_all [NativeSquare.bank,squareBinding,squarePorts]
  have hf : NativeSquare.bank (Counter.marked (NativeSquare.inputSquare expand rows extras))
      (Counter.marked (NativeSquare.outputSquare expand rows extras)) a (a+e)
      (NativeResizeScan.markedRuler rows.length)
      (NativeResizeScan.markedRuler (rows.length+extras.length))=
      Function.update (fun p => s ((squareBinding expand).ports p)) 1
        (Counter.marked (NativeSquare.outputSquare expand rows extras)) := by
    funext p; cases expand <;> fin_cases p <;> simp_all [NativeSquare.bank,squareBinding,squarePorts]
  have hx := NativeBindingCalls.restoring_call (squareBinding expand) Label.square
    (NativeSquare.program expand) (program expand) (square_code expand) _ _ s pos _ t
      (by simpa only [NativeSquare.cfg,workCfg,hi,hf] using htr)
  rw [values_changed] at hx
  exact ⟨t,ht,by simpa only [squareBinding_ports] using hx⟩

theorem copy_call (expand : Bool) (xs : List Bool) (s : Bank) (pos : Port → ℤ)
    (hs : s 2=Counter.marked xs) (hz : s 0=⟨[],[]⟩) :
    ∃ t≤6*xs.length+14,Trace expand t (cfg (.copy (.init (.erase 0))) s pos)
      (cfg (.copy (.seal .done)) (Function.update s 0 (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun p => pos (copyBinding.ports p))
  have hi : NativeMappedCopy.bank (Counter.marked xs) ⟨[],[]⟩=
      fun p => s (copyBinding.ports p) := by
    funext p; fin_cases p <;> simp [NativeMappedCopy.bank,hs,hz]
  have hf : NativeMappedCopy.bank (Counter.marked xs) (Counter.marked (xs.map id))=
      Function.update (fun p => s (copyBinding.ports p)) 1 (Counter.marked xs) := by
    funext p; fin_cases p <;> simp [NativeMappedCopy.bank,hs]
  have he := NativeBindingCalls.restoring_call copyBinding Label.copy (NativeMappedCopy.program id)
    (program expand) (copy_code expand) _ _ s pos _ t
      (by simpa only [NativeMappedCopy.cfg,workCfg,hi,hf] using htr)
  exact ⟨t,ht,by simpa only [values_changed,show copyBinding.ports 1=(0:Port) from rfl] using he⟩

end BitWord.NativeNormalize
