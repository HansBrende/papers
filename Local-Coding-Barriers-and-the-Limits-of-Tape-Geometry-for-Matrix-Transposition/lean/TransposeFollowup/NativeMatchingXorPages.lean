import TransposeFollowup.NativeMatchingXorPageReset

/-! A fixed-page-count native caller. Each increasing matching page is
followed by a paid reset before the next page starts. All prepared tag tapes
and source data survive, and target contexts are retained. -/
namespace TransposeFollowup.NativeMatchingXorPages
open FixedTapeCompiler CopyMachine MatchingXorStream
set_option autoImplicit false

inductive Port (q : ℕ) | source | target | tagA (i : Fin q) | tagB (i : Fin q)
  deriving DecidableEq, Fintype

def binding {q : ℕ} (i : Fin q) : FinitePortBinding (Fin 4) (Port q) where
  ports := ⟨![.source,.target,.tagA i,.tagB i],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
  decode := fun p => match p with
    | .source => some 0 | .target => some 1
    | .tagA j => if j=i then some 2 else none
    | .tagB j => if j=i then some 3 else none
  decode_spec := by
    intro p t
    change _ ↔ (![Port.source,Port.target,Port.tagA i,Port.tagB i] : Fin 4 → Port q) t=p
    cases p <;> fin_cases t <;> simp [eq_comm]

inductive Label (q : ℕ)
  | next (i : Fin (q+1)) | call (i : Fin q) (pc : NativeMatchingXorPageReset.Label)
  deriving DecidableEq, Fintype

def start (q : ℕ) : Label q := .next 0

def program (q : ℕ) : Microcode.Program (Port q) (Label q)
  | .next i => if h : i.val<q then .jump (.call ⟨i.val,h⟩ (.page .findA)) else .halt
  | .call i pc => if pc=.reset .done then .jump (.next i.succ)
      else (binding i).instruction (Label.call i) (NativeMatchingXorPageReset.program pc)

def bank {q : ℕ} (source target : Tape Bool) (a b : Fin q → List Bool) : Port q → Tape Bool
  | .source => source | .target => target
  | .tagA i => Counter.marked (a i) | .tagB i => Counter.marked (b i)

def cfg {q : ℕ} (pc : Label q) (source target : Tape Bool) (a b : Fin q → List Bool)
    (pos : Port q → ℤ) : NativeMicrocode.Config (Port q) (Label q) :=
  ⟨⟨pc,fun p => (bank source target a b p).denote⟩,pos⟩

def frame {q : ℕ} (source target : Tape Bool) (a b : Fin q → List Bool)
    (pos : Port q → ℤ) : MicrocodeEmbedding.Frame (Port q) :=
  ⟨fun p => (bank source target a b p).denote,pos⟩

def page (A B a b : List Bool) : List Bool := MatchingXorStream.apply (selected (a.zip A)) (b.zip B)

def output {q : ℕ} (A B : List Bool) (a b : Fin q → List Bool) : ℕ → List Bool
  | 0 => B
  | n+1 => if h : n<q then page A (output A B a b n) (a ⟨n,h⟩) (b ⟨n,h⟩)
      else output A B a b n

def ValidTags {q : ℕ} (N : ℕ) (a b : Fin q → List Bool) : Prop :=
  ∀ i, (a i).length=N ∧ (b i).length=N ∧ (a i).count true=(b i).count true

theorem values_zip (ts xs : List Bool) (h : ts.length=xs.length) : values (ts.zip xs)=xs := by
  simp [values,List.map_snd_zip,h]

theorem tags_zip (ts xs : List Bool) (h : ts.length=xs.length) : tags (ts.zip xs)=ts := by
  simp [tags,List.map_fst_zip,← h]

theorem selected_length_tags (xs : List Record) : (selected xs).length=(tags xs).count true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨tag,value⟩
    cases tag <;> simpa [selected,tags] using ih

theorem selected_zip_length (ts xs : List Bool) (h : ts.length=xs.length) :
    (selected (ts.zip xs)).length=ts.count true := by
  rw [selected_length_tags,tags_zip ts xs h]

theorem output_length {q : ℕ} (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b) (n : ℕ) :
    (output A B a b n).length=A.length := by
  induction n with
  | zero => exact hB
  | succ n ih =>
    simp only [output]
    split_ifs with h
    · simp [page,ih,(hvalid ⟨n,h⟩).2.1]
    · exact ih

theorem call_code {q : ℕ} (i : Fin q) (pc : NativeMatchingXorPageReset.Label)
    (hh : NativeMatchingXorPageReset.program pc≠.halt)
    (_ : NativeMatchingXorPageReset.program pc≠.reject) :
    program q (.call i pc)=MicrocodeEmbedding.instruction (binding i).ports (Label.call i)
      (NativeMatchingXorPageReset.program pc) := by
  have h : pc≠.reset .done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem embed_call {q : ℕ} (i : Fin q) (pc : NativeMatchingXorPageReset.Label)
    (source target baseTarget : Tape Bool) (a b : Fin q → List Bool) (pos : Port q → ℤ) :
    MicrocodeEmbedding.embed (binding i).ports (Label.call i)
      (NativeMatchingXorPageReset.cfg pc source target (Counter.marked (a i)) (Counter.marked (b i))
        (fun t => pos ((binding i).ports t))).denote
      (frame source baseTarget a b pos)=cfg (.call i pc) source target a b pos := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorPageReset.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← (binding i).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;>
    simp [FinitePortBinding.values,binding,bank] <;>
    first | rfl | (split_ifs <;> subst_vars <;> rfl)

abbrev Trace (q : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program q)) (NativeMicrocode.Active (program q))

theorem page_call {q : ℕ} (i : Fin q) (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b)
    (al ar bl br : List (Sym Bool)) (pos : Port q → ℤ) :
    ∃ t ≤ 8*A.length+6, Trace q t
      (cfg (.call i (.page .findA)) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos)
      (cfg (.call i (.reset .done)) ⟨al,symbols A++ar⟩
        ⟨bl,symbols (page A B (a i) (b i))++br⟩ a b pos) := by
  have ha := (hvalid i).1
  have hb := (hvalid i).2.1.trans hB.symm
  have hl : ((b i).zip B).length=((a i).zip A).length := by simp [List.length_zip,ha,hb,hB]
  have hc : (selected ((a i).zip A)).length=(selected ((b i).zip B)).length := by
    rw [selected_zip_length _ _ ha,selected_zip_length _ _ hb]
    exact (hvalid i).2.2
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorPageReset.page_reset_trace
    ((a i).zip A) ((b i).zip B) hl hc al ar bl br (fun t => pos ((binding i).ports t))
  have he := MicrocodeEmbedding.trace_embed (binding i).ports (Label.call i)
    NativeMatchingXorPageReset.program (program q) (frame ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos)
    (call_code i) htr
  rw [values_zip _ _ ha,values_zip _ _ hb,tags_zip _ _ ha,tags_zip _ _ hb] at he
  refine ⟨t,by simpa [List.length_zip,ha] using ht,?_⟩
  simpa only [embed_call,page] using he

theorem page_stage {q : ℕ} (i : Fin q) (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b)
    (al ar bl br : List (Sym Bool)) (pos : Port q → ℤ) :
    ∃ t ≤ 8*A.length+8, Trace q t
      (cfg (.next i.castSucc) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos)
      (cfg (.next i.succ) ⟨al,symbols A++ar⟩
        ⟨bl,symbols (page A B (a i) (b i))++br⟩ a b pos) := by
  have j1 : Trace q 1
      (cfg (.next i.castSucc) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos)
      (cfg (.call i (.page .findA)) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos) := by
    apply NativeMicrocode.jump_trace
    simp [program,cfg,i.isLt]
  obtain ⟨t,ht,htr⟩ := page_call i A B a b hB hvalid al ar bl br pos
  have j2 : Trace q 1
      (cfg (.call i (.reset .done)) ⟨al,symbols A++ar⟩
        ⟨bl,symbols (page A B (a i) (b i))++br⟩ a b pos)
      (cfg (.next i.succ) ⟨al,symbols A++ar⟩
        ⟨bl,symbols (page A B (a i) (b i))++br⟩ a b pos) :=
    NativeMicrocode.jump_trace _ _ _ (by simp [program,cfg])
  exact ⟨1+t+1,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans j1 htr) j2⟩

theorem partial_trace {q : ℕ} (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b)
    (al ar bl br : List (Sym Bool)) (pos : Port q → ℤ) (n : ℕ) (hn : n≤q) :
    ∃ t ≤ n*(8*A.length+8), Trace q t
      (cfg (start q) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos)
      (cfg (.next ⟨n,by omega⟩) ⟨al,symbols A++ar⟩
        ⟨bl,symbols (output A B a b n)++br⟩ a b pos) := by
  induction n with
  | zero => exact ⟨0,by simp,.refl _⟩
  | succ n ih =>
    have hn' : n<q := by omega
    obtain ⟨t,ht,htr⟩ := ih (by omega)
    obtain ⟨u,hu,hur⟩ := page_stage ⟨n,hn'⟩ A (output A B a b n) a b
      (output_length A B a b hB hvalid n) hvalid al ar bl br pos
    refine ⟨t+u,by nlinarith,?_⟩
    have he : (⟨n,hn'⟩ : Fin q).succ = (⟨n+1,by omega⟩ : Fin (q+1)) := rfl
    simpa only [output,dite_eq_left hn',he] using NativeCountedLoop.trace_trans htr hur

theorem complete_trace {q : ℕ} (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b)
    (al ar bl br : List (Sym Bool)) (pos : Port q → ℤ) :
    ∃ t ≤ q*(8*A.length+8), Trace q t
      (cfg (start q) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos)
      (cfg (.next (Fin.last q)) ⟨al,symbols A++ar⟩
        ⟨bl,symbols (output A B a b q)++br⟩ a b pos) :=
  partial_trace A B a b hB hvalid al ar bl br pos q (le_refl q)

noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) (start q)
noncomputable def nativeMachine (q : ℕ) := NativeMicrocode.machine (nativeEncoding q) (program q)

theorem fixed_tapes (q : ℕ) : (nativeMachine q).k=2+2*q ∧ (nativeMachine q).g+1=5 := by
  refine ⟨?_,rfl⟩
  change Fintype.card (Port q)=2+2*q
  let e : Port q ≃ (Bool ⊕ (Bool × Fin q)) :=
    { toFun := fun p => match p with
        | .source => .inl false | .target => .inl true
        | .tagA i => .inr (false,i) | .tagB i => .inr (true,i)
      invFun := fun p => match p with
        | .inl false => .source | .inl true => .target
        | .inr (false,i) => .tagA i | .inr (true,i) => .tagB i
      left_inv := by intro p; cases p <;> rfl
      right_inv := by rintro (b | ⟨b,i⟩) <;> cases b <;> rfl }
  rw [Fintype.card_congr e]
  simp

theorem fixed_states (q : ℕ) : (nativeMachine q).q+1=24*q+1 ∧
    (nativeEncoding q).label (start q)=0 := by
  refine ⟨?_,NativeMicrocode.initialEncoding_start _⟩
  let e : Label q ≃ (Fin (q+1) ⊕ (Fin q × NativeMatchingXorPageReset.Label)) :=
    { toFun := fun pc => match pc with | .next i => .inl i | .call i pc => .inr (i,pc)
      invFun := fun pc => match pc with | .inl i => .next i | .inr (i,pc) => .call i pc
      left_inv := by intro pc; cases pc <;> rfl
      right_inv := by rintro (i | ⟨i,pc⟩) <;> rfl }
  have hc : Fintype.card NativeMatchingXorPageReset.Label=23 := by decide +kernel
  have hq : Fintype.card (Label q)=24*q+1 := by
    rw [Fintype.card_congr e]
    simp [hc]
    omega
  change Fintype.card (Label q)-1+1=24*q+1
  rw [hq]
  omega

theorem native_pages {q : ℕ} (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b)
    (al ar bl br : List (Sym Bool)) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ q*(8*A.length+8),
      Transpose.stepN (nativeMachine q) input t
        ((cfg (start q) ⟨al,symbols A++ar⟩ ⟨bl,symbols B++br⟩ a b pos).denote
          (nativeEncoding q) (program q) ip outRev)=
        some ((cfg (.next (Fin.last q)) ⟨al,symbols A++ar⟩
          ⟨bl,symbols (output A B a b q)++br⟩ a b pos).denote
          (nativeEncoding q) (program q) ip outRev) ∧
      Transpose.step (nativeMachine q) input
        ((cfg (.next (Fin.last q)) ⟨al,symbols A++ar⟩
          ⟨bl,symbols (output A B a b q)++br⟩ a b pos).denote
          (nativeEncoding q) (program q) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace A B a b hB hvalid al ar bl br pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding q) (program q) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding q) (program q) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

end TransposeFollowup.NativeMatchingXorPages
