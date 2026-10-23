import TransposeFollowup.NativeMatchingXorReset
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop

/-! One matching-page computation followed by its physical four-head reset.
Source and target contexts survive, including an untouched payload prefix. -/
namespace TransposeFollowup.NativeMatchingXorPageReset
open FixedTapeCompiler CopyMachine MatchingXorStream
set_option autoImplicit false

def binding : FinitePortBinding (Fin 4) (Fin 4) where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

inductive Label | page (pc : NativeMatchingXorPage.Label) | reset (pc : NativeMatchingXorReset.Label)
  deriving DecidableEq, Fintype

def program : Microcode.Program (Fin 4) Label
  | .page .done => .jump (.reset .left)
  | .page pc => binding.instruction Label.page (NativeMatchingXorPage.program pc)
  | .reset pc => binding.instruction Label.reset (NativeMatchingXorReset.program pc)

def cfg (pc : Label) (a b af bf : Tape Bool) (pos : Fin 4 → ℤ) : NativeZipper.Config (Fin 4) Label :=
  ⟨⟨pc,![a,b,af,bf]⟩,pos⟩

def frame (pos : Fin 4 → ℤ) : MicrocodeEmbedding.Frame (Fin 4) :=
  ⟨fun _ => (⟨[],[]⟩ : Tape Bool).denote,pos⟩

theorem page_code (pc : NativeMatchingXorPage.Label)
    (hh : NativeMatchingXorPage.program pc≠.halt) (_ : NativeMatchingXorPage.program pc≠.reject) :
    program (.page pc)=MicrocodeEmbedding.instruction binding.ports Label.page (NativeMatchingXorPage.program pc) := by
  cases pc <;> simp_all [program,NativeMatchingXorPage.program,FinitePortBinding.instruction_eq]

theorem reset_code (pc : NativeMatchingXorReset.Label) :
    program (.reset pc)=MicrocodeEmbedding.instruction binding.ports Label.reset (NativeMatchingXorReset.program pc) :=
  binding.instruction_eq _ _

theorem embed_page (pc : NativeMatchingXorPage.Label) (a b af bf : Tape Bool) (pos origin : Fin 4 → ℤ) :
    MicrocodeEmbedding.embed binding.ports Label.page
      (NativeMatchingXorPage.cfg pc a b af bf pos).denote (frame origin)=
      (cfg (.page pc) a b af bf pos).denote := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorPage.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← binding.values_eq_extend]
  congr 2

theorem embed_reset (pc : NativeMatchingXorReset.Label) (a b af bf : Tape Bool) (pos origin : Fin 4 → ℤ) :
    MicrocodeEmbedding.embed binding.ports Label.reset
      (NativeMatchingXorReset.cfg pc a b af bf pos).denote (frame origin)=
      (cfg (.reset pc) a b af bf pos).denote := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorReset.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg frame
  simp only [← binding.values_eq_extend]
  congr 2

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem page_reset_trace (xs ys : List Record) (hlen : ys.length=xs.length)
    (hcount : (selected xs).length=(selected ys).length)
    (al ar bl br : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 8*xs.length+6, Trace t
      (cfg (.page .findA) ⟨al,symbols (values xs)++ar⟩ ⟨bl,symbols (values ys)++br⟩
        (Counter.marked (tags xs)) (Counter.marked (tags ys)) pos).denote
      (cfg (.reset .done) ⟨al,symbols (values xs)++ar⟩
        ⟨bl,symbols (MatchingXorStream.apply (selected xs) ys)++br⟩
        (Counter.marked (tags xs)) (Counter.marked (tags ys)) pos).denote := by
  obtain ⟨a,ha,ta⟩ := NativeZipper.trace_of_run NativeMatchingXorPage.program
    (NativeMatchingXorPage.scan_run xs ys hcount al ar bl br [.start] [] [.start] [] pos)
  have ea := MicrocodeEmbedding.trace_embed binding.ports Label.page
    NativeMatchingXorPage.program program (frame pos) page_code ta
  simp only [NativeMatchingXorPage.loaded,NativeMatchingXorPage.finished,embed_page,
    NativeMatchingXorPage.symbols,CopyMachine.symbols] at ea
  let out := MatchingXorStream.apply (selected xs) ys
  let endPos := NativeMatchingXorPage.advance pos xs.length ys.length
  have tj : Trace 1
      (cfg (.page .done) ⟨(symbols (values xs)).reverse++al,ar⟩
        ⟨(symbols out).reverse++bl,br⟩
        ⟨(symbols (tags xs)).reverse++[.start],[.stop]⟩
        ⟨(symbols (tags ys)).reverse++[.start],[.stop]⟩ endPos).denote
      (cfg (.reset .left) ⟨(symbols (values xs)).reverse++al,ar⟩
        ⟨(symbols out).reverse++bl,br⟩
        ⟨(symbols (tags xs)).reverse++[.start],[.stop]⟩
        ⟨(symbols (tags ys)).reverse++[.start],[.stop]⟩ endPos).denote :=
    NativeMicrocode.jump_trace _ _ _ rfl
  obtain ⟨b,hb,tb⟩ := NativeMatchingXorReset.reset_trace
    (values xs).reverse out.reverse (tags xs).reverse (tags ys).reverse
    (by simp [out,values,hlen]) (by simp [values,tags]) (by simp [values,tags,hlen])
    al ar bl br [] [.stop] [.start] [.stop] endPos
  have eb := MicrocodeEmbedding.trace_embed binding.ports Label.reset
    NativeMatchingXorReset.program program (frame pos) (fun pc _ _ => reset_code pc) tb
  have hp : (fun p => endPos p-(values xs).reverse.length)=pos := by
    funext p
    fin_cases p <;> simp [endPos,NativeMatchingXorPage.advance,values,hlen]
  simp only [embed_reset,hp,symbols,List.map_reverse,List.reverse_reverse] at eb
  refine ⟨a+1+b,?_,?_⟩
  · have hc := selected_length_le xs
    simp only [NativeMatchingXorPage.ticks,hlen] at ha
    simp only [List.length_reverse,values,List.length_map] at hb
    omega
  · simpa only [Counter.marked,symbols,Nat.add_assoc] using NativeCountedLoop.trace_trans ea
      (NativeCountedLoop.trace_trans tj eb)

end TransposeFollowup.NativeMatchingXorPageReset
