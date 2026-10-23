import BitWord.NativeCanonicalGenerator

namespace BitWord.NativeCanonicalGenerator
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
set_option autoImplicit false

theorem classifier_call (h : ℕ) (pos : Port → ℤ) :
    ∃ t ≤ 98, Trace t (cfg start (initial h) pos)
      (cfg (.classifier (.done (NativeSmallClassifier.answer (hword h)))) (initial h) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeSmallClassifier.complete_trace (hword h)
    (fun p => pos (classifierBinding.ports p))
  have hp : (fun p => initial h (classifierBinding.ports p)) =
      fun _ => Counter.marked (hword h) := by
    funext p; fin_cases p; rfl
  have hs : OperationalTrace.Trace (NativeMicrocode.step NativeSmallClassifier.program)
      (NativeMicrocode.Active NativeSmallClassifier.program) t
      (workCfg (.scan 0) (fun p => initial h (classifierBinding.ports p))
        (fun p => pos (classifierBinding.ports p)))
      (workCfg (.done (NativeSmallClassifier.answer (hword h)))
        (fun p => initial h (classifierBinding.ports p)) (fun p => pos (classifierBinding.ports p))) := by
    rw [hp]
    simpa only [NativeSmallClassifier.cfg,NativeZipper.Config.denote,Microcode.Config.denote,workCfg] using htr
  have he := NativeBindingCalls.restoring_call classifierBinding Label.classifier
    NativeSmallClassifier.program program classifier_code (.scan 0)
    (.done (NativeSmallClassifier.answer (hword h))) (initial h) pos _ t hs
  exact ⟨t,ht,by simpa only [start,classifierBinding.values_project] using he⟩

theorem branch_small (h : Fin 32) :
    branch (NativeSmallClassifier.answer (hword h))=.small (.start h) := by
  simp [branch,NativeSmallClassifier.answer,h.isLt]

theorem branch_large (h : ℕ) (hh : 32 ≤ h) :
    branch (NativeSmallClassifier.answer (hword h))=.large NativeLargeDescriptors.start := by
  simp [branch,NativeSmallClassifier.answer,Nat.min_eq_right hh]

theorem small_call (h : Fin 32) (pos : Port → ℤ) :
    ∃ t ≤ 133, Trace t (cfg (.small (.start h)) (initial h) pos)
      (cfg (.small (.done h)) (smallFinal h) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeSmallDescriptors.complete_trace h (fun p => pos (smallBinding.ports p))
  have hp : (fun p => initial h (smallBinding.ports p))=NativeSmallDescriptors.initial := by
    funext p; cases p <;> rfl
  have hs : OperationalTrace.Trace (NativeMicrocode.step NativeSmallDescriptors.program)
      (NativeMicrocode.Active NativeSmallDescriptors.program) t
      (workCfg (.start h) (fun p => initial h (smallBinding.ports p)) (fun p => pos (smallBinding.ports p)))
      (workCfg (.done h) (NativeSmallDescriptors.final h) (fun p => pos (smallBinding.ports p))) := by
    rw [hp]
    simpa only [NativeSmallDescriptors.Trace,NativeLiteralBank.Trace,NativeSmallDescriptors.program,NativeSmallDescriptors.cfg,NativeLiteralBank.cfg,NativeZipper.Config.denote,
      Microcode.Config.denote,workCfg] using htr
  have he := NativeBindingCalls.restoring_call smallBinding Label.small NativeSmallDescriptors.program
    program small_code (.start h) (.done h) (initial h) pos _ t hs
  exact ⟨t,by simpa only [NativeSmallDescriptors.bound] using ht,he⟩

end BitWord.NativeCanonicalGenerator
