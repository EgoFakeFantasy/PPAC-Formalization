import PPAC.Migration.Internal.AbstractFrameArguments

/-! 任意内部深度frame下原项／参数列运行与实际程序／编码操作的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectAbstractFramePrograms
open Source SourceAlgebra SourceLogic OmegaSyntax

def arbitraryDepthFrameVariableProgramIffSentence {m} (bound : Bool) (w mode depth P a b c e R S n q i : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).imp ((SyntaxVariableSyntax.code bound w i n).imp (((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q))))))).close

theorem source_arbitraryDepthFrameVariableProgramIff {m} (bound : Bool) (w mode depth P a b c e R S n q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameVariableProgramIffSentence bound w mode depth P a b c e R S n q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (Formula.mem i (SyntaxTermSyntax.limit bound a b)) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i (SyntaxTermSyntax.limit bound a b)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact AbstractFrameTerm.at_variable hZ bound w mode depth P a b c e R S n q i h0 h1 h2 h3

theorem arbitraryDepthFrameVariableProgramIff_kernel_certificate {m} (bound : Bool) (w mode depth P a b c e R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameVariableProgramIffSentence bound w mode depth P a b c e R S n q i)) := TheoryTransport.sentence (source_arbitraryDepthFrameVariableProgramIff bound w mode depth P a b c e R S n q i)

theorem native_arbitraryDepthFrameVariableProgramIff {m} (bound : Bool) (w mode depth P a b c e R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameVariableProgramIffSentence bound w mode depth P a b c e R S n q i)) := ZFReplay.replay (arbitraryDepthFrameVariableProgramIff_kernel_certificate bound w mode depth P a b c e R S n q i)

def arbitraryDepthFrameTermProgramIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)))))).close

theorem source_arbitraryDepthFrameTermProgramIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameTermProgramIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameTerm.program_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem arbitraryDepthFrameTermProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameTermProgramIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_arbitraryDepthFrameTermProgramIff w mode depth P a b c e R S n q)

theorem native_arbitraryDepthFrameTermProgramIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameTermProgramIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (arbitraryDepthFrameTermProgramIff_kernel_certificate w mode depth P a b c e R S n q)

def arbitraryDepthFrameTermCodedIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q)))))).close

theorem source_arbitraryDepthFrameTermCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameTermCodedIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameTerm.coded_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem arbitraryDepthFrameTermCodedIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameTermCodedIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_arbitraryDepthFrameTermCodedIff w mode depth P a b c e R S n q)

theorem native_arbitraryDepthFrameTermCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameTermCodedIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (arbitraryDepthFrameTermCodedIff_kernel_certificate w mode depth P a b c e R S n q)

def arbitraryDepthFrameTermGuardedCodedIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((((SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q))))).close

theorem source_arbitraryDepthFrameTermGuardedCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameTermGuardedCodedIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact AbstractFrameTerm.guarded_coded_iff hZ w mode depth P a b c e R S n q h0 h1

theorem arbitraryDepthFrameTermGuardedCodedIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameTermGuardedCodedIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_arbitraryDepthFrameTermGuardedCodedIff w mode depth P a b c e R S n q)

theorem native_arbitraryDepthFrameTermGuardedCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameTermGuardedCodedIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (arbitraryDepthFrameTermGuardedCodedIff_kernel_certificate w mode depth P a b c e R S n q)

def arbitraryDepthFrameTermAllOutputsAgreementSentence {m} (w mode depth P a b c e R S n : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.agreement w mode depth P R S n))))).close

theorem source_arbitraryDepthFrameTermAllOutputsAgreement {m} (w mode depth P a b c e R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameTermAllOutputsAgreementSentence w mode depth P a b c e R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameTermFiber.agreement hZ w mode depth P a b c e R S n h0 h1 h2

theorem arbitraryDepthFrameTermAllOutputsAgreement_kernel_certificate {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameTermAllOutputsAgreementSentence w mode depth P a b c e R S n)) := TheoryTransport.sentence (source_arbitraryDepthFrameTermAllOutputsAgreement w mode depth P a b c e R S n)

theorem native_arbitraryDepthFrameTermAllOutputsAgreement {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameTermAllOutputsAgreementSentence w mode depth P a b c e R S n)) := ZFReplay.replay (arbitraryDepthFrameTermAllOutputsAgreement_kernel_certificate w mode depth P a b c e R S n)

def arbitraryDepthFrameTypedTermUniqueFiberSentence {m} (w mode depth P a b c e R S n : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.fiber w mode depth P c e n))))).close

theorem source_arbitraryDepthFrameTypedTermUniqueFiber {m} (w mode depth P a b c e R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameTypedTermUniqueFiberSentence w mode depth P a b c e R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameTermFiber.fiber hZ w mode depth P a b c e R S n h0 h1 h2

theorem arbitraryDepthFrameTypedTermUniqueFiber_kernel_certificate {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameTypedTermUniqueFiberSentence w mode depth P a b c e R S n)) := TheoryTransport.sentence (source_arbitraryDepthFrameTypedTermUniqueFiber w mode depth P a b c e R S n)

theorem native_arbitraryDepthFrameTypedTermUniqueFiber {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameTypedTermUniqueFiberSentence w mode depth P a b c e R S n)) := ZFReplay.replay (arbitraryDepthFrameTypedTermUniqueFiber_kernel_certificate w mode depth P a b c e R S n)

def arbitraryDepthFrameTermPromiseDischargedSentence {m} (w mode depth P a b c e R S : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((OriginalNumericTermValueSyntax.promise w mode depth P a b c e)))).close

theorem source_arbitraryDepthFrameTermPromiseDischarged {m} (w mode depth P a b c e R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameTermPromiseDischargedSentence w mode depth P a b c e R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact AbstractFrameTermFiber.promise hZ w mode depth P a b c e R S h0 h1

theorem arbitraryDepthFrameTermPromiseDischarged_kernel_certificate {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameTermPromiseDischargedSentence w mode depth P a b c e R S)) := TheoryTransport.sentence (source_arbitraryDepthFrameTermPromiseDischarged w mode depth P a b c e R S)

theorem native_arbitraryDepthFrameTermPromiseDischarged {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameTermPromiseDischargedSentence w mode depth P a b c e R S)) := ZFReplay.replay (arbitraryDepthFrameTermPromiseDischarged_kernel_certificate w mode depth P a b c e R S)

def arbitraryDepthFrameArgumentFieldsIffSentence {m} (w mode depth P a b c e R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalArgumentFieldSyntax.fields w mode depth P k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q)))))).close

theorem source_arbitraryDepthFrameArgumentFieldsIff {m} (w mode depth P a b c e R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameArgumentFieldsIffSentence w mode depth P a b c e R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameArguments.fields_iff hZ w mode depth P a b c e R S n q k h0 h1 h2

theorem arbitraryDepthFrameArgumentFieldsIff_kernel_certificate {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameArgumentFieldsIffSentence w mode depth P a b c e R S n q k)) := TheoryTransport.sentence (source_arbitraryDepthFrameArgumentFieldsIff w mode depth P a b c e R S n q k)

theorem native_arbitraryDepthFrameArgumentFieldsIff {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameArgumentFieldsIffSentence w mode depth P a b c e R S n q k)) := ZFReplay.replay (arbitraryDepthFrameArgumentFieldsIff_kernel_certificate w mode depth P a b c e R S n q k)

def arbitraryDepthFrameArgumentProgramIffSentence {m} (w mode depth P a b c e R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalTransformRowSyntax.run 2 w mode depth P n q).iff (ArgumentProgramFieldSyntax.mapped w R S k c e n q)))))).close

theorem source_arbitraryDepthFrameArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameArgumentProgramIffSentence w mode depth P a b c e R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameArguments.run_iff hZ w mode depth P a b c e R S n q k h0 h1 h2

theorem arbitraryDepthFrameArgumentProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := TheoryTransport.sentence (source_arbitraryDepthFrameArgumentProgramIff w mode depth P a b c e R S n q k)

theorem native_arbitraryDepthFrameArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := ZFReplay.replay (arbitraryDepthFrameArgumentProgramIff_kernel_certificate w mode depth P a b c e R S n q k)

def arbitraryDepthFrameGuardedArgumentProgramIffSentence {m} (w mode depth P a b c e R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((((SyntaxMixedImageCodeSyntax.termList w k a b n).conj (OriginalTransformRowSyntax.run 2 w mode depth P n q)).iff ((SyntaxMixedImageCodeSyntax.termList w k a b n).conj (ArgumentProgramFieldSyntax.mapped w R S k c e n q)))))).close

theorem source_arbitraryDepthFrameGuardedArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryDepthFrameGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact AbstractFrameArguments.guarded_iff hZ w mode depth P a b c e R S n q k h0 h1

theorem arbitraryDepthFrameGuardedArgumentProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryDepthFrameGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := TheoryTransport.sentence (source_arbitraryDepthFrameGuardedArgumentProgramIff w mode depth P a b c e R S n q k)

theorem native_arbitraryDepthFrameGuardedArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryDepthFrameGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := ZFReplay.replay (arbitraryDepthFrameGuardedArgumentProgramIff_kernel_certificate w mode depth P a b c e R S n q k)

end PPAC.Migration.Internal.ObjectAbstractFramePrograms
