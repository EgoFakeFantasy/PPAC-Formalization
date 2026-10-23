import PPAC.Migration.Internal.IndexFormulaRenameBridge

/-! 全部内部索引环境及任意公式码双向传输的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectIndexFormulaRename
open Source SourceAlgebra SourceLogic OmegaSyntax

def convertedExistsSentence {m} (isBound : Bool) (w I a c d : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.input isBound w I a c d).imp ((IndexTermImageCodeSyntax.existsCode isBound w I a c d)))).close

theorem source_convertedExists {m} (isBound : Bool) (w I a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (convertedExistsSentence isBound w I a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.input isBound w I a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.input isBound w I a c d) := .hyp (Or.inl rfl)
  exact IndexTermImageCodeExistence.exists_code hZ isBound w I a c d h0 h1

theorem convertedExists_kernel_certificate {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (convertedExistsSentence isBound w I a c d)) := TheoryTransport.sentence (source_convertedExists isBound w I a c d)

theorem native_convertedExists {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (convertedExistsSentence isBound w I a c d)) := ZFReplay.replay (convertedExists_kernel_certificate isBound w I a c d)

def convertedFiberSentence {m} (isBound : Bool) (w I a c d : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.input isBound w I a c d).imp ((IndexTermImageCodeSyntax.fiber isBound w I a c d)))).close

theorem source_convertedFiber {m} (isBound : Bool) (w I a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (convertedFiberSentence isBound w I a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.input isBound w I a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.input isBound w I a c d) := .hyp (Or.inl rfl)
  exact IndexTermImageCodeUnique.actual_fiber hZ isBound w I a c d h0 h1

theorem convertedFiber_kernel_certificate {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (convertedFiberSentence isBound w I a c d)) := TheoryTransport.sentence (source_convertedFiber isBound w I a c d)

theorem native_convertedFiber {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (convertedFiberSentence isBound w I a c d)) := ZFReplay.replay (convertedFiber_kernel_certificate isBound w I a c d)

def convertedDomainIffSentence {m} (isBound : Bool) (w I a c d : Fin m) : Source.Sentence := ((omega w).imp (((IndexTermImageCodeSyntax.existsCode isBound w I a c d).iff (IndexTermImageCodeSyntax.input isBound w I a c d)))).close

theorem source_convertedDomainIff {m} (isBound : Bool) (w I a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (convertedDomainIffSentence isBound w I a c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact IndexTermImageCodeUnique.exists_iff_input hZ isBound w I a c d h0

theorem convertedDomainIff_kernel_certificate {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (convertedDomainIffSentence isBound w I a c d)) := TheoryTransport.sentence (source_convertedDomainIff isBound w I a c d)

theorem native_convertedDomainIff {m} (isBound : Bool) (w I a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (convertedDomainIffSentence isBound w I a c d)) := ZFReplay.replay (convertedDomainIff_kernel_certificate isBound w I a c d)

def convertedUniqueSentence {m} (isBound : Bool) (w I T U a c d : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.converted isBound w I T a c d).imp ((IndexTermImageCodeSyntax.converted isBound w I U a c d).imp ((.equal T U))))).close

theorem source_convertedUnique {m} (isBound : Bool) (w I T U a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (convertedUniqueSentence isBound w I T U a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted isBound w I U a c d) (Context.add (IndexTermImageCodeSyntax.converted isBound w I T a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.converted isBound w I T a c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (IndexTermImageCodeSyntax.converted isBound w I U a c d) := .hyp (Or.inl rfl)
  exact IndexTermImageCodeUnique.unique hZ isBound w I T U a c d h0 h1 h2

theorem convertedUnique_kernel_certificate {m} (isBound : Bool) (w I T U a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (convertedUniqueSentence isBound w I T U a c d)) := TheoryTransport.sentence (source_convertedUnique isBound w I T U a c d)

theorem native_convertedUnique {m} (isBound : Bool) (w I T U a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (convertedUniqueSentence isBound w I T U a c d)) := ZFReplay.replay (convertedUnique_kernel_certificate isBound w I T U a c d)

def environmentExistsSentence {m} (w I J a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c I).imp ((SyntaxMapCodeSyntax.mapCode w b d J).imp ((IndexTermImageCodeSyntax.existsEnvironment w I J a b c d))))).close

theorem source_environmentExists {m} (w I J a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentExistsSentence w I J a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.mapCode w b d J) (Context.add (SyntaxMapCodeSyntax.mapCode w a c I) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c I) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d J) := .hyp (Or.inl rfl)
  exact IndexTermImageEnvironment.exists_environment hZ w I J a b c d h0 h1 h2

theorem environmentExists_kernel_certificate {m} (w I J a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentExistsSentence w I J a b c d)) := TheoryTransport.sentence (source_environmentExists w I J a b c d)

theorem native_environmentExists {m} (w I J a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentExistsSentence w I J a b c d)) := ZFReplay.replay (environmentExists_kernel_certificate w I J a b c d)

def environmentUniqueSentence {m} (w I J R S U V a b c d : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((IndexTermImageCodeSyntax.environment w I J U V a b c d).imp (((Formula.equal R U).conj (.equal S V)))))).close

theorem source_environmentUnique {m} (w I J R S U V a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentUniqueSentence w I J R S U V a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.environment w I J U V a b c d) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (IndexTermImageCodeSyntax.environment w I J U V a b c d) := .hyp (Or.inl rfl)
  exact IndexTermImageEnvironment.unique hZ w I J R S U V a b c d h0 h1 h2

theorem environmentUnique_kernel_certificate {m} (w I J R S U V a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentUniqueSentence w I J R S U V a b c d)) := TheoryTransport.sentence (source_environmentUnique w I J R S U V a b c d)

theorem native_environmentUnique {m} (w I J R S U V a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentUniqueSentence w I J R S U V a b c d)) := ZFReplay.replay (environmentUnique_kernel_certificate w I J R S U V a b c d)

def termProgramIffSentence {m} (w I J R S a b c d r s n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxMapCodeSyntax.encoded w r a c I).imp ((SyntaxMapCodeSyntax.encoded w s b d J).imp (((TermTransformProgramSyntax.checked w R S a b c d n q).iff (SyntaxRenameTermSyntax.renamed w r s a b c d n q))))))).close

theorem source_termProgramIff {m} (w I J R S a b c d r s n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termProgramIffSentence w I J R S a b c d r s n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w s b d J) (Context.add (SyntaxMapCodeSyntax.encoded w r a c I) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c I) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d J) := .hyp (Or.inl rfl)
  exact IndexTermImageEnvironment.term_program_iff hZ w I J R S a b c d r s n q h0 h1 h2 h3

theorem termProgramIff_kernel_certificate {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termProgramIffSentence w I J R S a b c d r s n q)) := TheoryTransport.sentence (source_termProgramIff w I J R S a b c d r s n q)

theorem native_termProgramIff {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termProgramIffSentence w I J R S a b c d r s n q)) := ZFReplay.replay (termProgramIff_kernel_certificate w I J R S a b c d r s n q)

def membershipIffSentence {m} (w I J R S a b c d r s n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxMapCodeSyntax.encoded w r a c I).imp ((SyntaxMapCodeSyntax.encoded w s b d J).imp (((SyntaxRenameAtomSyntax.membership w r s a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.membership w R S a b c d n q))))))).close

theorem source_membershipIff {m} (w I J R S a b c d r s n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipIffSentence w I J R S a b c d r s n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w s b d J) (Context.add (SyntaxMapCodeSyntax.encoded w r a c I) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c I) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d J) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameAtoms.membership_iff hZ w I J R S a b c d r s n q h0 h1 h2 h3

theorem membershipIff_kernel_certificate {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipIffSentence w I J R S a b c d r s n q)) := TheoryTransport.sentence (source_membershipIff w I J R S a b c d r s n q)

theorem native_membershipIff {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipIffSentence w I J R S a b c d r s n q)) := ZFReplay.replay (membershipIff_kernel_certificate w I J R S a b c d r s n q)

def equalityIffSentence {m} (w I J R S a b c d r s n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxMapCodeSyntax.encoded w r a c I).imp ((SyntaxMapCodeSyntax.encoded w s b d J).imp (((SyntaxRenameAtomSyntax.equality w r s a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.equality w R S a b c d n q))))))).close

theorem source_equalityIff {m} (w I J R S a b c d r s n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityIffSentence w I J R S a b c d r s n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w s b d J) (Context.add (SyntaxMapCodeSyntax.encoded w r a c I) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c I) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d J) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameAtoms.equality_iff hZ w I J R S a b c d r s n q h0 h1 h2 h3

theorem equalityIff_kernel_certificate {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityIffSentence w I J R S a b c d r s n q)) := TheoryTransport.sentence (source_equalityIff w I J R S a b c d r s n q)

theorem native_equalityIff {m} (w I J R S a b c d r s n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityIffSentence w I J R S a b c d r s n q)) := ZFReplay.replay (equalityIff_kernel_certificate w I J R S a b c d r s n q)

def binderEnvironmentSentence {m} (w I J R S a b c d A C L K H : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxMapLiftSyntax.codedLift w a c I A C L).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((IndexTermImageCodeSyntax.environment w L J K H A b C d)))))).close

theorem source_binderEnvironment {m} (w I J R S a b c d A C L K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderEnvironmentSentence w I J R S a b c d A C L K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (SyntaxMapLiftSyntax.codedLift w a c I A C L) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c I A C L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact IndexTermCodedBinderTransport.coded_lift hZ w I J R S a b c d A C L K H h0 h1 h2 h3

theorem binderEnvironment_kernel_certificate {m} (w I J R S a b c d A C L K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderEnvironmentSentence w I J R S a b c d A C L K H)) := TheoryTransport.sentence (source_binderEnvironment w I J R S a b c d A C L K H)

theorem native_binderEnvironment {m} (w I J R S a b c d A C L K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderEnvironmentSentence w I J R S a b c d A C L K H)) := ZFReplay.replay (binderEnvironment_kernel_certificate w I J R S a b c d A C L K H)

def allMetadataAtNaturalSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((IndexFormulaRenameBridgeSyntax.property w n)))).close

theorem source_allMetadataAtNatural {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allMetadataAtNaturalSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameInduction.at_natural hZ w n h0 h1

theorem allMetadataAtNatural_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allMetadataAtNaturalSentence w n)) := TheoryTransport.sentence (source_allMetadataAtNatural w n)

theorem native_allMetadataAtNatural {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allMetadataAtNaturalSentence w n)) := ZFReplay.replay (allMetadataAtNatural_kernel_certificate w n)

def formulaForwardSentence {m} (w I J R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))))).close

theorem source_formulaForward {m} (w I J R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaForwardSentence w I J R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameInduction.forward hZ w I J R S a b c d n q h0 h1 h2

theorem formulaForward_kernel_certificate {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaForwardSentence w I J R S a b c d n q)) := TheoryTransport.sentence (source_formulaForward w I J R S a b c d n q)

theorem native_formulaForward {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaForwardSentence w I J R S a b c d n q)) := ZFReplay.replay (formulaForward_kernel_certificate w I J R S a b c d n q)

def formulaReverseSentence {m} (w I J R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q))))).close

theorem source_formulaReverse {m} (w I J R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaReverseSentence w I J R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameBridge.reverse hZ w I J R S a b c d n q h0 h1 h2

theorem formulaReverse_kernel_certificate {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaReverseSentence w I J R S a b c d n q)) := TheoryTransport.sentence (source_formulaReverse w I J R S a b c d n q)

theorem native_formulaReverse {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaReverseSentence w I J R S a b c d n q)) := ZFReplay.replay (formulaReverse_kernel_certificate w I J R S a b c d n q)

def formulaRenameIffSentence {m} (w I J R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp (((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))))).close

theorem source_formulaRenameIff {m} (w I J R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaRenameIffSentence w I J R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameBridge.rename_iff hZ w I J R S a b c d n q h0 h1

theorem formulaRenameIff_kernel_certificate {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaRenameIffSentence w I J R S a b c d n q)) := TheoryTransport.sentence (source_formulaRenameIff w I J R S a b c d n q)

theorem native_formulaRenameIff {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaRenameIffSentence w I J R S a b c d n q)) := ZFReplay.replay (formulaRenameIff_kernel_certificate w I J R S a b c d n q)

def formulaProgramIffSentence {m} (w I J R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q))))).close

theorem source_formulaProgramIff {m} (w I J R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaProgramIffSentence w I J R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inl rfl)
  exact IndexFormulaRenameBridge.program_iff hZ w I J R S a b c d n q h0 h1

theorem formulaProgramIff_kernel_certificate {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaProgramIffSentence w I J R S a b c d n q)) := TheoryTransport.sentence (source_formulaProgramIff w I J R S a b c d n q)

theorem native_formulaProgramIff {m} (w I J R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaProgramIffSentence w I J R S a b c d n q)) := ZFReplay.replay (formulaProgramIff_kernel_certificate w I J R S a b c d n q)

end PPAC.Migration.Internal.ObjectIndexFormulaRename
