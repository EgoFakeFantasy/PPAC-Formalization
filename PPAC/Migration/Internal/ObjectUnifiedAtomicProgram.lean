import PPAC.Migration.Internal.OriginalAtomicProgram

/-! 内部atomic守卫下整条原运行与既有Program四分支编译公式的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectUnifiedAtomicProgram
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def compiledAtomicProgramSourceSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b c d h n q).imp ((SyntaxAtomSyntax.atomic w a b n))).close

theorem source_compiledAtomicProgramSource {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compiledAtomicProgramSourceSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b c d h n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b c d h n q) := .hyp (Or.inl rfl)
  exact FormulaAtomicProgramSyntax.source w R S a b c d n q h0

theorem compiledAtomicProgramSource_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compiledAtomicProgramSourceSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_compiledAtomicProgramSource w R S a b c d h n q)

theorem native_compiledAtomicProgramSource {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compiledAtomicProgramSourceSentence w R S a b c d h n q)) := ZFReplay.replay (compiledAtomicProgramSource_kernel_certificate w R S a b c d h n q)

def replaceTypedMembershipWholeRunIffSentence {m} (w mode depth a b c L I R n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.membership w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.membership w R L a b a c n q)))))))))).close

theorem source_replaceTypedMembershipWholeRunIff {m} (w mode depth a b c L I R n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceTypedMembershipWholeRunIffSentence w mode depth a b c L I R n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.membership w a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.membership w a b n) := .hyp (Or.inl rfl)
  exact OriginalTypedAtomicCases.replace_membership_iff hZ w mode depth a b c L I R n q h0 h1 h2 h3 h4 h5 h6

theorem replaceTypedMembershipWholeRunIff_kernel_certificate {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceTypedMembershipWholeRunIffSentence w mode depth a b c L I R n q)) := TheoryTransport.sentence (source_replaceTypedMembershipWholeRunIff w mode depth a b c L I R n q)

theorem native_replaceTypedMembershipWholeRunIff {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceTypedMembershipWholeRunIffSentence w mode depth a b c L I R n q)) := ZFReplay.replay (replaceTypedMembershipWholeRunIff_kernel_certificate w mode depth a b c L I R n q)

def replaceTypedEqualityWholeRunIffSentence {m} (w mode depth a b c L I R n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.equality w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q)))))))))).close

theorem source_replaceTypedEqualityWholeRunIff {m} (w mode depth a b c L I R n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceTypedEqualityWholeRunIffSentence w mode depth a b c L I R n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equality w a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.equality w a b n) := .hyp (Or.inl rfl)
  exact OriginalTypedAtomicCases.replace_equality_iff hZ w mode depth a b c L I R n q h0 h1 h2 h3 h4 h5 h6

theorem replaceTypedEqualityWholeRunIff_kernel_certificate {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceTypedEqualityWholeRunIffSentence w mode depth a b c L I R n q)) := TheoryTransport.sentence (source_replaceTypedEqualityWholeRunIff w mode depth a b c L I R n q)

theorem native_replaceTypedEqualityWholeRunIff {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceTypedEqualityWholeRunIffSentence w mode depth a b c L I R n q)) := ZFReplay.replay (replaceTypedEqualityWholeRunIff_kernel_certificate w mode depth a b c L I R n q)

def replaceUnifiedAtomicProgramIffSentence {m} (w mode depth a b c L I R h n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R L a b a c h n q)))))))))).close

theorem source_replaceUnifiedAtomicProgramIff {m} (w mode depth a b c L I R h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceUnifiedAtomicProgramIffSentence w mode depth a b c L I R h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact OriginalAtomicProgram.replace_program_iff hZ w mode depth a b c L I R h n q h0 h1 h2 h3 h4 h5 h6

theorem replaceUnifiedAtomicProgramIff_kernel_certificate {m} (w mode depth a b c L I R h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceUnifiedAtomicProgramIffSentence w mode depth a b c L I R h n q)) := TheoryTransport.sentence (source_replaceUnifiedAtomicProgramIff w mode depth a b c L I R h n q)

theorem native_replaceUnifiedAtomicProgramIff {m} (w mode depth a b c L I R h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceUnifiedAtomicProgramIffSentence w mode depth a b c L I R h n q)) := ZFReplay.replay (replaceUnifiedAtomicProgramIff_kernel_certificate w mode depth a b c L I R h n q)

def weakenTypedMembershipWholeRunIffSentence {m} (w mode depth parameter a b B I J R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.membership w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.membership w R S a b a B n q))))))))))).close

theorem source_weakenTypedMembershipWholeRunIff {m} (w mode depth parameter a b B I J R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenTypedMembershipWholeRunIffSentence w mode depth parameter a b B I J R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.membership w a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxAtomSyntax.membership w a b n) := .hyp (Or.inl rfl)
  exact OriginalTypedAtomicCases.weaken_membership_iff hZ w mode depth parameter a b B I J R S n q h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenTypedMembershipWholeRunIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenTypedMembershipWholeRunIffSentence w mode depth parameter a b B I J R S n q)) := TheoryTransport.sentence (source_weakenTypedMembershipWholeRunIff w mode depth parameter a b B I J R S n q)

theorem native_weakenTypedMembershipWholeRunIff {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenTypedMembershipWholeRunIffSentence w mode depth parameter a b B I J R S n q)) := ZFReplay.replay (weakenTypedMembershipWholeRunIff_kernel_certificate w mode depth parameter a b B I J R S n q)

def weakenTypedEqualityWholeRunIffSentence {m} (w mode depth parameter a b B I J R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.equality w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q))))))))))).close

theorem source_weakenTypedEqualityWholeRunIff {m} (w mode depth parameter a b B I J R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenTypedEqualityWholeRunIffSentence w mode depth parameter a b B I J R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equality w a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxAtomSyntax.equality w a b n) := .hyp (Or.inl rfl)
  exact OriginalTypedAtomicCases.weaken_equality_iff hZ w mode depth parameter a b B I J R S n q h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenTypedEqualityWholeRunIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenTypedEqualityWholeRunIffSentence w mode depth parameter a b B I J R S n q)) := TheoryTransport.sentence (source_weakenTypedEqualityWholeRunIff w mode depth parameter a b B I J R S n q)

theorem native_weakenTypedEqualityWholeRunIff {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenTypedEqualityWholeRunIffSentence w mode depth parameter a b B I J R S n q)) := ZFReplay.replay (weakenTypedEqualityWholeRunIff_kernel_certificate w mode depth parameter a b B I J R S n q)

def weakenUnifiedAtomicProgramIffSentence {m} (w mode depth parameter a b B I J R S h n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b a B h n q))))))))))).close

theorem source_weakenUnifiedAtomicProgramIff {m} (w mode depth parameter a b B I J R S h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenUnifiedAtomicProgramIffSentence w mode depth parameter a b B I J R S h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact OriginalAtomicProgram.weaken_program_iff hZ w mode depth parameter a b B I J R S h n q h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenUnifiedAtomicProgramIff_kernel_certificate {m} (w mode depth parameter a b B I J R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenUnifiedAtomicProgramIffSentence w mode depth parameter a b B I J R S h n q)) := TheoryTransport.sentence (source_weakenUnifiedAtomicProgramIff w mode depth parameter a b B I J R S h n q)

theorem native_weakenUnifiedAtomicProgramIff {m} (w mode depth parameter a b B I J R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenUnifiedAtomicProgramIffSentence w mode depth parameter a b B I J R S h n q)) := ZFReplay.replay (weakenUnifiedAtomicProgramIff_kernel_certificate w mode depth parameter a b B I J R S h n q)

end PPAC.Migration.Internal.ObjectUnifiedAtomicProgram
