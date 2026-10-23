import PPAC.Migration.Internal.OriginalTermProgramBridge

/-! 原mode0／3纯签名项桥的源ZF闭句与原nativeZF回放证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalTermProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

def replace_checked_iffSentence {m} (w depth a b c L I R n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp (((OriginalTermTraceSyntax.checked true w depth L a b n q).iff ((OriginalTermTraceSyntax.metadata w depth L).conj (TermTransformProgramSyntax.checked w R L a b a c n q)))))))).close

theorem source_replace_checked_iff {m} (w depth a b c L I R n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replace_checked_iffSentence w depth a b c L I R n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inl rfl)
  exact OriginalTermProgramBridge.replace_checked_iff hZ w depth a b c L I R n q h0 h1 h2 h3

theorem replace_checked_iff_kernel_certificate {m} (w depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replace_checked_iffSentence w depth a b c L I R n q)) := TheoryTransport.sentence (source_replace_checked_iff w depth a b c L I R n q)

theorem native_replace_checked_iff {m} (w depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replace_checked_iffSentence w depth a b c L I R n q)) := ZFReplay.replay (replace_checked_iff_kernel_certificate w depth a b c L I R n q)

def replace_coded_iffSentence {m} (w depth a b c L I R n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp (((OriginalTermTraceSyntax.checked true w depth L a b n q).iff ((OriginalTermTraceSyntax.metadata w depth L).conj (SyntaxCodedMixedTermSyntax.substituted w R L a b a c n q)))))))).close

theorem source_replace_coded_iff {m} (w depth a b c L I R n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replace_coded_iffSentence w depth a b c L I R n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inl rfl)
  exact OriginalTermProgramBridge.replace_coded_iff hZ w depth a b c L I R n q h0 h1 h2 h3

theorem replace_coded_iff_kernel_certificate {m} (w depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replace_coded_iffSentence w depth a b c L I R n q)) := TheoryTransport.sentence (source_replace_coded_iff w depth a b c L I R n q)

theorem native_replace_coded_iff {m} (w depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replace_coded_iffSentence w depth a b c L I R n q)) := ZFReplay.replay (replace_coded_iff_kernel_certificate w depth a b c L I R n q)

def weaken_checked_iffSentence {m} (w depth parameter a b B I J R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp (((OriginalTermTraceSyntax.checked false w depth parameter a b n q).iff ((OriginalTermTraceSyntax.metadata w depth parameter).conj (TermTransformProgramSyntax.checked w R S a b a B n q))))))))).close

theorem source_weaken_checked_iff {m} (w depth parameter a b B I J R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weaken_checked_iffSentence w depth parameter a b B I J R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inl rfl)
  exact OriginalTermProgramBridge.weaken_checked_iff hZ w depth parameter a b B I J R S n q h0 h1 h2 h3 h4

theorem weaken_checked_iff_kernel_certificate {m} (w depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weaken_checked_iffSentence w depth parameter a b B I J R S n q)) := TheoryTransport.sentence (source_weaken_checked_iff w depth parameter a b B I J R S n q)

theorem native_weaken_checked_iff {m} (w depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weaken_checked_iffSentence w depth parameter a b B I J R S n q)) := ZFReplay.replay (weaken_checked_iff_kernel_certificate w depth parameter a b B I J R S n q)

def weaken_coded_iffSentence {m} (w depth parameter a b B I J R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp (((OriginalTermTraceSyntax.checked false w depth parameter a b n q).iff ((OriginalTermTraceSyntax.metadata w depth parameter).conj (SyntaxCodedMixedTermSyntax.substituted w R S a b a B n q))))))))).close

theorem source_weaken_coded_iff {m} (w depth parameter a b B I J R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weaken_coded_iffSentence w depth parameter a b B I J R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inl rfl)
  exact OriginalTermProgramBridge.weaken_coded_iff hZ w depth parameter a b B I J R S n q h0 h1 h2 h3 h4

theorem weaken_coded_iff_kernel_certificate {m} (w depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weaken_coded_iffSentence w depth parameter a b B I J R S n q)) := TheoryTransport.sentence (source_weaken_coded_iff w depth parameter a b B I J R S n q)

theorem native_weaken_coded_iff {m} (w depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weaken_coded_iffSentence w depth parameter a b B I J R S n q)) := ZFReplay.replay (weaken_coded_iff_kernel_certificate w depth parameter a b B I J R S n q)

end PPAC.Migration.Internal.ObjectOriginalTermProgram
