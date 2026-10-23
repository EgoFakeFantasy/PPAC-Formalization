import PPAC.Migration.Internal.OriginalArgumentFullProgramBridge

/-! 原参数列表与独立项程序全内部字段像完整对应之原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalArgumentFields
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def allCandidateOriginalListValueSentence {m} (w mode depth parameter k c d n q : Fin m) : Source.Sentence := ((OriginalArgumentValueSyntax.fiber w mode depth parameter k c d n).imp ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).imp ((OriginalArgumentValueSyntax.value w mode depth parameter k c d n q)))).close

theorem source_allCandidateOriginalListValue {m} (w mode depth parameter k c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allCandidateOriginalListValueSentence w mode depth parameter k c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) (Context.add (OriginalArgumentValueSyntax.fiber w mode depth parameter k c d n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalArgumentValueSyntax.fiber w mode depth parameter k c d n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) := .hyp (Or.inl rfl)
  exact OriginalArgumentCandidateValue.at_run w mode depth parameter k c d n q h0 h1

theorem allCandidateOriginalListValue_kernel_certificate {m} (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allCandidateOriginalListValueSentence w mode depth parameter k c d n q)) := TheoryTransport.sentence (source_allCandidateOriginalListValue w mode depth parameter k c d n q)

theorem native_allCandidateOriginalListValue {m} (w mode depth parameter k c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allCandidateOriginalListValueSentence w mode depth parameter k c d n q)) := ZFReplay.replay (allCandidateOriginalListValue_kernel_certificate w mode depth parameter k c d n q)

def originalAllInternalArgumentFieldsSentence {m} (three : Bool) (w mode depth parameter a b n k q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).imp ((OriginalArgumentFieldSyntax.fields w mode depth parameter k n q)))))))).close

theorem source_originalAllInternalArgumentFields {m} (three : Bool) (w mode depth parameter a b n k q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalAllInternalArgumentFieldsSentence three w mode depth parameter a b n k q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) (Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) := .hyp (Or.inl rfl)
  exact OriginalArgumentFieldInduction.actual_fields hZ three w mode depth parameter a b n k q h0 h1 h2 h3 h4 h5

theorem originalAllInternalArgumentFields_kernel_certificate {m} (three : Bool) (w mode depth parameter a b n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalAllInternalArgumentFieldsSentence three w mode depth parameter a b n k q)) := TheoryTransport.sentence (source_originalAllInternalArgumentFields three w mode depth parameter a b n k q)

theorem native_originalAllInternalArgumentFields {m} (three : Bool) (w mode depth parameter a b n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalAllInternalArgumentFieldsSentence three w mode depth parameter a b n k q)) := ZFReplay.replay (originalAllInternalArgumentFields_kernel_certificate three w mode depth parameter a b n k q)

def originalAllInternalFieldCodePropertiesSentence {m} (three : Bool) (w mode depth parameter a b : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (OriginalArgumentFieldSyntax.property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc (Fin.last m))))))))).close

theorem source_originalAllInternalFieldCodeProperties {m} (three : Bool) (w mode depth parameter a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalAllInternalFieldCodePropertiesSentence three w mode depth parameter a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inl rfl)
  exact OriginalArgumentFieldInduction.all_properties hZ three w mode depth parameter a b h0 h1 h2 h3

theorem originalAllInternalFieldCodeProperties_kernel_certificate {m} (three : Bool) (w mode depth parameter a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalAllInternalFieldCodePropertiesSentence three w mode depth parameter a b)) := TheoryTransport.sentence (source_originalAllInternalFieldCodeProperties three w mode depth parameter a b)

theorem native_originalAllInternalFieldCodeProperties {m} (three : Bool) (w mode depth parameter a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalAllInternalFieldCodePropertiesSentence three w mode depth parameter a b)) := ZFReplay.replay (originalAllInternalFieldCodeProperties_kernel_certificate three w mode depth parameter a b)

def allInternalFieldImageOutputUniqueSentence {m} (w mode depth parameter a b c d k n q r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d).imp ((OriginalArgumentFieldSyntax.fields w mode depth parameter k n q).imp ((OriginalArgumentFieldSyntax.fields w mode depth parameter k n r).imp ((SyntaxMixedImageCodeSyntax.termList w k c d q).imp ((SyntaxMixedImageCodeSyntax.termList w k c d r).imp ((Formula.equal q r))))))))).close

theorem source_allInternalFieldImageOutputUnique {m} (w mode depth parameter a b c d k n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFieldImageOutputUniqueSentence w mode depth parameter a b c d k n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k c d r) (Context.add (SyntaxMixedImageCodeSyntax.termList w k c d q) (Context.add (OriginalArgumentFieldSyntax.fields w mode depth parameter k n r) (Context.add (OriginalArgumentFieldSyntax.fields w mode depth parameter k n q) (Context.add (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) (Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (OriginalArgumentFieldSyntax.fields w mode depth parameter k n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (OriginalArgumentFieldSyntax.fields w mode depth parameter k n r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k c d q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k c d r) := .hyp (Or.inl rfl)
  exact OriginalArgumentFieldUnique.outputs_unique hZ w mode depth parameter a b c d k n q r h0 h1 h2 h3 h4 h5 h6

theorem allInternalFieldImageOutputUnique_kernel_certificate {m} (w mode depth parameter a b c d k n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFieldImageOutputUniqueSentence w mode depth parameter a b c d k n q r)) := TheoryTransport.sentence (source_allInternalFieldImageOutputUnique w mode depth parameter a b c d k n q r)

theorem native_allInternalFieldImageOutputUnique {m} (w mode depth parameter a b c d k n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFieldImageOutputUniqueSentence w mode depth parameter a b c d k n q r)) := ZFReplay.replay (allInternalFieldImageOutputUnique_kernel_certificate w mode depth parameter a b c d k n q r)

def originalRunAllFieldImageIffSentence {m} (three : Bool) (w mode depth parameter a b c d n k q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxTermSyntax.contexts w c d).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (OriginalArgumentFieldCompletion.mapped w mode depth parameter k c d n q)))))))))).close

theorem source_originalRunAllFieldImageIff {m} (three : Bool) (w mode depth parameter a b c d n k q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRunAllFieldImageIffSentence three w mode depth parameter a b c d n k q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentFieldCompletion.run_iff hZ three w mode depth parameter a b c d n k q h0 h1 h2 h3 h4 h5 h6

theorem originalRunAllFieldImageIff_kernel_certificate {m} (three : Bool) (w mode depth parameter a b c d n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRunAllFieldImageIffSentence three w mode depth parameter a b c d n k q)) := TheoryTransport.sentence (source_originalRunAllFieldImageIff three w mode depth parameter a b c d n k q)

theorem native_originalRunAllFieldImageIff {m} (three : Bool) (w mode depth parameter a b c d n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRunAllFieldImageIffSentence three w mode depth parameter a b c d n k q)) := ZFReplay.replay (originalRunAllFieldImageIff_kernel_certificate three w mode depth parameter a b c d n k q)

def replaceAllInternalProgramFieldsIffSentence {m} (w mode depth a b c L I R n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalArgumentFieldSyntax.fields w mode depth L k n q).iff (ArgumentProgramFieldSyntax.fields w R L k n q)))))))))).close

theorem source_replaceAllInternalProgramFieldsIff {m} (w mode depth a b c L I R n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceAllInternalProgramFieldsIffSentence w mode depth a b c L I R n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentProgramFields.replace_fields_iff hZ w mode depth a b c L I R n q k h0 h1 h2 h3 h4 h5 h6

theorem replaceAllInternalProgramFieldsIff_kernel_certificate {m} (w mode depth a b c L I R n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceAllInternalProgramFieldsIffSentence w mode depth a b c L I R n q k)) := TheoryTransport.sentence (source_replaceAllInternalProgramFieldsIff w mode depth a b c L I R n q k)

theorem native_replaceAllInternalProgramFieldsIff {m} (w mode depth a b c L I R n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceAllInternalProgramFieldsIffSentence w mode depth a b c L I R n q k)) := ZFReplay.replay (replaceAllInternalProgramFieldsIff_kernel_certificate w mode depth a b c L I R n q k)

def replaceWholeOriginalArgumentProgramIffSentence {m} (w mode depth a b c L I R n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff (ArgumentProgramFieldSyntax.mapped w R L k a c n q)))))))))).close

theorem source_replaceWholeOriginalArgumentProgramIff {m} (w mode depth a b c L I R n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceWholeOriginalArgumentProgramIffSentence w mode depth a b c L I R n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentFullProgramBridge.replace_iff hZ w mode depth a b c L I R n q k h0 h1 h2 h3 h4 h5 h6

theorem replaceWholeOriginalArgumentProgramIff_kernel_certificate {m} (w mode depth a b c L I R n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceWholeOriginalArgumentProgramIffSentence w mode depth a b c L I R n q k)) := TheoryTransport.sentence (source_replaceWholeOriginalArgumentProgramIff w mode depth a b c L I R n q k)

theorem native_replaceWholeOriginalArgumentProgramIff {m} (w mode depth a b c L I R n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceWholeOriginalArgumentProgramIffSentence w mode depth a b c L I R n q k)) := ZFReplay.replay (replaceWholeOriginalArgumentProgramIff_kernel_certificate w mode depth a b c L I R n q k)

def weakenAllInternalProgramFieldsIffSentence {m} (w mode depth parameter a b B I J R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalArgumentFieldSyntax.fields w mode depth parameter k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q))))))))))).close

theorem source_weakenAllInternalProgramFieldsIff {m} (w mode depth parameter a b B I J R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenAllInternalProgramFieldsIffSentence w mode depth parameter a b B I J R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h7 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentProgramFields.weaken_fields_iff hZ w mode depth parameter a b B I J R S n q k h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenAllInternalProgramFieldsIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenAllInternalProgramFieldsIffSentence w mode depth parameter a b B I J R S n q k)) := TheoryTransport.sentence (source_weakenAllInternalProgramFieldsIff w mode depth parameter a b B I J R S n q k)

theorem native_weakenAllInternalProgramFieldsIff {m} (w mode depth parameter a b B I J R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenAllInternalProgramFieldsIffSentence w mode depth parameter a b B I J R S n q k)) := ZFReplay.replay (weakenAllInternalProgramFieldsIff_kernel_certificate w mode depth parameter a b B I J R S n q k)

def weakenWholeOriginalArgumentProgramIffSentence {m} (w mode depth parameter a b B I J R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (ArgumentProgramFieldSyntax.mapped w R S k a B n q))))))))))).close

theorem source_weakenWholeOriginalArgumentProgramIff {m} (w mode depth parameter a b B I J R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenWholeOriginalArgumentProgramIffSentence w mode depth parameter a b B I J R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h7 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact OriginalArgumentFullProgramBridge.weaken_iff hZ w mode depth parameter a b B I J R S n q k h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenWholeOriginalArgumentProgramIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenWholeOriginalArgumentProgramIffSentence w mode depth parameter a b B I J R S n q k)) := TheoryTransport.sentence (source_weakenWholeOriginalArgumentProgramIff w mode depth parameter a b B I J R S n q k)

theorem native_weakenWholeOriginalArgumentProgramIff {m} (w mode depth parameter a b B I J R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenWholeOriginalArgumentProgramIffSentence w mode depth parameter a b B I J R S n q k)) := ZFReplay.replay (weakenWholeOriginalArgumentProgramIff_kernel_certificate w mode depth parameter a b B I J R S n q k)

def originalConsAllInternalFieldsSentence {m} (w mode depth parameter ell k h t H T n q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((Formula.mem H w).imp ((Formula.mem T w).imp ((Formula.mem ell w).imp ((successor k ell).imp ((StructuralListSyntax.consCode w h t n).imp ((StructuralListSyntax.consCode w H T q).imp ((OriginalTransformRowSyntax.run 1 w mode depth parameter h H).imp ((OriginalArgumentFieldSyntax.fields w mode depth parameter ell t T).imp ((OriginalArgumentFieldSyntax.fields w mode depth parameter k n q))))))))))))).close

theorem source_originalConsAllInternalFields {m} (w mode depth parameter ell k h t H T n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalConsAllInternalFieldsSentence w mode depth parameter ell k h t H T n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalArgumentFieldSyntax.fields w mode depth parameter ell t T) (Context.add (OriginalTransformRowSyntax.run 1 w mode depth parameter h H) (Context.add (StructuralListSyntax.consCode w H T q) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (successor k ell) (Context.add (Formula.mem ell w) (Context.add (Formula.mem T w) (Context.add (Formula.mem H w) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (Formula.mem H w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (Formula.mem T w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (Formula.mem ell w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (successor k ell) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (StructuralListSyntax.consCode w H T q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (OriginalTransformRowSyntax.run 1 w mode depth parameter h H) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (OriginalArgumentFieldSyntax.fields w mode depth parameter ell t T) := .hyp (Or.inl rfl)
  exact OriginalArgumentConsFields.cons_fields hZ w mode depth parameter ell k h t H T n q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem originalConsAllInternalFields_kernel_certificate {m} (w mode depth parameter ell k h t H T n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalConsAllInternalFieldsSentence w mode depth parameter ell k h t H T n q)) := TheoryTransport.sentence (source_originalConsAllInternalFields w mode depth parameter ell k h t H T n q)

theorem native_originalConsAllInternalFields {m} (w mode depth parameter ell k h t H T n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalConsAllInternalFieldsSentence w mode depth parameter ell k h t H T n q)) := ZFReplay.replay (originalConsAllInternalFields_kernel_certificate w mode depth parameter ell k h t H T n q)

end PPAC.Migration.Internal.ObjectOriginalArgumentFields
