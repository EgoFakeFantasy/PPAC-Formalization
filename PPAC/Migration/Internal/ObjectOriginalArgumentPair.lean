import PPAC.Migration.Internal.OriginalArgumentPairProgram

/-! 原有限参数森林的全索引字段对应与两参数任意候选输出程序桥的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalArgumentPair
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def finiteForestTypedListIffSentence {m} (k : Nat) (xs : Fin k → Fin m) (w len a b n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k len).imp ((SyntaxTermSyntax.contexts w a b).imp ((SyntaxForestSyntax.forest k w xs n).imp (((SyntaxMixedImageCodeSyntax.termList w len a b n).iff (ArgumentForestProgramSyntax.typedInputs k w a b xs))))))).close

theorem source_finiteForestTypedListIff {m} (k : Nat) (xs : Fin k → Fin m) (w len a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (finiteForestTypedListIffSentence k xs w len a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest k w xs n) (Context.add (SyntaxTermSyntax.contexts w a b) (Context.add (SyntaxNumeralSyntax.numeral k len) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k len) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTermSyntax.contexts w a b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxForestSyntax.forest k w xs n) := .hyp (Or.inl rfl)
  exact ArgumentForestTyping.list_iff hZ k w len a b n xs h0 h1 h2 h3

theorem finiteForestTypedListIff_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w len a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (finiteForestTypedListIffSentence k xs w len a b n)) := TheoryTransport.sentence (source_finiteForestTypedListIff k xs w len a b n)

theorem native_finiteForestTypedListIff {m} (k : Nat) (xs : Fin k → Fin m) (w len a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (finiteForestTypedListIffSentence k xs w len a b n)) := ZFReplay.replay (finiteForestTypedListIff_kernel_certificate k xs w len a b n)

def finiteForestAllIndexProgramFieldsIffSentence {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k len).imp ((SyntaxForestSyntax.forest k w xs n).imp ((SyntaxForestSyntax.forest k w ys q).imp (((ArgumentProgramFieldSyntax.fields w R S len n q).iff (ArgumentForestProgramSyntax.runs k w R S xs ys))))))).close

theorem source_finiteForestAllIndexProgramFieldsIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (finiteForestAllIndexProgramFieldsIffSentence k xs ys w R S len n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest k w ys q) (Context.add (SyntaxForestSyntax.forest k w xs n) (Context.add (SyntaxNumeralSyntax.numeral k len) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k len) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxForestSyntax.forest k w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxForestSyntax.forest k w ys q) := .hyp (Or.inl rfl)
  exact ArgumentForestProgramFields.fields_iff hZ k w R S len n q xs ys h0 h1 h2 h3

theorem finiteForestAllIndexProgramFieldsIff_kernel_certificate {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (finiteForestAllIndexProgramFieldsIffSentence k xs ys w R S len n q)) := TheoryTransport.sentence (source_finiteForestAllIndexProgramFieldsIff k xs ys w R S len n q)

theorem native_finiteForestAllIndexProgramFieldsIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (finiteForestAllIndexProgramFieldsIffSentence k xs ys w R S len n q)) := ZFReplay.replay (finiteForestAllIndexProgramFieldsIff_kernel_certificate k xs ys w R S len n q)

def finiteForestMappedProgramIffSentence {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k len).imp ((SyntaxTermSyntax.contexts w c d).imp ((SyntaxForestSyntax.forest k w xs n).imp ((SyntaxForestSyntax.forest k w ys q).imp (((ArgumentProgramFieldSyntax.mapped w R S len c d n q).iff ((ArgumentForestProgramSyntax.typedInputs k w c d ys).conj (ArgumentForestProgramSyntax.runs k w R S xs ys))))))))).close

theorem source_finiteForestMappedProgramIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (finiteForestMappedProgramIffSentence k xs ys w R S len c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest k w ys q) (Context.add (SyntaxForestSyntax.forest k w xs n) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (SyntaxNumeralSyntax.numeral k len) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k len) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxForestSyntax.forest k w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxForestSyntax.forest k w ys q) := .hyp (Or.inl rfl)
  exact ArgumentForestProgramFields.mapped_iff hZ k w R S len c d n q xs ys h0 h1 h2 h3 h4

theorem finiteForestMappedProgramIff_kernel_certificate {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (finiteForestMappedProgramIffSentence k xs ys w R S len c d n q)) := TheoryTransport.sentence (source_finiteForestMappedProgramIff k xs ys w R S len c d n q)

theorem native_finiteForestMappedProgramIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w R S len c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (finiteForestMappedProgramIffSentence k xs ys w R S len c d n q)) := ZFReplay.replay (finiteForestMappedProgramIff_kernel_certificate k xs ys w R S len c d n q)

def replaceOriginalRunAtFiniteForestsIffSentence {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth a b c L I R n q len : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxNumeralSyntax.numeral k len).imp ((SyntaxTermSyntax.contexts w a b).imp ((SyntaxForestSyntax.forest k w xs n).imp ((SyntaxForestSyntax.forest k w ys q).imp ((ArgumentForestProgramSyntax.typedInputs k w a b xs).imp (((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff ((ArgumentForestProgramSyntax.typedInputs k w a c ys).conj (ArgumentForestProgramSyntax.runs k w R L xs ys))))))))))))))).close

theorem source_replaceOriginalRunAtFiniteForestsIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth a b c L I R n q len : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth a b c L I R n q len) := by
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
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs k w a b xs) (Context.add (SyntaxForestSyntax.forest k w ys q) (Context.add (SyntaxForestSyntax.forest k w xs n) (Context.add (SyntaxTermSyntax.contexts w a b) (Context.add (SyntaxNumeralSyntax.numeral k len) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (SyntaxNumeralSyntax.numeral k len) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (SyntaxTermSyntax.contexts w a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (SyntaxForestSyntax.forest k w xs n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (SyntaxForestSyntax.forest k w ys q) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (ArgumentForestProgramSyntax.typedInputs k w a b xs) := .hyp (Or.inl rfl)
  exact OriginalArgumentForestProgram.replace_iff hZ k xs ys w mode depth a b c L I R n q len h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem replaceOriginalRunAtFiniteForestsIff_kernel_certificate {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth a b c L I R n q len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth a b c L I R n q len)) := TheoryTransport.sentence (source_replaceOriginalRunAtFiniteForestsIff k xs ys w mode depth a b c L I R n q len)

theorem native_replaceOriginalRunAtFiniteForestsIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth a b c L I R n q len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth a b c L I R n q len)) := ZFReplay.replay (replaceOriginalRunAtFiniteForestsIff_kernel_certificate k xs ys w mode depth a b c L I R n q len)

def weakenOriginalRunAtFiniteForestsIffSentence {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth parameter a b B I J R S n q len : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxNumeralSyntax.numeral k len).imp ((SyntaxTermSyntax.contexts w a b).imp ((SyntaxForestSyntax.forest k w xs n).imp ((SyntaxForestSyntax.forest k w ys q).imp ((ArgumentForestProgramSyntax.typedInputs k w a b xs).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff ((ArgumentForestProgramSyntax.typedInputs k w a B ys).conj (ArgumentForestProgramSyntax.runs k w R S xs ys)))))))))))))))).close

theorem source_weakenOriginalRunAtFiniteForestsIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth parameter a b B I J R S n q len : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth parameter a b B I J R S n q len) := by
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
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs k w a b xs) (Context.add (SyntaxForestSyntax.forest k w ys q) (Context.add (SyntaxForestSyntax.forest k w xs n) (Context.add (SyntaxTermSyntax.contexts w a b) (Context.add (SyntaxNumeralSyntax.numeral k len) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))))
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
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h7 : Derives Δ (SyntaxNumeralSyntax.numeral k len) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h8 : Derives Δ (SyntaxTermSyntax.contexts w a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h9 : Derives Δ (SyntaxForestSyntax.forest k w xs n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h10 : Derives Δ (SyntaxForestSyntax.forest k w ys q) := .hyp (Or.inr (Or.inl rfl))
  have h11 : Derives Δ (ArgumentForestProgramSyntax.typedInputs k w a b xs) := .hyp (Or.inl rfl)
  exact OriginalArgumentForestProgram.weaken_iff hZ k xs ys w mode depth parameter a b B I J R S n q len h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem weakenOriginalRunAtFiniteForestsIff_kernel_certificate {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth parameter a b B I J R S n q len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth parameter a b B I J R S n q len)) := TheoryTransport.sentence (source_weakenOriginalRunAtFiniteForestsIff k xs ys w mode depth parameter a b B I J R S n q len)

theorem native_weakenOriginalRunAtFiniteForestsIff {m} (k : Nat) (xs ys : Fin k → Fin m) (w mode depth parameter a b B I J R S n q len : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenOriginalRunAtFiniteForestsIffSentence k xs ys w mode depth parameter a b B I J R S n q len)) := ZFReplay.replay (weakenOriginalRunAtFiniteForestsIff_kernel_certificate k xs ys w mode depth parameter a b B I J R S n q len)

def twoArgumentListActualForestWitnessSentence {m} (w len a b q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 len).imp ((SyntaxMixedImageCodeSyntax.termList w len a b q).imp ((ArgumentPairOutput.output w a b q))))).close

theorem source_twoArgumentListActualForestWitness {m} (w len a b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (twoArgumentListActualForestWitnessSentence w len a b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w len a b q) (Context.add (SyntaxNumeralSyntax.numeral 2 len) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w len a b q) := .hyp (Or.inl rfl)
  exact ArgumentPairOutput.exists_output hZ w len a b q h0 h1 h2

theorem twoArgumentListActualForestWitness_kernel_certificate {m} (w len a b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (twoArgumentListActualForestWitnessSentence w len a b q)) := TheoryTransport.sentence (source_twoArgumentListActualForestWitness w len a b q)

theorem native_twoArgumentListActualForestWitness {m} (w len a b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (twoArgumentListActualForestWitnessSentence w len a b q)) := ZFReplay.replay (twoArgumentListActualForestWitness_kernel_certificate w len a b q)

def twoArgumentMappedAllCandidatesIffSentence {m} (w R S len c d n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 len).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n).imp (((ArgumentProgramFieldSyntax.mapped w R S len c d n q).iff (ArgumentPairProgramSyntax.returned w R S c d x y q)))))).close

theorem source_twoArgumentMappedAllCandidatesIff {m} (w R S len c d n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (twoArgumentMappedAllCandidatesIffSentence w R S len c d n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) (Context.add (SyntaxNumeralSyntax.numeral 2 len) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) := .hyp (Or.inl rfl)
  exact ArgumentPairProgramFields.mapped_iff hZ w R S len c d n q x y h0 h1 h2

theorem twoArgumentMappedAllCandidatesIff_kernel_certificate {m} (w R S len c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (twoArgumentMappedAllCandidatesIffSentence w R S len c d n q x y)) := TheoryTransport.sentence (source_twoArgumentMappedAllCandidatesIff w R S len c d n q x y)

theorem native_twoArgumentMappedAllCandidatesIff {m} (w R S len c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (twoArgumentMappedAllCandidatesIffSentence w R S len c d n q x y)) := ZFReplay.replay (twoArgumentMappedAllCandidatesIff_kernel_certificate w R S len c d n q x y)

def replaceOriginalTwoArgumentAllCandidatesIffSentence {m} (w mode depth a b c L I R n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff (ArgumentPairProgramSyntax.returned w R L a c x y q))))))))))).close

theorem source_replaceOriginalTwoArgumentAllCandidatesIff {m} (w mode depth a b c L I R n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceOriginalTwoArgumentAllCandidatesIffSentence w mode depth a b c L I R n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact OriginalArgumentPairProgram.replace_iff hZ w mode depth a b c L I R n q x y h0 h1 h2 h3 h4 h5 h6 h7

theorem replaceOriginalTwoArgumentAllCandidatesIff_kernel_certificate {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceOriginalTwoArgumentAllCandidatesIffSentence w mode depth a b c L I R n q x y)) := TheoryTransport.sentence (source_replaceOriginalTwoArgumentAllCandidatesIff w mode depth a b c L I R n q x y)

theorem native_replaceOriginalTwoArgumentAllCandidatesIff {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceOriginalTwoArgumentAllCandidatesIffSentence w mode depth a b c L I R n q x y)) := ZFReplay.replay (replaceOriginalTwoArgumentAllCandidatesIff_kernel_certificate w mode depth a b c L I R n q x y)

def weakenOriginalTwoArgumentAllCandidatesIffSentence {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (ArgumentPairProgramSyntax.returned w R S a B x y q)))))))))))).close

theorem source_weakenOriginalTwoArgumentAllCandidatesIff {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenOriginalTwoArgumentAllCandidatesIffSentence w mode depth parameter a b B I J R S n q x y) := by
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
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact OriginalArgumentPairProgram.weaken_iff hZ w mode depth parameter a b B I J R S n q x y h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem weakenOriginalTwoArgumentAllCandidatesIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenOriginalTwoArgumentAllCandidatesIffSentence w mode depth parameter a b B I J R S n q x y)) := TheoryTransport.sentence (source_weakenOriginalTwoArgumentAllCandidatesIff w mode depth parameter a b B I J R S n q x y)

theorem native_weakenOriginalTwoArgumentAllCandidatesIff {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenOriginalTwoArgumentAllCandidatesIffSentence w mode depth parameter a b B I J R S n q x y)) := ZFReplay.replay (weakenOriginalTwoArgumentAllCandidatesIff_kernel_certificate w mode depth parameter a b B I J R S n q x y)

def twoArgumentForestRecoveredFromActualFieldsSentence {m} (w len z e x y q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 len).imp ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxNumeralSyntax.numeral 1 e).imp ((StructuralListLengthSyntax.hasLength w q len).imp ((StructuralListFieldSyntax.field w q z x).imp ((StructuralListFieldSyntax.field w q e y).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) q))))))))).close

theorem source_twoArgumentForestRecoveredFromActualFields {m} (w len z e x y q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (twoArgumentForestRecoveredFromActualFieldsSentence w len z e x y q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w q e y) (Context.add (StructuralListFieldSyntax.field w q z x) (Context.add (StructuralListLengthSyntax.hasLength w q len) (Context.add (SyntaxNumeralSyntax.numeral 1 e) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Context.add (SyntaxNumeralSyntax.numeral 2 len) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 len) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListLengthSyntax.hasLength w q len) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListFieldSyntax.field w q z x) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListFieldSyntax.field w q e y) := .hyp (Or.inl rfl)
  exact ArgumentPairOutput.forest_of_fields hZ w len z e x y q h0 h1 h2 h3 h4 h5 h6

theorem twoArgumentForestRecoveredFromActualFields_kernel_certificate {m} (w len z e x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (twoArgumentForestRecoveredFromActualFieldsSentence w len z e x y q)) := TheoryTransport.sentence (source_twoArgumentForestRecoveredFromActualFields w len z e x y q)

theorem native_twoArgumentForestRecoveredFromActualFields {m} (w len z e x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (twoArgumentForestRecoveredFromActualFieldsSentence w len z e x y q)) := ZFReplay.replay (twoArgumentForestRecoveredFromActualFields_kernel_certificate w len z e x y q)

end PPAC.Migration.Internal.ObjectOriginalArgumentPair
