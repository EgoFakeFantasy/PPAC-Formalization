import PPAC.Migration.Internal.OriginalArgumentsRunEquation

/-! 原arity赋值与根行均消去的mode0/3参数列表整体运行方程之原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalArgumentRun
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def originalRunInputNaturalSentence {m} (kind : Nat) (w mode depth parameter input output : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.run kind w mode depth parameter input output).imp ((Formula.mem input w)))).close

theorem source_originalRunInputNatural {m} (kind : Nat) (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRunInputNaturalSentence kind w mode depth parameter input output) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run kind w mode depth parameter input output) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run kind w mode depth parameter input output) := .hyp (Or.inl rfl)
  exact OriginalArgumentRunNaturality.input_natural hZ kind w mode depth parameter input output h0 h1

theorem originalRunInputNatural_kernel_certificate {m} (kind : Nat) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRunInputNaturalSentence kind w mode depth parameter input output)) := TheoryTransport.sentence (source_originalRunInputNatural kind w mode depth parameter input output)

theorem native_originalRunInputNatural {m} (kind : Nat) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRunInputNaturalSentence kind w mode depth parameter input output)) := ZFReplay.replay (originalRunInputNatural_kernel_certificate kind w mode depth parameter input output)

def originalRunOutputNaturalSentence {m} (kind : Nat) (w mode depth parameter input output : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.run kind w mode depth parameter input output).imp ((Formula.mem output w)))).close

theorem source_originalRunOutputNatural {m} (kind : Nat) (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRunOutputNaturalSentence kind w mode depth parameter input output) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run kind w mode depth parameter input output) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run kind w mode depth parameter input output) := .hyp (Or.inl rfl)
  exact OriginalArgumentRunNaturality.output_natural hZ kind w mode depth parameter input output h0 h1

theorem originalRunOutputNatural_kernel_certificate {m} (kind : Nat) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRunOutputNaturalSentence kind w mode depth parameter input output)) := TheoryTransport.sentence (source_originalRunOutputNatural kind w mode depth parameter input output)

theorem native_originalRunOutputNatural {m} (kind : Nat) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRunOutputNaturalSentence kind w mode depth parameter input output)) := ZFReplay.replay (originalRunOutputNatural_kernel_certificate kind w mode depth parameter input output)

def actualOriginalArgumentRootSentence {m} (w mode depth parameter input output : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem mode w).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((Formula.mem input w).imp ((Formula.mem output w).imp ((Formula.ex ((Formula.mem (Fin.last m) w.castSucc).conj (OriginalTransformRowSyntax.row 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m))))))))))).close

theorem source_actualOriginalArgumentRoot {m} (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualOriginalArgumentRootSentence w mode depth parameter input output) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem output w) (Context.add (Formula.mem input w) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (Formula.mem mode w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem mode w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem input w) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (Formula.mem output w) := .hyp (Or.inl rfl)
  exact OriginalArgumentRoots.exists_row hZ 2 w mode depth parameter input output h0 h1 h2 h3 h4 h5

theorem actualOriginalArgumentRoot_kernel_certificate {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualOriginalArgumentRootSentence w mode depth parameter input output)) := TheoryTransport.sentence (source_actualOriginalArgumentRoot w mode depth parameter input output)

theorem native_actualOriginalArgumentRoot {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualOriginalArgumentRootSentence w mode depth parameter input output)) := ZFReplay.replay (actualOriginalArgumentRoot_kernel_certificate w mode depth parameter input output)

def originalArgumentOutcomesNaturalSentence {m} (w mode depth parameter input output : Fin m) : Source.Sentence := ((omega w).imp ((OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output).imp (((Formula.mem input w).conj (.mem output w))))).close

theorem source_originalArgumentOutcomesNatural {m} (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalArgumentOutcomesNaturalSentence w mode depth parameter input output) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output) := .hyp (Or.inl rfl)
  exact OriginalArgumentRoots.outcomes_natural hZ w mode depth parameter input output h0 h1

theorem originalArgumentOutcomesNatural_kernel_certificate {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalArgumentOutcomesNaturalSentence w mode depth parameter input output)) := TheoryTransport.sentence (source_originalArgumentOutcomesNatural w mode depth parameter input output)

theorem native_originalArgumentOutcomesNatural {m} (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalArgumentOutcomesNaturalSentence w mode depth parameter input output)) := ZFReplay.replay (originalArgumentOutcomesNatural_kernel_certificate w mode depth parameter input output)

def originalNilApplicationExactIffSentence {m} (three : Bool) (w mode depth parameter input output r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTransformRowSyntax.row 2 w mode depth parameter input output r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments) w r V).iff (OriginalArgumentCaseSyntax.nilData w input output))))))).close

theorem source_originalNilApplicationExactIff {m} (three : Bool) (w mode depth parameter input output r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalNilApplicationExactIffSentence three w mode depth parameter input output r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalArgumentsNilApplication.application_iff hZ three w mode depth parameter input output r V h0 h1 h2 h3

theorem originalNilApplicationExactIff_kernel_certificate {m} (three : Bool) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalNilApplicationExactIffSentence three w mode depth parameter input output r V)) := TheoryTransport.sentence (source_originalNilApplicationExactIff three w mode depth parameter input output r V)

theorem native_originalNilApplicationExactIff {m} (three : Bool) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalNilApplicationExactIffSentence three w mode depth parameter input output r V)) := ZFReplay.replay (originalNilApplicationExactIff_kernel_certificate three w mode depth parameter input output r V)

def originalConsApplicationExactIffSentence {m} (w mode depth parameter input output r V : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.row 2 w mode depth parameter input output r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments) w r V).iff (OriginalArgumentCaseSyntax.consCase w mode depth parameter input output)))))).close

theorem source_originalConsApplicationExactIff {m} (w mode depth parameter input output r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalConsApplicationExactIffSentence w mode depth parameter input output r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalArgumentsConsApplication.application_iff hZ w mode depth parameter input output r V h0 h1 h2

theorem originalConsApplicationExactIff_kernel_certificate {m} (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalConsApplicationExactIffSentence w mode depth parameter input output r V)) := TheoryTransport.sentence (source_originalConsApplicationExactIff w mode depth parameter input output r V)

theorem native_originalConsApplicationExactIff {m} (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalConsApplicationExactIffSentence w mode depth parameter input output r V)) := ZFReplay.replay (originalConsApplicationExactIff_kernel_certificate w mode depth parameter input output r V)

def originalArgumentTraceCasesExactIffSentence {m} (three : Bool) (w mode depth parameter input output r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTransformRowSyntax.row 2 w mode depth parameter input output r).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output)))))).close

theorem source_originalArgumentTraceCasesExactIff {m} (three : Bool) (w mode depth parameter input output r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalArgumentTraceCasesExactIffSentence three w mode depth parameter input output r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) := .hyp (Or.inl rfl)
  exact OriginalArgumentsTraceEquation.at_row hZ three w mode depth parameter input output r h0 h1 h2

theorem originalArgumentTraceCasesExactIff_kernel_certificate {m} (three : Bool) (w mode depth parameter input output r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalArgumentTraceCasesExactIffSentence three w mode depth parameter input output r)) := TheoryTransport.sentence (source_originalArgumentTraceCasesExactIff three w mode depth parameter input output r)

theorem native_originalArgumentTraceCasesExactIff {m} (three : Bool) (w mode depth parameter input output r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalArgumentTraceCasesExactIffSentence three w mode depth parameter input output r)) := ZFReplay.replay (originalArgumentTraceCasesExactIff_kernel_certificate three w mode depth parameter input output r)

def originalArgumentWholeRunCasesExactIffSentence {m} (three : Bool) (w mode depth parameter input output : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter input output).iff (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output))))))).close

theorem source_originalArgumentWholeRunCasesExactIff {m} (three : Bool) (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalArgumentWholeRunCasesExactIffSentence three w mode depth parameter input output) := by
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
  exact OriginalArgumentsRunEquation.run_iff hZ three w mode depth parameter input output h0 h1 h2 h3

theorem originalArgumentWholeRunCasesExactIff_kernel_certificate {m} (three : Bool) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalArgumentWholeRunCasesExactIffSentence three w mode depth parameter input output)) := TheoryTransport.sentence (source_originalArgumentWholeRunCasesExactIff three w mode depth parameter input output)

theorem native_originalArgumentWholeRunCasesExactIff {m} (three : Bool) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalArgumentWholeRunCasesExactIffSentence three w mode depth parameter input output)) := ZFReplay.replay (originalArgumentWholeRunCasesExactIff_kernel_certificate three w mode depth parameter input output)

end PPAC.Migration.Internal.ObjectOriginalArgumentRun
