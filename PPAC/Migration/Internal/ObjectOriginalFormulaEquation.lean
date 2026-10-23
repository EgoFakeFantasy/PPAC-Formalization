import PPAC.Migration.Internal.OriginalFormulaRunEquation

/-! 原十一公式arity消去和全部内部候选Run₃整体方程之原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalFormulaEquation
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def originalFormulaConstantAssignmentEliminatedSentence {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) w r V).iff (OriginalFormulaLocalData.constant tag w n q))))))).close

theorem source_originalFormulaConstantAssignmentEliminated {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaConstantAssignmentEliminatedSentence three tag _hr w mode depth parameter n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaArityApplications.constant_iff hZ three tag _hr w mode depth parameter n q r V h0 h1 h2 h3

theorem originalFormulaConstantAssignmentEliminated_kernel_certificate {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaConstantAssignmentEliminatedSentence three tag _hr w mode depth parameter n q r V)) := TheoryTransport.sentence (source_originalFormulaConstantAssignmentEliminated three tag _hr w mode depth parameter n q r V)

theorem native_originalFormulaConstantAssignmentEliminated {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaConstantAssignmentEliminatedSentence three tag _hr w mode depth parameter n q r V)) := ZFReplay.replay (originalFormulaConstantAssignmentEliminated_kernel_certificate three tag _hr w mode depth parameter n q r V)

def originalFormulaBinaryAssignmentEliminatedSentence {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) w r V).iff (OriginalFormulaCaseSyntax.binaryCase tag kind w mode depth parameter n q)))))).close

theorem source_originalFormulaBinaryAssignmentEliminated {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinaryAssignmentEliminatedSentence tag kind _hr w mode depth parameter n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaArityApplications.binary_iff hZ tag kind _hr w mode depth parameter n q r V h0 h1 h2

theorem originalFormulaBinaryAssignmentEliminated_kernel_certificate {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinaryAssignmentEliminatedSentence tag kind _hr w mode depth parameter n q r V)) := TheoryTransport.sentence (source_originalFormulaBinaryAssignmentEliminated tag kind _hr w mode depth parameter n q r V)

theorem native_originalFormulaBinaryAssignmentEliminated {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinaryAssignmentEliminatedSentence tag kind _hr w mode depth parameter n q r V)) := ZFReplay.replay (originalFormulaBinaryAssignmentEliminated_kernel_certificate tag kind _hr w mode depth parameter n q r V)

def originalFormulaNonbinderAssignmentEliminatedSentence {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) w r V).iff (OriginalFormulaCaseSyntax.unaryCase tag w mode depth parameter n q)))))).close

theorem source_originalFormulaNonbinderAssignmentEliminated {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaNonbinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaArityApplications.nonbinder_iff hZ tag _hr w mode depth parameter n q r V h0 h1 h2

theorem originalFormulaNonbinderAssignmentEliminated_kernel_certificate {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaNonbinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V)) := TheoryTransport.sentence (source_originalFormulaNonbinderAssignmentEliminated tag _hr w mode depth parameter n q r V)

theorem native_originalFormulaNonbinderAssignmentEliminated {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaNonbinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V)) := ZFReplay.replay (originalFormulaNonbinderAssignmentEliminated_kernel_certificate tag _hr w mode depth parameter n q r V)

def originalFormulaBinderAssignmentEliminatedSentence {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) w r V).iff (OriginalFormulaCaseSyntax.binderCase tag w mode depth parameter n q)))))).close

theorem source_originalFormulaBinderAssignmentEliminated {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaBinderApplication.application_iff hZ tag _hr w mode depth parameter n q r V h0 h1 h2

theorem originalFormulaBinderAssignmentEliminated_kernel_certificate {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V)) := TheoryTransport.sentence (source_originalFormulaBinderAssignmentEliminated tag _hr w mode depth parameter n q r V)

theorem native_originalFormulaBinderAssignmentEliminated {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinderAssignmentEliminatedSentence tag _hr w mode depth parameter n q r V)) := ZFReplay.replay (originalFormulaBinderAssignmentEliminated_kernel_certificate tag _hr w mode depth parameter n q r V)

def originalFormulaApplicationAssignmentEliminatedSentence {m} (w mode depth parameter n q r V : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r V).iff (OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q)))))).close

theorem source_originalFormulaApplicationAssignmentEliminated {m} (w mode depth parameter n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaApplicationAssignmentEliminatedSentence w mode depth parameter n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaArityApplications.application_iff hZ w mode depth parameter n q r V h0 h1 h2

theorem originalFormulaApplicationAssignmentEliminated_kernel_certificate {m} (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaApplicationAssignmentEliminatedSentence w mode depth parameter n q r V)) := TheoryTransport.sentence (source_originalFormulaApplicationAssignmentEliminated w mode depth parameter n q r V)

theorem native_originalFormulaApplicationAssignmentEliminated {m} (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaApplicationAssignmentEliminatedSentence w mode depth parameter n q r V)) := ZFReplay.replay (originalFormulaApplicationAssignmentEliminated_kernel_certificate w mode depth parameter n q r V)

def originalFormulaBinderAtActualSuccessorSentence {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V childDepth : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp ((successor childDepth depth).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) w r V).iff (OriginalFormulaCaseSyntax.unaryCase tag w mode childDepth parameter n q))))))).close

theorem source_originalFormulaBinderAtActualSuccessor {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V childDepth : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinderAtActualSuccessorSentence tag _hr w mode depth parameter n q r V childDepth) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor childDepth depth) (Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor childDepth depth) := .hyp (Or.inl rfl)
  exact OriginalFormulaBinderApplication.at_successor_iff hZ tag _hr w mode depth parameter n q r V childDepth h0 h1 h2 h3

theorem originalFormulaBinderAtActualSuccessor_kernel_certificate {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinderAtActualSuccessorSentence tag _hr w mode depth parameter n q r V childDepth)) := TheoryTransport.sentence (source_originalFormulaBinderAtActualSuccessor tag _hr w mode depth parameter n q r V childDepth)

theorem native_originalFormulaBinderAtActualSuccessor {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinderAtActualSuccessorSentence tag _hr w mode depth parameter n q r V childDepth)) := ZFReplay.replay (originalFormulaBinderAtActualSuccessor_kernel_certificate tag _hr w mode depth parameter n q r V childDepth)

def originalFormulaElevenCasesAtTraceValueSentence {m} (three : Bool) (w mode depth parameter n q r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalFormulaTraceEquation.outcomes w mode depth parameter n q))))))).close

theorem source_originalFormulaElevenCasesAtTraceValue {m} (three : Bool) (w mode depth parameter n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaElevenCasesAtTraceValueSentence three w mode depth parameter n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceEquation.at_row_value hZ three w mode depth parameter n q r V h0 h1 h2 h3

theorem originalFormulaElevenCasesAtTraceValue_kernel_certificate {m} (three : Bool) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaElevenCasesAtTraceValueSentence three w mode depth parameter n q r V)) := TheoryTransport.sentence (source_originalFormulaElevenCasesAtTraceValue three w mode depth parameter n q r V)

theorem native_originalFormulaElevenCasesAtTraceValue {m} (three : Bool) (w mode depth parameter n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaElevenCasesAtTraceValueSentence three w mode depth parameter n q r V)) := ZFReplay.replay (originalFormulaElevenCasesAtTraceValue_kernel_certificate three w mode depth parameter n q r V)

def originalFormulaElevenCasesAtRowSentence {m} (three : Bool) (w mode depth parameter n q r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTransformRowSyntax.row 3 w mode depth parameter n q r).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalFormulaTraceEquation.outcomes w mode depth parameter n q)))))).close

theorem source_originalFormulaElevenCasesAtRow {m} (three : Bool) (w mode depth parameter n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaElevenCasesAtRowSentence three w mode depth parameter n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceEquation.at_row hZ three w mode depth parameter n q r h0 h1 h2

theorem originalFormulaElevenCasesAtRow_kernel_certificate {m} (three : Bool) (w mode depth parameter n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaElevenCasesAtRowSentence three w mode depth parameter n q r)) := TheoryTransport.sentence (source_originalFormulaElevenCasesAtRow three w mode depth parameter n q r)

theorem native_originalFormulaElevenCasesAtRow {m} (three : Bool) (w mode depth parameter n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaElevenCasesAtRowSentence three w mode depth parameter n q r)) := ZFReplay.replay (originalFormulaElevenCasesAtRow_kernel_certificate three w mode depth parameter n q r)

def originalFormulaElevenCasesInputOutputNaturalSentence {m} (w mode depth parameter n q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).imp (((Formula.mem n w).conj (.mem q w))))).close

theorem source_originalFormulaElevenCasesInputOutputNatural {m} (w mode depth parameter n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaElevenCasesInputOutputNaturalSentence w mode depth parameter n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaTraceEquation.outcomes w mode depth parameter n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalFormulaTraceEquation.outcomes w mode depth parameter n q) := .hyp (Or.inl rfl)
  exact OriginalFormulaOutcomesNaturality.outcomes_natural hZ w mode depth parameter n q h0 h1

theorem originalFormulaElevenCasesInputOutputNatural_kernel_certificate {m} (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaElevenCasesInputOutputNaturalSentence w mode depth parameter n q)) := TheoryTransport.sentence (source_originalFormulaElevenCasesInputOutputNatural w mode depth parameter n q)

theorem native_originalFormulaElevenCasesInputOutputNatural {m} (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaElevenCasesInputOutputNaturalSentence w mode depth parameter n q)) := ZFReplay.replay (originalFormulaElevenCasesInputOutputNatural_kernel_certificate w mode depth parameter n q)

def originalFormulaWholeRunElevenCasesSentence {m} (three : Bool) (w mode depth parameter n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaTraceEquation.outcomes w mode depth parameter n q))))))).close

theorem source_originalFormulaWholeRunElevenCases {m} (three : Bool) (w mode depth parameter n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaWholeRunElevenCasesSentence three w mode depth parameter n q) := by
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
  exact OriginalFormulaRunEquation.run_iff hZ three w mode depth parameter n q h0 h1 h2 h3

theorem originalFormulaWholeRunElevenCases_kernel_certificate {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaWholeRunElevenCasesSentence three w mode depth parameter n q)) := TheoryTransport.sentence (source_originalFormulaWholeRunElevenCases three w mode depth parameter n q)

theorem native_originalFormulaWholeRunElevenCases {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaWholeRunElevenCasesSentence three w mode depth parameter n q)) := ZFReplay.replay (originalFormulaWholeRunElevenCases_kernel_certificate three w mode depth parameter n q)

end PPAC.Migration.Internal.ObjectOriginalFormulaEquation
