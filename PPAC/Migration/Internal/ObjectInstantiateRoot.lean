import PPAC.Migration.Internal.InstantiateClosedParameterRename
import PPAC.Migration.Internal.InstantiateVariableSpecialization
import PPAC.Migration.Internal.InstantiateTopTermOperation

/-! 实际mode2根环境、闭参数binder重命名及真实零深度项操作的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectInstantiateRoot
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeTwoClosedParameterBinderRenameIffSentence {m} (w U V c e C P q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w e V).imp ((InstantiateOperationFrameSyntax.closedParameter w e P).imp (((SyntaxRenameTermSyntax.renamed w U V c e C e P q).iff (.equal q P))))))).close

theorem source_modeTwoClosedParameterBinderRenameIff {m} (w U V c e C P q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoClosedParameterBinderRenameIffSentence w U V c e C P q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InstantiateOperationFrameSyntax.closedParameter w e P) (Context.add (SyntaxIdentityMapSyntax.identityMap w e V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w e V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (InstantiateOperationFrameSyntax.closedParameter w e P) := .hyp (Or.inl rfl)
  exact InstantiateClosedParameterRename.closed_iff hZ w U V c e C P q h0 h1 h2 h3

theorem modeTwoClosedParameterBinderRenameIff_kernel_certificate {m} (w U V c e C P q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoClosedParameterBinderRenameIffSentence w U V c e C P q)) := TheoryTransport.sentence (source_modeTwoClosedParameterBinderRenameIff w U V c e C P q)

theorem native_modeTwoClosedParameterBinderRenameIff {m} (w U V c e C P q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoClosedParameterBinderRenameIffSentence w U V c e C P q)) := ZFReplay.replay (modeTwoClosedParameterBinderRenameIff_kernel_certificate w U V c e C P q)

def modeTwoVariableAtPointIffSentence {m} (w d P i x y : Fin m) : Source.Sentence := ((Formula.equal i d).imp (((InstantiateVariableValueSyntax.boundValue w d P i x y).iff (.equal y P)))).close

theorem source_modeTwoVariableAtPointIff {m} (w d P i x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoVariableAtPointIffSentence w d P i x y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.equal i d) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (Formula.equal i d) := .hyp (Or.inl rfl)
  exact InstantiateVariableSpecialization.at_point_iff hZ w d P i x y h0

theorem modeTwoVariableAtPointIff_kernel_certificate {m} (w d P i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoVariableAtPointIffSentence w d P i x y)) := TheoryTransport.sentence (source_modeTwoVariableAtPointIff w d P i x y)

theorem native_modeTwoVariableAtPointIff {m} (w d P i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoVariableAtPointIffSentence w d P i x y)) := ZFReplay.replay (modeTwoVariableAtPointIff_kernel_certificate w d P i x y)

def modeTwoVariableBelowIffSentence {m} (w d P i x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((Formula.mem i d).imp (((InstantiateVariableValueSyntax.boundValue w d P i x y).iff (.equal y x)))))).close

theorem source_modeTwoVariableBelowIff {m} (w d P i x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoVariableBelowIffSentence w d P i x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i d) := .hyp (Or.inl rfl)
  exact InstantiateVariableSpecialization.below_iff hZ w d P i x y h0 h1 h2

theorem modeTwoVariableBelowIff_kernel_certificate {m} (w d P i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoVariableBelowIffSentence w d P i x y)) := TheoryTransport.sentence (source_modeTwoVariableBelowIff w d P i x y)

theorem native_modeTwoVariableBelowIff {m} (w d P i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoVariableBelowIffSentence w d P i x y)) := ZFReplay.replay (modeTwoVariableBelowIff_kernel_certificate w d P i x y)

def modeTwoActualRootVariableFieldIffSentence {m} (bound : Bool) (w z b A P R S i n q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((Formula.mem i (SyntaxTermSyntax.limit bound A b)).imp ((SyntaxVariableSyntax.code bound w i n).imp (((InstantiateVariableValueSyntax.valueSpec bound w z P i n q).iff (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q)))))))).close

theorem source_modeTwoActualRootVariableFieldIff {m} (bound : Bool) (w z b A P R S i n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootVariableFieldIffSentence bound w z b A P R S i n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (Formula.mem i (SyntaxTermSyntax.limit bound A b)) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem i (SyntaxTermSyntax.limit bound A b)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact InstantiateOperationFrameRoot.numeric_field_iff hZ bound w z b A P R S i n q h0 h1 h2 h3 h4

theorem modeTwoActualRootVariableFieldIff_kernel_certificate {m} (bound : Bool) (w z b A P R S i n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootVariableFieldIffSentence bound w z b A P R S i n q)) := TheoryTransport.sentence (source_modeTwoActualRootVariableFieldIff bound w z b A P R S i n q)

theorem native_modeTwoActualRootVariableFieldIff {m} (bound : Bool) (w z b A P R S i n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootVariableFieldIffSentence bound w z b A P R S i n q)) := ZFReplay.replay (modeTwoActualRootVariableFieldIff_kernel_certificate bound w z b A P R S i n q)

def modeTwoActualRootVariableCompatibilitySentence {m} (bound : Bool) (w z b A P R S : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((InstantiateOperationFrameSyntax.compatible bound w z P A b R S))))).close

theorem source_modeTwoActualRootVariableCompatibility {m} (bound : Bool) (w z b A P R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootVariableCompatibilitySentence bound w z b A P R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inl rfl)
  exact InstantiateOperationFrameRoot.compatible_from_actual hZ bound w z b A P R S h0 h1 h2

theorem modeTwoActualRootVariableCompatibility_kernel_certificate {m} (bound : Bool) (w z b A P R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootVariableCompatibilitySentence bound w z b A P R S)) := TheoryTransport.sentence (source_modeTwoActualRootVariableCompatibility bound w z b A P R S)

theorem native_modeTwoActualRootVariableCompatibility {m} (bound : Bool) (w z b A P R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootVariableCompatibilitySentence bound w z b A P R S)) := ZFReplay.replay (modeTwoActualRootVariableCompatibility_kernel_certificate bound w z b A P R S)

def modeTwoActualRootFrameSentence {m} (w mode z P b A R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((InstantiateOperationFrameSyntax.frame w mode z P A b z b R S)))))).close

theorem source_modeTwoActualRootFrame {m} (w mode z P b A R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootFrameSentence w mode z P b A R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inl rfl)
  exact InstantiateOperationFrameRoot.from_actual_input hZ w mode z P b A R S h0 h1 h2 h3

theorem modeTwoActualRootFrame_kernel_certificate {m} (w mode z P b A R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootFrameSentence w mode z P b A R S)) := TheoryTransport.sentence (source_modeTwoActualRootFrame w mode z P b A R S)

theorem native_modeTwoActualRootFrame {m} (w mode z P b A R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootFrameSentence w mode z P b A R S)) := ZFReplay.replay (modeTwoActualRootFrame_kernel_certificate w mode z P b A R S)

def modeTwoActualRootTermProgramIffSentence {m} (w mode z P b A R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((SyntaxTermSyntax.term w A b n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)))))))).close

theorem source_modeTwoActualRootTermProgramIff {m} (w mode z P b A R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootTermProgramIffSentence w mode z P b A R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w A b n) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTermSyntax.term w A b n) := .hyp (Or.inl rfl)
  exact InstantiateTopTermOperation.program_iff hZ w mode z P b A R S n q h0 h1 h2 h3 h4

theorem modeTwoActualRootTermProgramIff_kernel_certificate {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootTermProgramIffSentence w mode z P b A R S n q)) := TheoryTransport.sentence (source_modeTwoActualRootTermProgramIff w mode z P b A R S n q)

theorem native_modeTwoActualRootTermProgramIff {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootTermProgramIffSentence w mode z P b A R S n q)) := ZFReplay.replay (modeTwoActualRootTermProgramIff_kernel_certificate w mode z P b A R S n q)

def modeTwoActualRootTermCodedIffSentence {m} (w mode z P b A R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((SyntaxTermSyntax.term w A b n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S A b z b n q)))))))).close

theorem source_modeTwoActualRootTermCodedIff {m} (w mode z P b A R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootTermCodedIffSentence w mode z P b A R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w A b n) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTermSyntax.term w A b n) := .hyp (Or.inl rfl)
  exact InstantiateTopTermOperation.coded_iff hZ w mode z P b A R S n q h0 h1 h2 h3 h4

theorem modeTwoActualRootTermCodedIff_kernel_certificate {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootTermCodedIffSentence w mode z P b A R S n q)) := TheoryTransport.sentence (source_modeTwoActualRootTermCodedIff w mode z P b A R S n q)

theorem native_modeTwoActualRootTermCodedIff {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootTermCodedIffSentence w mode z P b A R S n q)) := ZFReplay.replay (modeTwoActualRootTermCodedIff_kernel_certificate w mode z P b A R S n q)

def modeTwoActualRootGuardedTermCodedIffSentence {m} (w mode z P b A R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((((SyntaxTermSyntax.term w A b n).conj (OriginalTransformRowSyntax.run 1 w mode z P n q)).iff (SyntaxCodedMixedTermSyntax.substituted w R S A b z b n q))))))).close

theorem source_modeTwoActualRootGuardedTermCodedIff {m} (w mode z P b A R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootGuardedTermCodedIffSentence w mode z P b A R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inl rfl)
  exact InstantiateTopTermOperation.guarded_coded_iff hZ w mode z P b A R S n q h0 h1 h2 h3

theorem modeTwoActualRootGuardedTermCodedIff_kernel_certificate {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootGuardedTermCodedIffSentence w mode z P b A R S n q)) := TheoryTransport.sentence (source_modeTwoActualRootGuardedTermCodedIff w mode z P b A R S n q)

theorem native_modeTwoActualRootGuardedTermCodedIff {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootGuardedTermCodedIffSentence w mode z P b A R S n q)) := ZFReplay.replay (modeTwoActualRootGuardedTermCodedIff_kernel_certificate w mode z P b A R S n q)

end PPAC.Migration.Internal.ObjectInstantiateRoot
