import PPAC.Migration.Internal.AbstractTopTermOperation

/-! 原mode1零深度纯项运行与实际首槽抽象码表及操作的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectAbstractTopTerm
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeOneBoundAtZeroDepthIffSentence {m} (w z i j x y : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((Formula.mem i w).imp ((successor j i).imp (((AbstractVariableValueSyntax.boundValue w z i x y).iff (SyntaxVariableSyntax.code true w j y))))))).close

theorem source_modeOneBoundAtZeroDepthIff {m} (w z i j x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundAtZeroDepthIffSentence w z i j x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (Formula.mem i w) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact AbstractVariableSpecialization.bound_zero_iff hZ w z i j x y h0 h1 h2 h3

theorem modeOneBoundAtZeroDepthIff_kernel_certificate {m} (w z i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundAtZeroDepthIffSentence w z i j x y)) := TheoryTransport.sentence (source_modeOneBoundAtZeroDepthIff w z i j x y)

theorem native_modeOneBoundAtZeroDepthIff {m} (w z i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundAtZeroDepthIffSentence w z i j x y)) := ZFReplay.replay (modeOneBoundAtZeroDepthIff_kernel_certificate w z i j x y)

def modeOneFreeAtZeroIndexIffSentence {m} (w d i y : Fin m) : Source.Sentence := ((empty i).imp (((AbstractVariableValueSyntax.freeValue w d i y).iff (SyntaxVariableSyntax.code true w d y)))).close

theorem source_modeOneFreeAtZeroIndexIff {m} (w d i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeAtZeroIndexIffSentence w d i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact AbstractVariableSpecialization.free_zero_iff w d i y h0

theorem modeOneFreeAtZeroIndexIff_kernel_certificate {m} (w d i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeAtZeroIndexIffSentence w d i y)) := TheoryTransport.sentence (source_modeOneFreeAtZeroIndexIff w d i y)

theorem native_modeOneFreeAtZeroIndexIff {m} (w d i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeAtZeroIndexIffSentence w d i y)) := ZFReplay.replay (modeOneFreeAtZeroIndexIff_kernel_certificate w d i y)

def modeOneFreeAtSuccessorIndexIffSentence {m} (w d i k y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem k w).imp ((successor i k).imp (((AbstractVariableValueSyntax.freeValue w d i y).iff (SyntaxVariableSyntax.code false w k y)))))).close

theorem source_modeOneFreeAtSuccessorIndexIff {m} (w d i k y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeAtSuccessorIndexIffSentence w d i k y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i k) (Context.add (Formula.mem k w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor i k) := .hyp (Or.inl rfl)
  exact AbstractVariableSpecialization.free_successor_iff hZ w d i k y h0 h1 h2

theorem modeOneFreeAtSuccessorIndexIff_kernel_certificate {m} (w d i k y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeAtSuccessorIndexIffSentence w d i k y)) := TheoryTransport.sentence (source_modeOneFreeAtSuccessorIndexIff w d i k y)

theorem native_modeOneFreeAtSuccessorIndexIff {m} (w d i k y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeAtSuccessorIndexIffSentence w d i k y)) := ZFReplay.replay (modeOneFreeAtSuccessorIndexIff_kernel_certificate w d i k y)

def modeOneBoundBelowDepthIffSentence {m} (w d i x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((Formula.mem i d).imp (((AbstractVariableValueSyntax.boundValue w d i x y).iff (Formula.equal y x)))))).close

theorem source_modeOneBoundBelowDepthIff {m} (w d i x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundBelowDepthIffSentence w d i x y) := by
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
  exact AbstractVariableSpecialization.bound_below_iff hZ w d i x y h0 h1 h2

theorem modeOneBoundBelowDepthIff_kernel_certificate {m} (w d i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundBelowDepthIffSentence w d i x y)) := TheoryTransport.sentence (source_modeOneBoundBelowDepthIff w d i x y)

theorem native_modeOneBoundBelowDepthIff {m} (w d i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundBelowDepthIffSentence w d i x y)) := ZFReplay.replay (modeOneBoundBelowDepthIff_kernel_certificate w d i x y)

def modeOneActualBoundTableAtSuccessorIffSentence {m} (w z a b A B R S i j x y : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem i a).imp ((successor j i).imp (((AbstractVariableValueSyntax.boundValue w z i x y).iff (StructuralListFieldSyntax.field w R i y)))))))).close

theorem source_modeOneActualBoundTableAtSuccessorIff {m} (w z a b A B R S i j x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualBoundTableAtSuccessorIffSentence w z a b A B R S i j x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (Formula.mem i a) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact AbstractTopVariablePoint.bound_at_successor hZ w z a b A B R S i j x y h0 h1 h2 h3 h4

theorem modeOneActualBoundTableAtSuccessorIff_kernel_certificate {m} (w z a b A B R S i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualBoundTableAtSuccessorIffSentence w z a b A B R S i j x y)) := TheoryTransport.sentence (source_modeOneActualBoundTableAtSuccessorIff w z a b A B R S i j x y)

theorem native_modeOneActualBoundTableAtSuccessorIff {m} (w z a b A B R S i j x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualBoundTableAtSuccessorIffSentence w z a b A B R S i j x y)) := ZFReplay.replay (modeOneActualBoundTableAtSuccessorIff_kernel_certificate w z a b A B R S i j x y)

def modeOneActualFreeTableAtZeroIffSentence {m} (w z a b A B R S i y : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem i B).imp ((empty i).imp (((AbstractVariableValueSyntax.freeValue w z i y).iff (StructuralListFieldSyntax.field w S i y)))))))).close

theorem source_modeOneActualFreeTableAtZeroIff {m} (w z a b A B R S i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualFreeTableAtZeroIffSentence w z a b A B R S i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (Formula.mem i B) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem i B) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact AbstractTopVariablePoint.free_at_zero hZ w z a b A B R S i y h0 h1 h2 h3 h4

theorem modeOneActualFreeTableAtZeroIff_kernel_certificate {m} (w z a b A B R S i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualFreeTableAtZeroIffSentence w z a b A B R S i y)) := TheoryTransport.sentence (source_modeOneActualFreeTableAtZeroIff w z a b A B R S i y)

theorem native_modeOneActualFreeTableAtZeroIff {m} (w z a b A B R S i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualFreeTableAtZeroIffSentence w z a b A B R S i y)) := ZFReplay.replay (modeOneActualFreeTableAtZeroIff_kernel_certificate w z a b A B R S i y)

def modeOneActualFreeTableAtSuccessorIffSentence {m} (w z a b A B R S i j y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem i B).imp ((successor i j).imp (((AbstractVariableValueSyntax.freeValue w z i y).iff (StructuralListFieldSyntax.field w S i y))))))).close

theorem source_modeOneActualFreeTableAtSuccessorIff {m} (w z a b A B R S i j y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualFreeTableAtSuccessorIffSentence w z a b A B R S i j y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem i B) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact AbstractTopVariablePoint.free_at_successor hZ w z a b A B R S i j y h0 h1 h2 h3

theorem modeOneActualFreeTableAtSuccessorIff_kernel_certificate {m} (w z a b A B R S i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualFreeTableAtSuccessorIffSentence w z a b A B R S i j y)) := TheoryTransport.sentence (source_modeOneActualFreeTableAtSuccessorIff w z a b A B R S i j y)

theorem native_modeOneActualFreeTableAtSuccessorIff {m} (w z a b A B R S i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualFreeTableAtSuccessorIffSentence w z a b A B R S i j y)) := ZFReplay.replay (modeOneActualFreeTableAtSuccessorIff_kernel_certificate w z a b A B R S i j y)

def modeOneZeroDepthActualVariableTableIffSentence {m} (bound : Bool) (w z a b A B R S i n q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem i (SyntaxTermSyntax.limit bound a B)).imp (((AbstractVariableValueSyntax.valueSpec bound w z i n q).iff (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q))))))).close

theorem source_modeOneZeroDepthActualVariableTableIff {m} (bound : Bool) (w z a b A B R S i n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthActualVariableTableIffSentence bound w z a b A B R S i n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i (SyntaxTermSyntax.limit bound a B)) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem i (SyntaxTermSyntax.limit bound a B)) := .hyp (Or.inl rfl)
  exact AbstractTopVariable.numeric_field_iff hZ bound w z a b A B R S i n q h0 h1 h2 h3

theorem modeOneZeroDepthActualVariableTableIff_kernel_certificate {m} (bound : Bool) (w z a b A B R S i n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthActualVariableTableIffSentence bound w z a b A B R S i n q)) := TheoryTransport.sentence (source_modeOneZeroDepthActualVariableTableIff bound w z a b A B R S i n q)

theorem native_modeOneZeroDepthActualVariableTableIff {m} (bound : Bool) (w z a b A B R S i n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthActualVariableTableIffSentence bound w z a b A B R S i n q)) := ZFReplay.replay (modeOneZeroDepthActualVariableTableIff_kernel_certificate bound w z a b A B R S i n q)

def modeOneZeroDepthActualVariableProgramIffSentence {m} (bound : Bool) (w mode z P a b A B R S n q i : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((Formula.mem i (SyntaxTermSyntax.limit bound a B)).imp ((SyntaxVariableSyntax.code bound w i n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)))))))))).close

theorem source_modeOneZeroDepthActualVariableProgramIff {m} (bound : Bool) (w mode z P a b A B R S n q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthActualVariableProgramIffSentence bound w mode z P a b A B R S n q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (Formula.mem i (SyntaxTermSyntax.limit bound a B)) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (Formula.mem i (SyntaxTermSyntax.limit bound a B)) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact AbstractTopVariable.program_at_variable hZ bound w mode z P a b A B R S n q i h0 h1 h2 h3 h4 h5 h6

theorem modeOneZeroDepthActualVariableProgramIff_kernel_certificate {m} (bound : Bool) (w mode z P a b A B R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthActualVariableProgramIffSentence bound w mode z P a b A B R S n q i)) := TheoryTransport.sentence (source_modeOneZeroDepthActualVariableProgramIff bound w mode z P a b A B R S n q i)

theorem native_modeOneZeroDepthActualVariableProgramIff {m} (bound : Bool) (w mode z P a b A B R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthActualVariableProgramIffSentence bound w mode z P a b A B R S n q i)) := ZFReplay.replay (modeOneZeroDepthActualVariableProgramIff_kernel_certificate bound w mode z P a b A B R S n q i)

def modeOneZeroDepthActualPureTermProgramIffSentence {m} (w mode z P a b A B R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTermSyntax.term w a B n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q))))))))).close

theorem source_modeOneZeroDepthActualPureTermProgramIff {m} (w mode z P a b A B R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthActualPureTermProgramIffSentence w mode z P a b A B R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxTermSyntax.term w a B n) := .hyp (Or.inl rfl)
  exact AbstractTopTerm.program_iff hZ w mode z P a b A B R S n q h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthActualPureTermProgramIff_kernel_certificate {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthActualPureTermProgramIffSentence w mode z P a b A B R S n q)) := TheoryTransport.sentence (source_modeOneZeroDepthActualPureTermProgramIff w mode z P a b A B R S n q)

theorem native_modeOneZeroDepthActualPureTermProgramIff {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthActualPureTermProgramIffSentence w mode z P a b A B R S n q)) := ZFReplay.replay (modeOneZeroDepthActualPureTermProgramIff_kernel_certificate w mode z P a b A B R S n q)

def modeOneZeroDepthActualCodedPureTermIffSentence {m} (w mode z P a b A B R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTermSyntax.term w a B n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a B A b n q))))))))).close

theorem source_modeOneZeroDepthActualCodedPureTermIff {m} (w mode z P a b A B R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthActualCodedPureTermIffSentence w mode z P a b A B R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxTermSyntax.term w a B n) := .hyp (Or.inl rfl)
  exact AbstractTopTerm.coded_iff hZ w mode z P a b A B R S n q h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthActualCodedPureTermIff_kernel_certificate {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthActualCodedPureTermIffSentence w mode z P a b A B R S n q)) := TheoryTransport.sentence (source_modeOneZeroDepthActualCodedPureTermIff w mode z P a b A B R S n q)

theorem native_modeOneZeroDepthActualCodedPureTermIff {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthActualCodedPureTermIffSentence w mode z P a b A B R S n q)) := ZFReplay.replay (modeOneZeroDepthActualCodedPureTermIff_kernel_certificate w mode z P a b A B R S n q)

def modeOneZeroDepthPureTermAtActualCodesIffSentence {m} (w mode z P a b A B R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTermSyntax.term w a B n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (AbstractTopTermSyntax.abstracted w a b A B n q))))))))).close

theorem source_modeOneZeroDepthPureTermAtActualCodesIff {m} (w mode z P a b A B R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthPureTermAtActualCodesIffSentence w mode z P a b A B R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxTermSyntax.term w a B n) := .hyp (Or.inl rfl)
  exact AbstractTopTermOperation.at_codes_iff hZ w mode z P a b A B R S n q h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthPureTermAtActualCodesIff_kernel_certificate {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthPureTermAtActualCodesIffSentence w mode z P a b A B R S n q)) := TheoryTransport.sentence (source_modeOneZeroDepthPureTermAtActualCodesIff w mode z P a b A B R S n q)

theorem native_modeOneZeroDepthPureTermAtActualCodesIff {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthPureTermAtActualCodesIffSentence w mode z P a b A B R S n q)) := ZFReplay.replay (modeOneZeroDepthPureTermAtActualCodesIff_kernel_certificate w mode z P a b A B R S n q)

def modeOneZeroDepthPureTermActualOperationIffSentence {m} (w mode z P a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((SyntaxTermSyntax.term w a B n).imp (((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (AbstractTopTermSyntax.abstracted w a b A B n q))))))))).close

theorem source_modeOneZeroDepthPureTermActualOperationIff {m} (w mode z P a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthPureTermActualOperationIffSentence w mode z P a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a B n) (Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxTermSyntax.term w a B n) := .hyp (Or.inl rfl)
  exact AbstractTopTermOperation.run_iff hZ w mode z P a b A B n q h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthPureTermActualOperationIff_kernel_certificate {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthPureTermActualOperationIffSentence w mode z P a b A B n q)) := TheoryTransport.sentence (source_modeOneZeroDepthPureTermActualOperationIff w mode z P a b A B n q)

theorem native_modeOneZeroDepthPureTermActualOperationIff {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthPureTermActualOperationIffSentence w mode z P a b A B n q)) := ZFReplay.replay (modeOneZeroDepthPureTermActualOperationIff_kernel_certificate w mode z P a b A B n q)

def actualAbstractPureTermSourceTypeSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((AbstractTopTermSyntax.abstracted w a b A B n q).imp ((SyntaxTermSyntax.term w a B n))).close

theorem source_actualAbstractPureTermSourceType {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualAbstractPureTermSourceTypeSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractTopTermSyntax.abstracted w a b A B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (AbstractTopTermSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact AbstractTopTermOperation.source_type w a b A B n q h0

theorem actualAbstractPureTermSourceType_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualAbstractPureTermSourceTypeSentence w a b A B n q)) := TheoryTransport.sentence (source_actualAbstractPureTermSourceType w a b A B n q)

theorem native_actualAbstractPureTermSourceType {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualAbstractPureTermSourceTypeSentence w a b A B n q)) := ZFReplay.replay (actualAbstractPureTermSourceType_kernel_certificate w a b A B n q)

def modeOneZeroDepthGuardedPureTermActualOperationIffSentence {m} (w mode z P a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((((SyntaxTermSyntax.term w a B n).conj (OriginalTransformRowSyntax.run 1 w mode z P n q)).iff (AbstractTopTermSyntax.abstracted w a b A B n q)))))))).close

theorem source_modeOneZeroDepthGuardedPureTermActualOperationIff {m} (w mode z P a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthGuardedPureTermActualOperationIffSentence w mode z P a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inl rfl)
  exact AbstractTopTermOperation.guarded_iff hZ w mode z P a b A B n q h0 h1 h2 h3 h4

theorem modeOneZeroDepthGuardedPureTermActualOperationIff_kernel_certificate {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthGuardedPureTermActualOperationIffSentence w mode z P a b A B n q)) := TheoryTransport.sentence (source_modeOneZeroDepthGuardedPureTermActualOperationIff w mode z P a b A B n q)

theorem native_modeOneZeroDepthGuardedPureTermActualOperationIff {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthGuardedPureTermActualOperationIffSentence w mode z P a b A B n q)) := ZFReplay.replay (modeOneZeroDepthGuardedPureTermActualOperationIff_kernel_certificate w mode z P a b A B n q)

end PPAC.Migration.Internal.ObjectAbstractTopTerm
