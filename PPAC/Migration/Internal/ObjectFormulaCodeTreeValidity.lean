import PPAC.Migration.Internal.FormulaCodeTypedDataForward

/-! 原树有效性全内部成员归纳及实际唯一TypedData正向解码的原nativeZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax
open SyntaxForestFields (graphLaw)
open SyntaxTreeValiditySyntax StructuralTreeValiditySyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeTreeValiditySyntax
open FormulaCodeTypedDataSyntax (typedData)
open StructuralTreeOperatorSyntax (shape)

def graphChildrenSentence {m} (k : Nat) (xs : Fin k → Fin m) (w g : Fin m) : Source.Sentence := ((graphLaw k xs g).imp ((validInputs k w xs).imp ((validChildren w g)))).close

theorem source_graphChildren {m} (k : Nat) (xs : Fin k → Fin m) (w g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphChildrenSentence k xs w g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (validInputs k w xs) (Context.add (graphLaw k xs g) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (graphLaw k xs g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (validInputs k w xs) := .hyp (Or.inl rfl)
  exact SyntaxTreeValidity.graph_children k w xs g h0 h1

theorem graphChildren_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphChildrenSentence k xs w g)) := TheoryTransport.sentence (source_graphChildren k xs w g)

theorem native_graphChildren {m} (k : Nat) (xs : Fin k → Fin m) (w g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphChildrenSentence k xs w g)) := ZFReplay.replay (graphChildren_kernel_certificate k xs w g)

def nodeSentence {m} (k : Nat) (xs : Fin k → Fin m) (w a n : Fin m) : Source.Sentence := ((omega w).imp ((node k w a xs n).imp ((validInputs k w xs).imp ((valid w n))))).close

theorem source_node {m} (k : Nat) (xs : Fin k → Fin m) (w a n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nodeSentence k xs w a n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (validInputs k w xs) (Context.add (node k w a xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (node k w a xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (validInputs k w xs) := .hyp (Or.inl rfl)
  exact SyntaxTreeValidity.node hZ k w a xs n h0 h1 h2

theorem node_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeSentence k xs w a n)) := TheoryTransport.sentence (source_node k xs w a n)

theorem native_node {m} (k : Nat) (xs : Fin k → Fin m) (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeSentence k xs w a n)) := ZFReplay.replay (node_kernel_certificate k xs w a n)

def constructorSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((validInputs k w xs).imp ((valid w n))))).close

theorem source_constructor {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorSentence k tag xs w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (validInputs k w xs) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (validInputs k w xs) := .hyp (Or.inl rfl)
  exact SyntaxTreeValidity.constructor hZ k tag w xs n h0 h1 h2

theorem constructor_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorSentence k tag xs w n)) := TheoryTransport.sentence (source_constructor k tag xs w n)

theorem native_constructor {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorSentence k tag xs w n)) := ZFReplay.replay (constructor_kernel_certificate k tag xs w n)

def scalarSentence {m} (w i n : Fin m) : Source.Sentence := ((omega w).imp ((scalar w i n).imp ((valid w n)))).close

theorem source_scalar {m} (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (scalarSentence w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (scalar w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (scalar w i n) := .hyp (Or.inl rfl)
  exact SyntaxTreeValidity.scalar hZ w i n h0 h1

theorem scalar_kernel_certificate {m} (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (scalarSentence w i n)) := TheoryTransport.sentence (source_scalar w i n)

theorem native_scalar {m} (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (scalarSentence w i n)) := ZFReplay.replay (scalar_kernel_certificate w i n)

def variableSentence {m} (bound : Bool) (w i n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxVariableSyntax.code bound w i n).imp ((valid w n)))).close

theorem source_variable {m} (bound : Bool) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableSentence bound w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact SyntaxTermTreeValidity.variable_code hZ bound w i n h0 h1

theorem variable_kernel_certificate {m} (bound : Bool) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableSentence bound w i n)) := TheoryTransport.sentence (source_variable bound w i n)

theorem native_variable {m} (bound : Bool) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableSentence bound w i n)) := ZFReplay.replay (variable_kernel_certificate bound w i n)

def termBranchSentence {m} (bound : Bool) (w l n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.branch bound w l n).imp ((valid w n)))).close

theorem source_termBranch {m} (bound : Bool) (w l n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termBranchSentence bound w l n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.branch bound w l n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.branch bound w l n) := .hyp (Or.inl rfl)
  exact SyntaxTermTreeValidity.branch hZ bound w l n h0 h1

theorem termBranch_kernel_certificate {m} (bound : Bool) (w l n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termBranchSentence bound w l n)) := TheoryTransport.sentence (source_termBranch bound w l n)

theorem native_termBranch {m} (bound : Bool) (w l n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termBranchSentence bound w l n)) := ZFReplay.replay (termBranch_kernel_certificate bound w l n)

def termSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((term w b f n).imp ((valid w n)))).close

theorem source_term {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (term w b f n) := .hyp (Or.inl rfl)
  exact SyntaxTermTreeValidity.term hZ w b f n h0 h1

theorem term_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termSentence w b f n)) := TheoryTransport.sentence (source_term w b f n)

theorem native_term {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termSentence w b f n)) := ZFReplay.replay (term_kernel_certificate w b f n)

def nullarySentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.nullary truth w b f n).imp ((valid w n)))).close

theorem source_nullary {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullarySentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.nullary truth w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.nullary truth w b f n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTreeValidity.nullary hZ truth w b f n h0 h1

theorem nullary_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullarySentence truth w b f n)) := TheoryTransport.sentence (source_nullary truth w b f n)

theorem native_nullary {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullarySentence truth w b f n)) := ZFReplay.replay (nullary_kernel_certificate truth w b f n)

def memberSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.membership w b f n).imp ((valid w n)))).close

theorem source_member {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.membership w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.membership w b f n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTreeValidity.membership hZ w b f n h0 h1

theorem member_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberSentence w b f n)) := TheoryTransport.sentence (source_member w b f n)

theorem native_member {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberSentence w b f n)) := ZFReplay.replay (member_kernel_certificate w b f n)

def equalSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.equality w b f n).imp ((valid w n)))).close

theorem source_equal {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equality w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.equality w b f n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTreeValidity.equality hZ w b f n h0 h1

theorem equal_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalSentence w b f n)) := TheoryTransport.sentence (source_equal w b f n)

theorem native_equal {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalSentence w b f n)) := ZFReplay.replay (equal_kernel_certificate w b f n)

def atomicSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.atomic w b f n).imp ((valid w n)))).close

theorem source_atomic {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.atomic w b f n) := .hyp (Or.inl rfl)
  exact SyntaxAtomTreeValidity.atomic hZ w b f n h0 h1

theorem atomic_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicSentence w b f n)) := TheoryTransport.sentence (source_atomic w b f n)

theorem native_atomic {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicSentence w b f n)) := ZFReplay.replay (atomic_kernel_certificate w b f n)

def advancedChildSentence {m} (w n x b f : Fin m) : Source.Sentence := ((earlier w n).imp ((Formula.mem x n).imp ((advancedCode w x b f).imp ((valid w x))))).close

theorem source_advancedChild {m} (w n x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedChildSentence w n x b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (advancedCode w x b f) (Context.add (Formula.mem x n) (Context.add (earlier w n) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (advancedCode w x b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidityCases.advanced_child w n x b f h0 h1 h2

theorem advancedChild_kernel_certificate {m} (w n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedChildSentence w n x b f)) := TheoryTransport.sentence (source_advancedChild w n x b f)

theorem native_advancedChild {m} (w n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedChildSentence w n x b f)) := ZFReplay.replay (advancedChild_kernel_certificate w n x b f)

def singleCaseSentence {m} (tag : Nat) (advance : Bool) (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((earlier w n).imp ((singleCase tag advance w b f n).imp ((valid w n))))).close

theorem source_singleCase {m} (tag : Nat) (advance : Bool) (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleCaseSentence tag advance w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCase tag advance w b f n) (Context.add (earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (singleCase tag advance w b f n) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidityCases.single hZ tag advance w n b f h0 h1 h2

theorem singleCase_kernel_certificate {m} (tag : Nat) (advance : Bool) (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleCaseSentence tag advance w n b f)) := TheoryTransport.sentence (source_singleCase tag advance w n b f)

theorem native_singleCase {m} (tag : Nat) (advance : Bool) (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleCaseSentence tag advance w n b f)) := ZFReplay.replay (singleCase_kernel_certificate tag advance w n b f)

def binaryCaseSentence {m} (kind : Fin 4) (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((earlier w n).imp ((binaryCase kind w b f n).imp ((valid w n))))).close

theorem source_binaryCase {m} (kind : Fin 4) (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryCaseSentence kind w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCase kind w b f n) (Context.add (earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (binaryCase kind w b f n) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidityCases.binary hZ kind w n b f h0 h1 h2

theorem binaryCase_kernel_certificate {m} (kind : Fin 4) (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryCaseSentence kind w n b f)) := TheoryTransport.sentence (source_binaryCase kind w n b f)

theorem native_binaryCase {m} (kind : Fin 4) (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryCaseSentence kind w n b f)) := ZFReplay.replay (binaryCase_kernel_certificate kind w n b f)

def atContextSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((earlier w n).imp ((formulaCode w n b f).imp ((valid w n))))).close

theorem source_atContext {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atContextSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidityPoint.at_context hZ w n b f h0 h1 h2

theorem atContext_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atContextSentence w n b f)) := TheoryTransport.sentence (source_atContext w n b f)

theorem native_atContext {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atContextSentence w n b f)) := ZFReplay.replay (atContext_kernel_certificate w n b f)

def propertySentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((earlier w n).imp ((property w n)))).close

theorem source_property {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (propertySentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (earlier w n) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidityPoint.property_from_earlier hZ w n h0 h1

theorem property_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (propertySentence w n)) := TheoryTransport.sentence (source_property w n)

theorem native_property {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (propertySentence w n)) := ZFReplay.replay (property_kernel_certificate w n)

def progressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((BoundedInduction.progressive FormulaCodeTreeValiditySyntax.matrix (fun _ : Fin 1 => w) w))).close

theorem source_progressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (progressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidity.progressive hZ w h0

theorem progressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (progressiveSentence w)) := TheoryTransport.sentence (source_progressive w)

theorem native_progressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (progressiveSentence w)) := ZFReplay.replay (progressive_kernel_certificate w)

def allPropertiesSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))))).close

theorem source_allProperties {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allPropertiesSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidity.all_properties hZ w h0

theorem allProperties_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allPropertiesSentence w)) := TheoryTransport.sentence (source_allProperties w)

theorem native_allProperties {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allPropertiesSentence w)) := ZFReplay.replay (allProperties_kernel_certificate w)

def codeSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((valid w n)))).close

theorem source_code {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidity.code hZ w n b f h0 h1

theorem code_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeSentence w n b f)) := TheoryTransport.sentence (source_code w n b f)

theorem native_code {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeSentence w n b f)) := ZFReplay.replay (code_kernel_certificate w n b f)

def rejectNonTreeSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp (((valid w n).neg).imp (((formulaCode w n b f).neg)))).close

theorem source_rejectNonTree {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectNonTreeSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((valid w n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((valid w n).neg) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidity.reject_non_tree hZ w n b f h0 h1

theorem rejectNonTree_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectNonTreeSentence w n b f)) := TheoryTransport.sentence (source_rejectNonTree w n b f)

theorem native_rejectNonTree {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectNonTreeSentence w n b f)) := ZFReplay.replay (rejectNonTree_kernel_certificate w n b f)

def decodedTreeSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((decodedFiber w n)))).close

theorem source_decodedTree {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodedTreeSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidity.decoded hZ w n b f h0 h1

theorem decodedTree_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedTreeSentence w n b f)) := TheoryTransport.sentence (source_decodedTree w n b f)

theorem native_decodedTree {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedTreeSentence w n b f)) := ZFReplay.replay (decodedTree_kernel_certificate w n b f)

def treeChildrenSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shape w n t p l g).imp ((validChildren w g))))).close

theorem source_treeChildren {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeChildrenSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTreeValidity.children hZ w n b f t p l g h0 h1 h2

theorem treeChildren_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeChildrenSentence w n b f t p l g)) := TheoryTransport.sentence (source_treeChildren w n b f t p l g)

theorem native_treeChildren {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeChildrenSentence w n b f t p l g)) := ZFReplay.replay (treeChildren_kernel_certificate w n b f t p l g)

def typedCasesSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shape w n t p l g).imp ((FormulaCodeTypedDataSyntax.cases 11 w t l g b f))))).close

theorem source_typedCases {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedCasesSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataForward.cases_of_shape hZ w n b f t p l g h0 h1 h2

theorem typedCases_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedCasesSentence w n b f t p l g)) := TheoryTransport.sentence (source_typedCases w n b f t p l g)

theorem native_typedCases {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedCasesSentence w n b f t p l g)) := ZFReplay.replay (typedCases_kernel_certificate w n b f t p l g)

def typedDataSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((shape w n t p l g).imp ((typedData w n b f t p l g))))).close

theorem source_typedData {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedDataSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataForward.data_of_shape hZ w n b f t p l g h0 h1 h2

theorem typedData_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedDataSentence w n b f t p l g)) := TheoryTransport.sentence (source_typedData w n b f t p l g)

theorem native_typedData {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedDataSentence w n b f t p l g)) := ZFReplay.replay (typedData_kernel_certificate w n b f t p l g)

def typedFiberSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((formulaCode w n b f).imp ((FormulaCodeTypedDataSyntax.typedFiber w n b f)))).close

theorem source_typedFiber {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedFiberSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataForward.actual_fiber hZ w n b f h0 h1

theorem typedFiber_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedFiberSentence w n b f)) := TheoryTransport.sentence (source_typedFiber w n b f)

theorem native_typedFiber {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedFiberSentence w n b f)) := ZFReplay.replay (typedFiber_kernel_certificate w n b f)

def rejectCasesSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp (((FormulaCodeTypedDataSyntax.cases 11 w t l g b f).neg).imp (((formulaCode w n b f).neg))))).close

theorem source_rejectCases {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectCasesSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeTypedDataSyntax.cases 11 w t l g b f).neg) (Context.add (shape w n t p l g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((FormulaCodeTypedDataSyntax.cases 11 w t l g b f).neg) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataForward.reject_cases hZ w n b f t p l g h0 h1 h2

theorem rejectCases_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectCasesSentence w n b f t p l g)) := TheoryTransport.sentence (source_rejectCases w n b f t p l g)

theorem native_rejectCases {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectCasesSentence w n b f t p l g)) := ZFReplay.replay (rejectCases_kernel_certificate w n b f t p l g)

def rejectDataSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp (((typedData w n b f t p l g).neg).imp (((formulaCode w n b f).neg))))).close

theorem source_rejectData {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectDataSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((typedData w n b f t p l g).neg) (Context.add (shape w n t p l g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((typedData w n b f t p l g).neg) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataForward.reject_data hZ w n b f t p l g h0 h1 h2

theorem rejectData_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectDataSentence w n b f t p l g)) := TheoryTransport.sentence (source_rejectData w n b f t p l g)

theorem native_rejectData {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectDataSentence w n b f t p l g)) := ZFReplay.replay (rejectData_kernel_certificate w n b f t p l g)

def dataTreeValidSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((typedData w n b f t p l g).imp ((valid w n)))).close

theorem source_dataTreeValid {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (dataTreeValidSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (typedData w n b f t p l g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (typedData w n b f t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataForward.data_tree_valid hZ w n b f t p l g h0 h1

theorem dataTreeValid_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (dataTreeValidSentence w n b f t p l g)) := TheoryTransport.sentence (source_dataTreeValid w n b f t p l g)

theorem native_dataTreeValid {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (dataTreeValidSentence w n b f t p l g)) := ZFReplay.replay (dataTreeValid_kernel_certificate w n b f t p l g)

end PPAC.Migration.Internal.ObjectFormulaCodeTreeValidity
