import PPAC.Migration.Internal.FormulaCodeGraphTyping

/-! 原森林完整字段对应及解码图类型检查的原nativeZF闭句模式；内部索引/值均无标准性限制。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxTypedFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxNodeSyntax SyntaxForestSyntax SyntaxNumeralSyntax SyntaxTermSyntax SyntaxAtomSyntax
open SyntaxLogicalSyntax (singleCode binaryCode quantifierTag)
open StructuralListLengthSyntax (hasLength)
open StructuralListFieldSyntax (field)
open StructuralListFieldGraphSyntax (fields)
open StructuralTreeOperatorSyntax (shape)
open SyntaxPositionSyntax SyntaxForestFields SyntaxSlotSyntax SyntaxCheckedFieldSyntax MinimalPredicates
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeTypedFields FormulaCodeGraphTyping

def numeralMembersSentence {m} (k : Nat) (l i : Fin m) : Source.Sentence := ((numeral k l).imp (((Formula.mem i l).iff (below k i)))).close

theorem source_numeralMembers {m} (k : Nat) (l i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (numeralMembersSentence k l i) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (numeral k l) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (numeral k l) := .hyp (Or.inl rfl)
  exact SyntaxNumeralMembers.member_iff hZ k l i h0

theorem numeralMembers_kernel_certificate {m} (k : Nat) (l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numeralMembersSentence k l i)) := TheoryTransport.sentence (source_numeralMembers k l i)

theorem native_numeralMembers {m} (k : Nat) (l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numeralMembersSentence k l i)) := ZFReplay.replay (numeralMembers_kernel_certificate k l i)

def indexMemberSentence {m} (k : Nat) (j : Fin k) (l i : Fin m) : Source.Sentence := ((numeral k l).imp ((numeral j.val i).imp ((Formula.mem i l)))).close

theorem source_indexMember {m} (k : Nat) (j : Fin k) (l i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (indexMemberSentence k j l i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j.val i) (Context.add (numeral k l) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (numeral k l) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (numeral j.val i) := .hyp (Or.inl rfl)
  exact SyntaxNumeralMembers.index_member hZ k j l i h0 h1

theorem indexMember_kernel_certificate {m} (k : Nat) (j : Fin k) (l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (indexMemberSentence k j l i)) := TheoryTransport.sentence (source_indexMember k j l i)

theorem native_indexMember {m} (k : Nat) (j : Fin k) (l i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (indexMemberSentence k j l i)) := ZFReplay.replay (indexMember_kernel_certificate k j l i)

def forestValueSentence {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((numeral j.val i).imp (((field w n i y).iff (.equal y (xs j))))))).close

theorem source_forestValue {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestValueSentence k xs j w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j.val i) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (forest k w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (numeral j.val i) := .hyp (Or.inl rfl)
  exact SyntaxForestFieldValues.field_at hZ k w xs n j i y h0 h1 h2

theorem forestValue_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestValueSentence k xs j w n i y)) := TheoryTransport.sentence (source_forestValue k xs j w n i y)

theorem native_forestValue {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestValueSentence k xs j w n i y)) := ZFReplay.replay (forestValue_kernel_certificate k xs j w n i y)

def forestEdgeSentence {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n l g i y : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((hasLength w n l).imp ((fields w n l g).imp ((numeral j.val i).imp (((edge g i y).iff (.equal y (xs j))))))))).close

theorem source_forestEdge {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n l g i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestEdgeSentence k xs j w n l g i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j.val i) (Context.add (fields w n l g) (Context.add (hasLength w n l) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (forest k w xs n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (hasLength w n l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (fields w n l g) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (numeral j.val i) := .hyp (Or.inl rfl)
  exact SyntaxForestFields.edge_at hZ k w xs n l g j i y h0 h1 h2 h3 h4

theorem forestEdge_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestEdgeSentence k xs j w n l g i y)) := TheoryTransport.sentence (source_forestEdge k xs j w n l g i y)

theorem native_forestEdge {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestEdgeSentence k xs j w n l g i y)) := ZFReplay.replay (forestEdge_kernel_certificate k xs j w n l g i y)

def forestFullSentence {m} (k : Nat) (xs : Fin k → Fin m) (w n l g i y : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((hasLength w n l).imp ((fields w n l g).imp (((edge g i y).iff (positions k xs i y))))))).close

theorem source_forestFull {m} (k : Nat) (xs : Fin k → Fin m) (w n l g i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestFullSentence k xs w n l g i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (fields w n l g) (Context.add (hasLength w n l) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (forest k w xs n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (hasLength w n l) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (fields w n l g) := .hyp (Or.inl rfl)
  exact SyntaxForestFields.full_iff hZ k w xs n l g i y h0 h1 h2 h3

theorem forestFull_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w n l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestFullSentence k xs w n l g i y)) := TheoryTransport.sentence (source_forestFull k xs w n l g i y)

theorem native_forestFull {m} (k : Nat) (xs : Fin k → Fin m) (w n l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestFullSentence k xs w n l g i y)) := ZFReplay.replay (forestFull_kernel_certificate k xs w n l g i y)

def forestAllSentence {m} (k : Nat) (xs : Fin k → Fin m) (w n l g : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((hasLength w n l).imp ((fields w n l g).imp ((graphLaw k xs g)))))).close

theorem source_forestAll {m} (k : Nat) (xs : Fin k → Fin m) (w n l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestAllSentence k xs w n l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (fields w n l g) (Context.add (hasLength w n l) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (forest k w xs n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (hasLength w n l) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (fields w n l g) := .hyp (Or.inl rfl)
  exact SyntaxForestFields.all_edges hZ k w xs n l g h0 h1 h2 h3

theorem forestAll_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w n l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestAllSentence k xs w n l g)) := TheoryTransport.sentence (source_forestAll k xs w n l g)

theorem native_forestAll {m} (k : Nat) (xs : Fin k → Fin m) (w n l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestAllSentence k xs w n l g)) := ZFReplay.replay (forestAll_kernel_certificate k xs w n l g)

def nodeAllSentence {m} (k : Nat) (xs : Fin k → Fin m) (w a n t p l g : Fin m) : Source.Sentence := ((omega w).imp ((node k w a xs n).imp ((shape w n t p l g).imp ((graphLaw k xs g))))).close

theorem source_nodeAll {m} (k : Nat) (xs : Fin k → Fin m) (w a n t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nodeAllSentence k xs w a n t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (node k w a xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (node k w a xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact SyntaxNodeFields.node hZ k w a xs n t p l g h0 h1 h2

theorem nodeAll_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w a n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeAllSentence k xs w a n t p l g)) := TheoryTransport.sentence (source_nodeAll k xs w a n t p l g)

theorem native_nodeAll {m} (k : Nat) (xs : Fin k → Fin m) (w a n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeAllSentence k xs w a n t p l g)) := ZFReplay.replay (nodeAll_kernel_certificate k xs w a n t p l g)

def nodeValueSentence {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w a n t p l g i y : Fin m) : Source.Sentence := ((omega w).imp ((node k w a xs n).imp ((shape w n t p l g).imp ((numeral j.val i).imp (((edge g i y).iff (.equal y (xs j)))))))).close

theorem source_nodeValue {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w a n t p l g i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nodeValueSentence k xs j w a n t p l g i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j.val i) (Context.add (shape w n t p l g) (Context.add (node k w a xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (node k w a xs n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (numeral j.val i) := .hyp (Or.inl rfl)
  exact SyntaxNodeFields.edge_at_node hZ k w a xs n t p l g j i y h0 h1 h2 h3

theorem nodeValue_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w a n t p l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeValueSentence k xs j w a n t p l g i y)) := TheoryTransport.sentence (source_nodeValue k xs j w a n t p l g i y)

theorem native_nodeValue {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w a n t p l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeValueSentence k xs j w a n t p l g i y)) := ZFReplay.replay (nodeValue_kernel_certificate k xs j w a n t p l g i y)

def constructorAllSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp ((graphLaw k xs g))))).close

theorem source_constructorAll {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorAllSentence k tag xs w n t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact SyntaxNodeFields.constructor hZ k tag w xs n t p l g h0 h1 h2

theorem constructorAll_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorAllSentence k tag xs w n t p l g)) := TheoryTransport.sentence (source_constructorAll k tag xs w n t p l g)

theorem native_constructorAll {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorAllSentence k tag xs w n t p l g)) := ZFReplay.replay (constructorAll_kernel_certificate k tag xs w n t p l g)

def constructorValueSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g i y : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp ((numeral j.val i).imp (((edge g i y).iff (.equal y (xs j)))))))).close

theorem source_constructorValue {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorValueSentence k tag xs j w n t p l g i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j.val i) (Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (numeral j.val i) := .hyp (Or.inl rfl)
  exact SyntaxNodeFields.edge_at_constructor hZ k tag w xs n t p l g j i y h0 h1 h2 h3

theorem constructorValue_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorValueSentence k tag xs j w n t p l g i y)) := TheoryTransport.sentence (source_constructorValue k tag xs j w n t p l g i y)

theorem native_constructorValue {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorValueSentence k tag xs j w n t p l g i y)) := ZFReplay.replay (constructorValue_kernel_certificate k tag xs j w n t p l g i y)

def slotSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g y : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp (((slot g j.val y).iff (.equal y (xs j))))))).close

theorem source_slot {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (slotSentence k tag xs j w n t p l g y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact SyntaxConstructorSlots.slot_iff hZ k tag w xs n t p l g j y h0 h1 h2

theorem slot_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (slotSentence k tag xs j w n t p l g y)) := TheoryTransport.sentence (source_slot k tag xs j w n t p l g y)

theorem native_slot {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (slotSentence k tag xs j w n t p l g y)) := ZFReplay.replay (slot_kernel_certificate k tag xs j w n t p l g y)

def checkedSentence {m} (q : Nat) (a : Formula (q+1)) (ρ : Fin q → Fin m) (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp (((checked a ρ g j.val).iff (pred a ρ (xs j))))))).close

theorem source_checked {m} (q : Nat) (a : Formula (q+1)) (ρ : Fin q → Fin m) (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkedSentence q a ρ k tag xs j w n t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact SyntaxCheckedFields.iff_at_constructor hZ a ρ k tag w xs n t p l g j h0 h1 h2

theorem checked_kernel_certificate {m} (q : Nat) (a : Formula (q+1)) (ρ : Fin q → Fin m) (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkedSentence q a ρ k tag xs j w n t p l g)) := TheoryTransport.sentence (source_checked q a ρ k tag xs j w n t p l g)

theorem native_checked {m} (q : Nat) (a : Formula (q+1)) (ρ : Fin q → Fin m) (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkedSentence q a ρ k tag xs j w n t p l g)) := ZFReplay.replay (checked_kernel_certificate q a ρ k tag xs j w n t p l g)

def codeFieldSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp (((codeField w g j.val b f).iff (formulaCode w (xs j) b f)))))).close

theorem source_codeField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFieldSentence k tag xs j w n t p l g b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedFields.code_iff hZ k tag w xs n t p l g b f j h0 h1 h2

theorem codeField_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFieldSentence k tag xs j w n t p l g b f)) := TheoryTransport.sentence (source_codeField k tag xs j w n t p l g b f)

theorem native_codeField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFieldSentence k tag xs j w n t p l g b f)) := ZFReplay.replay (codeField_kernel_certificate k tag xs j w n t p l g b f)

def termFieldSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp (((termField w g j.val b f).iff (term w b f (xs j))))))).close

theorem source_termField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termFieldSentence k tag xs j w n t p l g b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedFields.term_iff hZ k tag w xs n t p l g b f j h0 h1 h2

theorem termField_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termFieldSentence k tag xs j w n t p l g b f)) := TheoryTransport.sentence (source_termField k tag xs j w n t p l g b f)

theorem native_termField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termFieldSentence k tag xs j w n t p l g b f)) := ZFReplay.replay (termField_kernel_certificate k tag xs j w n t p l g b f)

def advancedFieldSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp (((advancedField w g j.val b f).iff (advancedCode w (xs j) b f)))))).close

theorem source_advancedField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedFieldSentence k tag xs j w n t p l g b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedFields.advanced_iff hZ k tag w xs n t p l g b f j h0 h1 h2

theorem advancedField_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedFieldSentence k tag xs j w n t p l g b f)) := TheoryTransport.sentence (source_advancedField k tag xs j w n t p l g b f)

theorem native_advancedField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedFieldSentence k tag xs j w n t p l g b f)) := ZFReplay.replay (advancedField_kernel_certificate k tag xs j w n t p l g b f)

def zeroFieldSentence {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : Source.Sentence := ((omega w).imp ((constructor k tag w xs n).imp ((shape w n t p l g).imp (((zeroField w g j.val).iff (zeroScalar w (xs j))))))).close

theorem source_zeroField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroFieldSentence k tag xs j w n t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedFields.zero_iff hZ k tag w xs n t p l g j h0 h1 h2

theorem zeroField_kernel_certificate {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroFieldSentence k tag xs j w n t p l g)) := TheoryTransport.sentence (source_zeroField k tag xs j w n t p l g)

theorem native_zeroField {m} (k : Nat) (tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroFieldSentence k tag xs j w n t p l g)) := ZFReplay.replay (zeroField_kernel_certificate k tag xs j w n t p l g)

def memberTypingSentence {m} (w n b f s x y t p l g : Fin m) : Source.Sentence := ((omega w).imp ((memberCode w s x y n).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (memberCheck w g b f)))))).close

theorem source_memberTyping {m} (w n b f s x y t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberTypingSentence w n b f s x y t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (memberCode w s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeGraphTyping.membership hZ w n b f s x y t p l g h0 h1 h2

theorem memberTyping_kernel_certificate {m} (w n b f s x y t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberTypingSentence w n b f s x y t p l g)) := TheoryTransport.sentence (source_memberTyping w n b f s x y t p l g)

theorem native_memberTyping {m} (w n b f s x y t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberTypingSentence w n b f s x y t p l g)) := ZFReplay.replay (memberTyping_kernel_certificate w n b f s x y t p l g)

def equalTypingSentence {m} (w n b f x y t p l g : Fin m) : Source.Sentence := ((omega w).imp ((equalCode w x y n).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (equalCheck w g b f)))))).close

theorem source_equalTyping {m} (w n b f x y t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalTypingSentence w n b f x y t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeGraphTyping.equality hZ w n b f x y t p l g h0 h1 h2

theorem equalTyping_kernel_certificate {m} (w n b f x y t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalTypingSentence w n b f x y t p l g)) := TheoryTransport.sentence (source_equalTyping w n b f x y t p l g)

theorem native_equalTyping {m} (w n b f x y t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalTypingSentence w n b f x y t p l g)) := ZFReplay.replay (equalTyping_kernel_certificate w n b f x y t p l g)

def negationTypingSentence {m} (w n b f x t p l g : Fin m) : Source.Sentence := ((omega w).imp ((singleCode 4 w x n).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (singleCheck false w g b f)))))).close

theorem source_negationTyping {m} (w n b f x t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationTypingSentence w n b f x t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (singleCode 4 w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeGraphTyping.negation hZ w n b f x t p l g h0 h1 h2

theorem negationTyping_kernel_certificate {m} (w n b f x t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationTypingSentence w n b f x t p l g)) := TheoryTransport.sentence (source_negationTyping w n b f x t p l g)

theorem native_negationTyping {m} (w n b f x t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationTypingSentence w n b f x t p l g)) := ZFReplay.replay (negationTyping_kernel_certificate w n b f x t p l g)

def binaryTypingSentence {m} (kind : Fin 4) (w n b f x y t p l g : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode kind w x y n).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (binaryCheck w g b f)))))).close

theorem source_binaryTyping {m} (kind : Fin 4) (w n b f x y t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryTypingSentence kind w n b f x y t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeGraphTyping.binary hZ kind w n b f x y t p l g h0 h1 h2

theorem binaryTyping_kernel_certificate {m} (kind : Fin 4) (w n b f x y t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryTypingSentence kind w n b f x y t p l g)) := TheoryTransport.sentence (source_binaryTyping kind w n b f x y t p l g)

theorem native_binaryTyping {m} (kind : Fin 4) (w n b f x y t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryTypingSentence kind w n b f x y t p l g)) := ZFReplay.replay (binaryTyping_kernel_certificate kind w n b f x y t p l g)

def quantifierTypingSentence {m} (universal : Bool) (w n b f x t p l g : Fin m) : Source.Sentence := ((omega w).imp ((singleCode (quantifierTag universal) w x n).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (singleCheck true w g b f)))))).close

theorem source_quantifierTyping {m} (universal : Bool) (w n b f x t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierTypingSentence universal w n b f x t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (singleCode (quantifierTag universal) w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode (quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeGraphTyping.quantifier hZ universal w n b f x t p l g h0 h1 h2

theorem quantifierTyping_kernel_certificate {m} (universal : Bool) (w n b f x t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierTypingSentence universal w n b f x t p l g)) := TheoryTransport.sentence (source_quantifierTyping universal w n b f x t p l g)

theorem native_quantifierTyping {m} (universal : Bool) (w n b f x t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierTypingSentence universal w n b f x t p l g)) := ZFReplay.replay (quantifierTyping_kernel_certificate universal w n b f x t p l g)

def quantifierSuccessorSentence {m} (universal : Bool) (w n b f x t p l g u : Fin m) : Source.Sentence := ((omega w).imp ((singleCode (quantifierTag universal) w x n).imp ((shape w n t p l g).imp ((successor u b).imp (((formulaCode w n b f).iff ((contexts w b f).conj (codeField w g 0 u f)))))))).close

theorem source_quantifierSuccessor {m} (universal : Bool) (w n b f x t p l g u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierSuccessorSentence universal w n b f x t p l g u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor u b) (Context.add (shape w n t p l g) (Context.add (singleCode (quantifierTag universal) w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (singleCode (quantifierTag universal) w x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor u b) := .hyp (Or.inl rfl)
  exact FormulaCodeGraphTyping.quantifier_at_successor hZ universal w n b f x t p l g u h0 h1 h2 h3

theorem quantifierSuccessor_kernel_certificate {m} (universal : Bool) (w n b f x t p l g u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierSuccessorSentence universal w n b f x t p l g u)) := TheoryTransport.sentence (source_quantifierSuccessor universal w n b f x t p l g u)

theorem native_quantifierSuccessor {m} (universal : Bool) (w n b f x t p l g u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierSuccessorSentence universal w n b f x t p l g u)) := ZFReplay.replay (quantifierSuccessor_kernel_certificate universal w n b f x t p l g u)

end PPAC.Migration.Internal.ObjectSyntaxTypedFields
