import PPAC.Migration.Internal.FormulaCodeTypedDecode

/-! 全内部真实字段恢复、完整类型识别及实际唯一纤维双向原nativeZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxNumeralSyntax SyntaxForestSyntax SyntaxNodeSyntax
open SyntaxFieldsFromSlots (slots)
open SyntaxSlotSyntax (slot)
open SyntaxForestFields (graphLaw)
open SyntaxCheckedSlotExists (existsSlot)
open StructuralListLengthSyntax (hasLength)
open StructuralListFieldGraphSyntax (fields)
open StructuralTreeOperatorSyntax (shape)
open FormulaCodeSyntax FormulaCodeTypedDataSyntax FormulaCodeAllowedAritySyntax

def slotIndexSentence {m} (j : Nat) (g y i : Fin m) : Source.Sentence := ((slot g j y).imp ((numeral j i).imp ((edge g i y)))).close

theorem source_slotIndex {m} (j : Nat) (g y i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (slotIndexSentence j g y i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (numeral j i) (Context.add (slot g j y) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (slot g j y) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (numeral j i) := .hyp (Or.inl rfl)
  exact SyntaxFieldsFromSlots.slot_at_index hZ g y i j h0 h1

theorem slotIndex_kernel_certificate {m} (j : Nat) (g y i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (slotIndexSentence j g y i)) := TheoryTransport.sentence (source_slotIndex j g y i)

theorem native_slotIndex {m} (j : Nat) (g y i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (slotIndexSentence j g y i)) := ZFReplay.replay (slotIndex_kernel_certificate j g y i)

def slotNaturalSentence {m} (j : Nat) (g w y : Fin m) : Source.Sentence := ((slot g j y).imp ((SequenceSyntax.bounded g w).imp ((Formula.mem y w)))).close

theorem source_slotNatural {m} (j : Nat) (g w y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (slotNaturalSentence j g w y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequenceSyntax.bounded g w) (Context.add (slot g j y) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (slot g j y) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SequenceSyntax.bounded g w) := .hyp (Or.inl rfl)
  exact SyntaxFieldsFromSlots.slot_natural g w y j h0 h1

theorem slotNatural_kernel_certificate {m} (j : Nat) (g w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (slotNaturalSentence j g w y)) := TheoryTransport.sentence (source_slotNatural j g w y)

theorem native_slotNatural {m} (j : Nat) (g w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (slotNaturalSentence j g w y)) := ZFReplay.replay (slotNatural_kernel_certificate j g w y)

def slotInputsSentence {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : Source.Sentence := ((fields w p l g).imp ((slots k g xs).imp ((inputs k w xs)))).close

theorem source_slotInputs {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (slotInputsSentence k xs w p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (slots k g xs) (Context.add (fields w p l g) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (fields w p l g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (slots k g xs) := .hyp (Or.inl rfl)
  exact SyntaxFieldsFromSlots.inputs_of_slots k w p l g xs h0 h1

theorem slotInputs_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (slotInputsSentence k xs w p l g)) := TheoryTransport.sentence (source_slotInputs k xs w p l g)

theorem native_slotInputs {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (slotInputsSentence k xs w p l g)) := ZFReplay.replay (slotInputs_kernel_certificate k xs w p l g)

def slotsFullSentence {m} (k : Nat) (xs : Fin k → Fin m) (w p l g i y : Fin m) : Source.Sentence := ((fields w p l g).imp ((numeral k l).imp ((slots k g xs).imp (((edge g i y).iff (SyntaxPositionSyntax.positions k xs i y)))))).close

theorem source_slotsFull {m} (k : Nat) (xs : Fin k → Fin m) (w p l g i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (slotsFullSentence k xs w p l g i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (slots k g xs) (Context.add (numeral k l) (Context.add (fields w p l g) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (fields w p l g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (numeral k l) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (slots k g xs) := .hyp (Or.inl rfl)
  exact SyntaxFieldsFromSlots.full_iff hZ k w p l g xs i y h0 h1 h2

theorem slotsFull_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w p l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (slotsFullSentence k xs w p l g i y)) := TheoryTransport.sentence (source_slotsFull k xs w p l g i y)

theorem native_slotsFull {m} (k : Nat) (xs : Fin k → Fin m) (w p l g i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (slotsFullSentence k xs w p l g i y)) := ZFReplay.replay (slotsFull_kernel_certificate k xs w p l g i y)

def slotsAllSentence {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : Source.Sentence := ((fields w p l g).imp ((numeral k l).imp ((slots k g xs).imp ((graphLaw k xs g))))).close

theorem source_slotsAll {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (slotsAllSentence k xs w p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (slots k g xs) (Context.add (numeral k l) (Context.add (fields w p l g) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (fields w p l g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (numeral k l) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (slots k g xs) := .hyp (Or.inl rfl)
  exact SyntaxFieldsFromSlots.all_edges hZ k w p l g xs h0 h1 h2

theorem slotsAll_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (slotsAllSentence k xs w p l g)) := TheoryTransport.sentence (source_slotsAll k xs w p l g)

theorem native_slotsAll {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (slotsAllSentence k xs w p l g)) := ZFReplay.replay (slotsAll_kernel_certificate k xs w p l g)

def graphEqualitySentence {m} (k : Nat) (xs : Fin k → Fin m) (g h d e : Fin m) : Source.Sentence := ((entriesOn g d).imp ((entriesOn h e).imp ((graphLaw k xs g).imp ((graphLaw k xs h).imp ((Formula.equal g h)))))).close

theorem source_graphEquality {m} (k : Nat) (xs : Fin k → Fin m) (g h d e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphEqualitySentence k xs g h d e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graphLaw k xs h) (Context.add (graphLaw k xs g) (Context.add (entriesOn h e) (Context.add (entriesOn g d) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (entriesOn g d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (entriesOn h e) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (graphLaw k xs g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (graphLaw k xs h) := .hyp (Or.inl rfl)
  exact SyntaxForestFromFields.equal_graphs hZ k xs g h d e h0 h1 h2 h3

theorem graphEquality_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (g h d e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphEqualitySentence k xs g h d e)) := TheoryTransport.sentence (source_graphEquality k xs g h d e)

theorem native_graphEquality {m} (k : Nat) (xs : Fin k → Fin m) (g h d e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphEqualitySentence k xs g h d e)) := ZFReplay.replay (graphEquality_kernel_certificate k xs g h d e)

def fieldsGraphSubstSentence {m} (w p l g h : Fin m) : Source.Sentence := ((Formula.equal g h).imp ((fields w p l g).imp ((fields w p l h)))).close

theorem source_fieldsGraphSubst {m} (w p l g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fieldsGraphSubstSentence w p l g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (fields w p l g) (Context.add (Formula.equal g h) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (Formula.equal g h) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (fields w p l g) := .hyp (Or.inl rfl)
  exact SyntaxForestFromFields.fields_subst_graph w p l g h h0 h1

theorem fieldsGraphSubst_kernel_certificate {m} (w p l g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldsGraphSubstSentence w p l g h)) := TheoryTransport.sentence (source_fieldsGraphSubst w p l g h)

theorem native_fieldsGraphSubst {m} (w p l g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldsGraphSubstSentence w p l g h)) := ZFReplay.replay (fieldsGraphSubst_kernel_certificate w p l g h)

def forestRecoverSentence {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : Source.Sentence := ((omega w).imp ((hasLength w p l).imp ((fields w p l g).imp ((numeral k l).imp ((slots k g xs).imp ((forest k w xs p))))))).close

theorem source_forestRecover {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestRecoverSentence k xs w p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (slots k g xs) (Context.add (numeral k l) (Context.add (fields w p l g) (Context.add (hasLength w p l) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (hasLength w p l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (fields w p l g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral k l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (slots k g xs) := .hyp (Or.inl rfl)
  exact SyntaxForestFromFields.recover hZ k w p l g xs h0 h1 h2 h3 h4

theorem forestRecover_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestRecoverSentence k xs w p l g)) := TheoryTransport.sentence (source_forestRecover k xs w p l g)

theorem native_forestRecover {m} (k : Nat) (xs : Fin k → Fin m) (w p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestRecoverSentence k xs w p l g)) := ZFReplay.replay (forestRecover_kernel_certificate k xs w p l g)

def constructorRecoverSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral k l).imp ((slots k g xs).imp ((constructor k tag w xs n))))))).close

theorem source_constructorRecover {m} (k tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constructorRecoverSentence k tag xs w n t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (slots k g xs) (Context.add (numeral k l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral k l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (slots k g xs) := .hyp (Or.inl rfl)
  exact SyntaxForestFromFields.constructor_of_shape hZ k tag w n t p l g xs h0 h1 h2 h3 h4

theorem constructorRecover_kernel_certificate {m} (k tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorRecoverSentence k tag xs w n t p l g)) := TheoryTransport.sentence (source_constructorRecover k tag xs w n t p l g)

theorem native_constructorRecover {m} (k tag : Nat) (xs : Fin k → Fin m) (w n t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorRecoverSentence k tag xs w n t p l g)) := ZFReplay.replay (constructorRecover_kernel_certificate k tag xs w n t p l g)

def knownTypesSentence {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((constructor (expectedArity tag) tag w xs n).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (rootCheck tag w g b f)))))).close

theorem source_knownTypes {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : Derives (Source.SetLanguage.ZF.at 0) (knownTypesSentence tag xs w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (constructor (expectedArity tag) tag w xs n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (constructor (expectedArity tag) tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataKnown.known_iff hZ tag ht w n b f t p l g xs h0 h1 h2

theorem knownTypes_kernel_certificate {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (knownTypesSentence tag xs w n b f t p l g)) := TheoryTransport.sentence (source_knownTypes tag xs w n b f t p l g ht)

theorem native_knownTypes {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (knownTypesSentence tag xs w n b f t p l g)) := ZFReplay.replay (knownTypes_kernel_certificate tag xs w n b f t p l g ht)

def codeFromSlotsSentence {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral (expectedArity tag) l).imp ((slots (expectedArity tag) g xs).imp ((rootCheck tag w g b f).imp ((formulaCode w n b f)))))))).close

theorem source_codeFromSlots {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : Derives (Source.SetLanguage.ZF.at 0) (codeFromSlotsSentence tag xs w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) (Context.add (slots (expectedArity tag) g xs) (Context.add (numeral (expectedArity tag) l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (numeral (expectedArity tag) l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (slots (expectedArity tag) g xs) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataKnown.from_slots hZ tag ht w n b f t p l g xs h0 h1 h2 h3 h4 h5

theorem codeFromSlots_kernel_certificate {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFromSlotsSentence tag xs w n b f t p l g)) := TheoryTransport.sentence (source_codeFromSlots tag xs w n b f t p l g ht)

theorem native_codeFromSlots {m} (tag : Nat) (xs : Fin (expectedArity tag) → Fin m) (w n b f t p l g : Fin m) (ht : tag < 11) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFromSlotsSentence tag xs w n b f t p l g)) := ZFReplay.replay (codeFromSlots_kernel_certificate tag xs w n b f t p l g ht)

def rootSlotSentence {m} (k tag : Nat) (j : Fin k) (w g b f : Fin m) : Source.Sentence := ((rootCheck tag w g b f).imp ((existsSlot g j.val))).close

theorem source_rootSlot {m} (k tag : Nat) (j : Fin k) (w g b f : Fin m) (ht : tag < 11) (hk : k = expectedArity tag) : Derives (Source.SetLanguage.ZF.at 0) (rootSlotSentence k tag j w g b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeRootSlots.at_arity k tag ht hk w g b f j h0

theorem rootSlot_kernel_certificate {m} (k tag : Nat) (j : Fin k) (w g b f : Fin m) (ht : tag < 11) (hk : k = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rootSlotSentence k tag j w g b f)) := TheoryTransport.sentence (source_rootSlot k tag j w g b f ht hk)

theorem native_rootSlot {m} (k tag : Nat) (j : Fin k) (w g b f : Fin m) (ht : tag < 11) (hk : k = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rootSlotSentence k tag j w g b f)) := ZFReplay.replay (rootSlot_kernel_certificate k tag j w g b f ht hk)

def arity0Sentence {m} (tag : Nat) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral 0 l).imp ((rootCheck tag w g b f).imp ((formulaCode w n b f))))))).close

theorem source_arity0 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 0 = expectedArity tag) : Derives (Source.SetLanguage.ZF.at 0) (arity0Sentence tag w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) (Context.add (numeral 0 l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral 0 l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataOperands.arity0 hZ tag ht hk w n b f t p l g h0 h1 h2 h3 h4

theorem arity0_kernel_certificate {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 0 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arity0Sentence tag w n b f t p l g)) := TheoryTransport.sentence (source_arity0 tag w n b f t p l g ht hk)

theorem native_arity0 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 0 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arity0Sentence tag w n b f t p l g)) := ZFReplay.replay (arity0_kernel_certificate tag w n b f t p l g ht hk)

def arity1Sentence {m} (tag : Nat) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral 1 l).imp ((rootCheck tag w g b f).imp ((formulaCode w n b f))))))).close

theorem source_arity1 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 1 = expectedArity tag) : Derives (Source.SetLanguage.ZF.at 0) (arity1Sentence tag w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) (Context.add (numeral 1 l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral 1 l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataOperands.arity1 hZ tag ht hk w n b f t p l g h0 h1 h2 h3 h4

theorem arity1_kernel_certificate {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 1 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arity1Sentence tag w n b f t p l g)) := TheoryTransport.sentence (source_arity1 tag w n b f t p l g ht hk)

theorem native_arity1 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 1 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arity1Sentence tag w n b f t p l g)) := ZFReplay.replay (arity1_kernel_certificate tag w n b f t p l g ht hk)

def arity2Sentence {m} (tag : Nat) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral 2 l).imp ((rootCheck tag w g b f).imp ((formulaCode w n b f))))))).close

theorem source_arity2 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 2 = expectedArity tag) : Derives (Source.SetLanguage.ZF.at 0) (arity2Sentence tag w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) (Context.add (numeral 2 l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral 2 l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataOperands.arity2 hZ tag ht hk w n b f t p l g h0 h1 h2 h3 h4

theorem arity2_kernel_certificate {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 2 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arity2Sentence tag w n b f t p l g)) := TheoryTransport.sentence (source_arity2 tag w n b f t p l g ht hk)

theorem native_arity2 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 2 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arity2Sentence tag w n b f t p l g)) := ZFReplay.replay (arity2_kernel_certificate tag w n b f t p l g ht hk)

def arity3Sentence {m} (tag : Nat) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral 3 l).imp ((rootCheck tag w g b f).imp ((formulaCode w n b f))))))).close

theorem source_arity3 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 3 = expectedArity tag) : Derives (Source.SetLanguage.ZF.at 0) (arity3Sentence tag w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) (Context.add (numeral 3 l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral 3 l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataOperands.arity3 hZ tag ht hk w n b f t p l g h0 h1 h2 h3 h4

theorem arity3_kernel_certificate {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 3 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arity3Sentence tag w n b f t p l g)) := TheoryTransport.sentence (source_arity3 tag w n b f t p l g ht hk)

theorem native_arity3 {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) (hk : 3 = expectedArity tag) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arity3Sentence tag w n b f t p l g)) := ZFReplay.replay (arity3_kernel_certificate tag w n b f t p l g ht hk)

def rootCheckSentence {m} (tag : Nat) (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((numeral tag t).imp ((numeral (expectedArity tag) l).imp ((rootCheck tag w g b f).imp ((formulaCode w n b f))))))).close

theorem source_rootCheck {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) : Derives (Source.SetLanguage.ZF.at 0) (rootCheckSentence tag w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (rootCheck tag w g b f) (Context.add (numeral (expectedArity tag) l) (Context.add (numeral tag t) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (numeral tag t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (numeral (expectedArity tag) l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (rootCheck tag w g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataReverse.root_check hZ tag ht w n b f t p l g h0 h1 h2 h3 h4

theorem rootCheck_kernel_certificate {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rootCheckSentence tag w n b f t p l g)) := TheoryTransport.sentence (source_rootCheck tag w n b f t p l g ht)

theorem native_rootCheck {m} (tag : Nat) (w n b f t p l g : Fin m) (ht : tag < 11) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rootCheckSentence tag w n b f t p l g)) := ZFReplay.replay (rootCheck_kernel_certificate tag w n b f t p l g ht)

def casesCodeSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp ((FormulaCodeTypedDataSyntax.cases 11 w t l g b f).imp ((formulaCode w n b f))))).close

theorem source_casesCode {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (casesCodeSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeTypedDataSyntax.cases 11 w t l g b f) (Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeTypedDataSyntax.cases 11 w t l g b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataReverse.code_of_cases hZ w n b f t p l g h0 h1 h2

theorem casesCode_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (casesCodeSentence w n b f t p l g)) := TheoryTransport.sentence (source_casesCode w n b f t p l g)

theorem native_casesCode {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (casesCodeSentence w n b f t p l g)) := ZFReplay.replay (casesCode_kernel_certificate w n b f t p l g)

def dataCodeSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((typedData w n b f t p l g).imp ((formulaCode w n b f)))).close

theorem source_dataCode {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (dataCodeSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (typedData w n b f t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (typedData w n b f t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataReverse.code_of_data hZ w n b f t p l g h0 h1

theorem dataCode_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (dataCodeSentence w n b f t p l g)) := TheoryTransport.sentence (source_dataCode w n b f t p l g)

theorem native_dataCode {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (dataCodeSentence w n b f t p l g)) := ZFReplay.replay (dataCode_kernel_certificate w n b f t p l g)

def dataIffSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (typedData w n b f t p l g))))).close

theorem source_dataIff {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (dataIffSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataReverse.data_iff hZ w n b f t p l g h0 h1

theorem dataIff_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (dataIffSentence w n b f t p l g)) := TheoryTransport.sentence (source_dataIff w n b f t p l g)

theorem native_dataIff {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (dataIffSentence w n b f t p l g)) := ZFReplay.replay (dataIff_kernel_certificate w n b f t p l g)

def casesIffSentence {m} (w n b f t p l g : Fin m) : Source.Sentence := ((omega w).imp ((shape w n t p l g).imp (((formulaCode w n b f).iff (FormulaCodeTypedDataSyntax.cases 11 w t l g b f))))).close

theorem source_casesIff {m} (w n b f t p l g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (casesIffSentence w n b f t p l g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (shape w n t p l g) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (shape w n t p l g) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDataReverse.cases_iff hZ w n b f t p l g h0 h1

theorem casesIff_kernel_certificate {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (casesIffSentence w n b f t p l g)) := TheoryTransport.sentence (source_casesIff w n b f t p l g)

theorem native_casesIff {m} (w n b f t p l g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (casesIffSentence w n b f t p l g)) := ZFReplay.replay (casesIff_kernel_certificate w n b f t p l g)

def fiberCodeSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((typedFiber w n b f).imp ((formulaCode w n b f)))).close

theorem source_fiberCode {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberCodeSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (typedFiber w n b f) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (typedFiber w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDecode.code_of_fiber hZ w n b f h0 h1

theorem fiberCode_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberCodeSentence w n b f)) := TheoryTransport.sentence (source_fiberCode w n b f)

theorem native_fiberCode {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberCodeSentence w n b f)) := ZFReplay.replay (fiberCode_kernel_certificate w n b f)

def fiberIffSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp (((formulaCode w n b f).iff (typedFiber w n b f)))).close

theorem source_fiberIff {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberIffSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDecode.fiber_iff hZ w n b f h0

theorem fiberIff_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberIffSentence w n b f)) := TheoryTransport.sentence (source_fiberIff w n b f)

theorem native_fiberIff {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberIffSentence w n b f)) := ZFReplay.replay (fiberIff_kernel_certificate w n b f)

def rejectFiberIffSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp (((formulaCode w n b f).neg.iff (typedFiber w n b f).neg))).close

theorem source_rejectFiberIff {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectFiberIffSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDecode.reject_fiber_iff hZ w n b f h0

theorem rejectFiberIff_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectFiberIffSentence w n b f)) := TheoryTransport.sentence (source_rejectFiberIff w n b f)

theorem native_rejectFiberIff {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectFiberIffSentence w n b f)) := ZFReplay.replay (rejectFiberIff_kernel_certificate w n b f)

def classificationSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((((formulaCode w n b f).conj (typedFiber w n b f)).disj ((formulaCode w n b f).neg.conj (typedFiber w n b f).neg)))).close

theorem source_classification {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (classificationSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeTypedDecode.classification hZ w n b f h0

theorem classification_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (classificationSentence w n b f)) := TheoryTransport.sentence (source_classification w n b f)

theorem native_classification {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (classificationSentence w n b f)) := ZFReplay.replay (classification_kernel_certificate w n b f)

end PPAC.Migration.Internal.ObjectFormulaCodeTypedDecode
