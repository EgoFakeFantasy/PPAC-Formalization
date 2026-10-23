import PPAC.Migration.Internal.PureQuotationTypedFormulas

/-! quotation精确字段、作用域和实际带类型唯一纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectQuotationFields
open Source SourceAlgebra SourceLogic OmegaSyntax

def fieldNaturalSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((OriginalQuotationFieldSyntax.fields children w xs).imp ((SyntaxForestSyntax.inputs children.length w xs)))).close

theorem source_fieldNatural {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fieldNaturalSentence children xs w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inl rfl)
  exact OriginalQuotationFieldSyntax.natural_fields hZ children w xs h0 h1

theorem fieldNatural_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldNaturalSentence children xs w)) := TheoryTransport.sentence (source_fieldNatural children xs w)

theorem native_fieldNatural {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldNaturalSentence children xs w)) := ZFReplay.replay (fieldNatural_kernel_certificate children xs w)

def fieldAtSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (i : Fin children.length) (w : Fin m) : Source.Sentence := ((OriginalQuotationFieldSyntax.fields children w xs).imp ((OriginalTreeQuotationSyntax.tree (children.get i) w (xs i)))).close

theorem source_fieldAt {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (i : Fin children.length) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fieldAtSentence children xs i w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inl rfl)
  exact OriginalQuotationFieldSyntax.fields_at children w xs i h0

theorem fieldAt_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (i : Fin children.length) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldAtSentence children xs i w)) := TheoryTransport.sentence (source_fieldAt children xs i w)

theorem native_fieldAt {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (i : Fin children.length) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldAtSentence children xs i w)) := ZFReplay.replay (fieldAt_kernel_certificate children xs i w)

def forestOfFieldsSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : Source.Sentence := ((OriginalQuotationFieldSyntax.fields children w xs).imp ((SyntaxForestSyntax.forest children.length w xs p).imp ((OriginalTreeQuotationSyntax.forest children w p)))).close

theorem source_forestOfFields {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestOfFieldsSentence children xs w p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxForestSyntax.forest children.length w xs p) (Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxForestSyntax.forest children.length w xs p) := .hyp (Or.inl rfl)
  exact OriginalQuotationForestFields.forest_of_fields children w p xs h0 h1

theorem forestOfFields_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestOfFieldsSentence children xs w p)) := TheoryTransport.sentence (source_forestOfFields children xs w p)

theorem native_forestOfFields {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestOfFieldsSentence children xs w p)) := ZFReplay.replay (forestOfFields_kernel_certificate children xs w p)

def forestToFieldsSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : Source.Sentence := ((omega w).imp ((OriginalQuotationFieldSyntax.fields children w xs).imp ((OriginalTreeQuotationSyntax.forest children w p).imp ((SyntaxForestSyntax.forest children.length w xs p))))).close

theorem source_forestToFields {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestToFieldsSentence children xs w p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.forest children w p) (Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.forest children w p) := .hyp (Or.inl rfl)
  exact OriginalQuotationForestFields.forest_to_fields hZ children w p xs h0 h1 h2

theorem forestToFields_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestToFieldsSentence children xs w p)) := TheoryTransport.sentence (source_forestToFields children xs w p)

theorem native_forestToFields {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestToFieldsSentence children xs w p)) := ZFReplay.replay (forestToFields_kernel_certificate children xs w p)

def forestIffSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : Source.Sentence := ((omega w).imp ((OriginalQuotationFieldSyntax.fields children w xs).imp (((OriginalTreeQuotationSyntax.forest children w p).iff (SyntaxForestSyntax.forest children.length w xs p))))).close

theorem source_forestIff {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestIffSentence children xs w p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inl rfl)
  exact OriginalQuotationForestFields.forest_iff hZ children w p xs h0 h1

theorem forestIff_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestIffSentence children xs w p)) := TheoryTransport.sentence (source_forestIff children xs w p)

theorem native_forestIff {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestIffSentence children xs w p)) := ZFReplay.replay (forestIff_kernel_certificate children xs w p)

def treeOfConstructorSentence {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : Source.Sentence := ((OriginalQuotationFieldSyntax.fields children w xs).imp ((SyntaxNodeSyntax.constructor children.length tag w xs n).imp ((OriginalTreeQuotationSyntax.tree (.node tag children) w n)))).close

theorem source_treeOfConstructor {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeOfConstructorSentence tag children xs w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor children.length tag w xs n) (Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor children.length tag w xs n) := .hyp (Or.inl rfl)
  exact OriginalQuotationNodeFields.tree_of_constructor tag children w n xs h0 h1

theorem treeOfConstructor_kernel_certificate {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeOfConstructorSentence tag children xs w n)) := TheoryTransport.sentence (source_treeOfConstructor tag children xs w n)

theorem native_treeOfConstructor {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeOfConstructorSentence tag children xs w n)) := ZFReplay.replay (treeOfConstructor_kernel_certificate tag children xs w n)

def treeToConstructorSentence {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalQuotationFieldSyntax.fields children w xs).imp ((OriginalTreeQuotationSyntax.tree (.node tag children) w n).imp ((SyntaxNodeSyntax.constructor children.length tag w xs n))))).close

theorem source_treeToConstructor {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeToConstructorSentence tag children xs w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (.node tag children) w n) (Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node tag children) w n) := .hyp (Or.inl rfl)
  exact OriginalQuotationNodeFields.tree_to_constructor hZ tag children w n xs h0 h1 h2

theorem treeToConstructor_kernel_certificate {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeToConstructorSentence tag children xs w n)) := TheoryTransport.sentence (source_treeToConstructor tag children xs w n)

theorem native_treeToConstructor {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeToConstructorSentence tag children xs w n)) := ZFReplay.replay (treeToConstructor_kernel_certificate tag children xs w n)

def treeIffSentence {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalQuotationFieldSyntax.fields children w xs).imp (((OriginalTreeQuotationSyntax.tree (.node tag children) w n).iff (SyntaxNodeSyntax.constructor children.length tag w xs n))))).close

theorem source_treeIff {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeIffSentence tag children xs w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalQuotationFieldSyntax.fields children w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalQuotationFieldSyntax.fields children w xs) := .hyp (Or.inl rfl)
  exact OriginalQuotationNodeFields.tree_iff hZ tag children w n xs h0 h1

theorem treeIff_kernel_certificate {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeIffSentence tag children xs w n)) := TheoryTransport.sentence (source_treeIff tag children xs w n)

theorem native_treeIff {m} (tag : Nat) (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (xs : Fin children.length → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeIffSentence tag children xs w n)) := ZFReplay.replay (treeIff_kernel_certificate tag children xs w n)

def treeOfScalarSentence {m} (k : Nat) (w i n : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral k i).imp ((SyntaxNodeSyntax.scalar w i n).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k) w n)))).close

theorem source_treeOfScalar {m} (k : Nat) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeOfScalarSentence k w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.scalar w i n) (Context.add (SyntaxNumeralSyntax.numeral k i) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.scalar w i n) := .hyp (Or.inl rfl)
  exact OriginalQuotationVariableFields.tree_of_scalar k w i n h0 h1

theorem treeOfScalar_kernel_certificate {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeOfScalarSentence k w i n)) := TheoryTransport.sentence (source_treeOfScalar k w i n)

theorem native_treeOfScalar {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeOfScalarSentence k w i n)) := ZFReplay.replay (treeOfScalar_kernel_certificate k w i n)

def scalarOfTreeSentence {m} (k : Nat) (w i n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k i).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k) w n).imp ((SyntaxNodeSyntax.scalar w i n))))).close

theorem source_scalarOfTree {m} (k : Nat) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (scalarOfTreeSentence k w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k) w n) (Context.add (SyntaxNumeralSyntax.numeral k i) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k) w n) := .hyp (Or.inl rfl)
  exact OriginalQuotationVariableFields.scalar_of_tree hZ k w i n h0 h1 h2

theorem scalarOfTree_kernel_certificate {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (scalarOfTreeSentence k w i n)) := TheoryTransport.sentence (source_scalarOfTree k w i n)

theorem native_scalarOfTree {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (scalarOfTreeSentence k w i n)) := ZFReplay.replay (scalarOfTree_kernel_certificate k w i n)

def scalarIffSentence {m} (k : Nat) (w i n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k i).imp (((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k) w n).iff (SyntaxNodeSyntax.scalar w i n))))).close

theorem source_scalarIff {m} (k : Nat) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (scalarIffSentence k w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral k i) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inl rfl)
  exact OriginalQuotationVariableFields.scalar_iff hZ k w i n h0 h1

theorem scalarIff_kernel_certificate {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (scalarIffSentence k w i n)) := TheoryTransport.sentence (source_scalarIff k w i n)

theorem native_scalarIff {m} (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (scalarIffSentence k w i n)) := ZFReplay.replay (scalarIff_kernel_certificate k w i n)

def treeOfVariableSentence {m} (bound : Bool) (k : Nat) (w i n : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral k i).imp ((SyntaxVariableSyntax.code bound w i n).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag bound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n)))).close

theorem source_treeOfVariable {m} (bound : Bool) (k : Nat) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (treeOfVariableSentence bound k w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (SyntaxNumeralSyntax.numeral k i) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact OriginalQuotationVariableFields.tree_of_variable bound k w i n h0 h1

theorem treeOfVariable_kernel_certificate {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (treeOfVariableSentence bound k w i n)) := TheoryTransport.sentence (source_treeOfVariable bound k w i n)

theorem native_treeOfVariable {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (treeOfVariableSentence bound k w i n)) := ZFReplay.replay (treeOfVariable_kernel_certificate bound k w i n)

def variableOfTreeSentence {m} (bound : Bool) (k : Nat) (w i n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k i).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag bound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n).imp ((SyntaxVariableSyntax.code bound w i n))))).close

theorem source_variableOfTree {m} (bound : Bool) (k : Nat) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableOfTreeSentence bound k w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag bound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n) (Context.add (SyntaxNumeralSyntax.numeral k i) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag bound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n) := .hyp (Or.inl rfl)
  exact OriginalQuotationVariableFields.variable_of_tree hZ bound k w i n h0 h1 h2

theorem variableOfTree_kernel_certificate {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableOfTreeSentence bound k w i n)) := TheoryTransport.sentence (source_variableOfTree bound k w i n)

theorem native_variableOfTree {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableOfTreeSentence bound k w i n)) := ZFReplay.replay (variableOfTree_kernel_certificate bound k w i n)

def variableIffSentence {m} (bound : Bool) (k : Nat) (w i n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k i).imp (((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag bound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n).iff (SyntaxVariableSyntax.code bound w i n))))).close

theorem source_variableIff {m} (bound : Bool) (k : Nat) (w i n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableIffSentence bound k w i n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral k i) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inl rfl)
  exact OriginalQuotationVariableFields.variable_iff hZ bound k w i n h0 h1

theorem variableIff_kernel_certificate {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableIffSentence bound k w i n)) := TheoryTransport.sentence (source_variableIff bound k w i n)

theorem native_variableIff {m} (bound : Bool) (k : Nat) (w i n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableIffSentence bound k w i n)) := ZFReplay.replay (variableIff_kernel_certificate bound k w i n)

def contextsOfLengthsSentence {m} (bLen fLen : Nat) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bLen b).imp ((SyntaxNumeralSyntax.numeral fLen f).imp ((SyntaxTermSyntax.contexts w b f))))).close

theorem source_contextsOfLengths {m} (bLen fLen : Nat) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (contextsOfLengthsSentence bLen fLen w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral fLen f) (Context.add (SyntaxNumeralSyntax.numeral bLen b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bLen b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fLen f) := .hyp (Or.inl rfl)
  exact PureQuotationTermTyping.contexts_of_lengths hZ bLen fLen w b f h0 h1 h2

theorem contextsOfLengths_kernel_certificate {m} (bLen fLen : Nat) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (contextsOfLengthsSentence bLen fLen w b f)) := TheoryTransport.sentence (source_contextsOfLengths bLen fLen w b f)

theorem native_contextsOfLengths {m} (bLen fLen : Nat) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (contextsOfLengthsSentence bLen fLen w b f)) := ZFReplay.replay (contextsOfLengths_kernel_certificate bLen fLen w b f)

def termTypeSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length b).imp ((SyntaxNumeralSyntax.numeral free.length f).imp ((PureQuotationSyntax.term input w n).imp ((SyntaxTermSyntax.term w b f n)))))).close

theorem source_termType {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termTypeSentence input w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term input w n) (Context.add (SyntaxNumeralSyntax.numeral free.length f) (Context.add (SyntaxNumeralSyntax.numeral bound.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PureQuotationSyntax.term input w n) := .hyp (Or.inl rfl)
  exact PureQuotationTermTyping.term_type hZ input w b f n h0 h1 h2 h3

theorem termType_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termTypeSentence input w b f n)) := TheoryTransport.sentence (source_termType input w b f n)

theorem native_termType {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termTypeSentence input w b f n)) := ZFReplay.replay (termType_kernel_certificate input w b f n)

def termTypedExistsSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length b).imp ((SyntaxNumeralSyntax.numeral free.length f).imp ((PureQuotationTypedSyntax.termExists input w b f))))).close

theorem source_termTypedExists {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termTypedExistsSentence input w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral free.length f) (Context.add (SyntaxNumeralSyntax.numeral bound.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f) := .hyp (Or.inl rfl)
  exact PureQuotationTypedTerms.exists_typed hZ input w b f h0 h1 h2

theorem termTypedExists_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termTypedExistsSentence input w b f)) := TheoryTransport.sentence (source_termTypedExists input w b f)

theorem native_termTypedExists {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termTypedExistsSentence input w b f)) := ZFReplay.replay (termTypedExists_kernel_certificate input w b f)

def termTypedUniqueSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n v : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationTypedSyntax.termValue input w b f n).imp ((PureQuotationTypedSyntax.termValue input w b f v).imp ((Formula.equal n v))))).close

theorem source_termTypedUnique {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termTypedUniqueSentence input w b f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationTypedSyntax.termValue input w b f v) (Context.add (PureQuotationTypedSyntax.termValue input w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureQuotationTypedSyntax.termValue input w b f n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PureQuotationTypedSyntax.termValue input w b f v) := .hyp (Or.inl rfl)
  exact PureQuotationTypedTerms.unique hZ input w b f n v h0 h1 h2

theorem termTypedUnique_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termTypedUniqueSentence input w b f n v)) := TheoryTransport.sentence (source_termTypedUnique input w b f n v)

theorem native_termTypedUnique {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termTypedUniqueSentence input w b f n v)) := ZFReplay.replay (termTypedUnique_kernel_certificate input w b f n v)

def termTypedUniqueOutputSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationTypedSyntax.termValue input w b f n).imp ((PureQuotationTypedSyntax.termUnique input w b f n)))).close

theorem source_termTypedUniqueOutput {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termTypedUniqueOutputSentence input w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationTypedSyntax.termValue input w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureQuotationTypedSyntax.termValue input w b f n) := .hyp (Or.inl rfl)
  exact PureQuotationTypedTerms.unique_output hZ input w b f n h0 h1

theorem termTypedUniqueOutput_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termTypedUniqueOutputSentence input w b f n)) := TheoryTransport.sentence (source_termTypedUniqueOutput input w b f n)

theorem native_termTypedUniqueOutput {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termTypedUniqueOutputSentence input w b f n)) := ZFReplay.replay (termTypedUniqueOutput_kernel_certificate input w b f n)

def termTypedFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length b).imp ((SyntaxNumeralSyntax.numeral free.length f).imp ((PureQuotationTypedSyntax.termFiber input w b f))))).close

theorem source_termTypedFiber {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termTypedFiberSentence input w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral free.length f) (Context.add (SyntaxNumeralSyntax.numeral bound.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f) := .hyp (Or.inl rfl)
  exact PureQuotationTypedTerms.actual_fiber hZ input w b f h0 h1 h2

theorem termTypedFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termTypedFiberSentence input w b f)) := TheoryTransport.sentence (source_termTypedFiber input w b f)

theorem native_termTypedFiber {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termTypedFiberSentence input w b f)) := ZFReplay.replay (termTypedFiber_kernel_certificate input w b f)

def formulaTypeSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length b).imp ((SyntaxNumeralSyntax.numeral free.length f).imp ((PureQuotationSyntax.formula input w n).imp ((FormulaCodeSyntax.formulaCode w n b f)))))).close

theorem source_formulaType {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaTypeSentence input w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w n) (Context.add (SyntaxNumeralSyntax.numeral free.length f) (Context.add (SyntaxNumeralSyntax.numeral bound.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inl rfl)
  exact PureQuotationFormulaTyping.formula_type hZ input w b f n h0 h1 h2 h3

theorem formulaType_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaTypeSentence input w b f n)) := TheoryTransport.sentence (source_formulaType input w b f n)

theorem native_formulaType {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaTypeSentence input w b f n)) := ZFReplay.replay (formulaType_kernel_certificate input w b f n)

def formulaTypedExistsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length b).imp ((SyntaxNumeralSyntax.numeral free.length f).imp ((PureQuotationTypedSyntax.formulaExists input w b f))))).close

theorem source_formulaTypedExists {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaTypedExistsSentence input w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral free.length f) (Context.add (SyntaxNumeralSyntax.numeral bound.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f) := .hyp (Or.inl rfl)
  exact PureQuotationTypedFormulas.exists_typed hZ input w b f h0 h1 h2

theorem formulaTypedExists_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaTypedExistsSentence input w b f)) := TheoryTransport.sentence (source_formulaTypedExists input w b f)

theorem native_formulaTypedExists {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaTypedExistsSentence input w b f)) := ZFReplay.replay (formulaTypedExists_kernel_certificate input w b f)

def formulaTypedUniqueSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n v : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationTypedSyntax.formulaValue input w b f n).imp ((PureQuotationTypedSyntax.formulaValue input w b f v).imp ((Formula.equal n v))))).close

theorem source_formulaTypedUnique {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaTypedUniqueSentence input w b f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationTypedSyntax.formulaValue input w b f v) (Context.add (PureQuotationTypedSyntax.formulaValue input w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureQuotationTypedSyntax.formulaValue input w b f n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PureQuotationTypedSyntax.formulaValue input w b f v) := .hyp (Or.inl rfl)
  exact PureQuotationTypedFormulas.unique hZ input w b f n v h0 h1 h2

theorem formulaTypedUnique_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaTypedUniqueSentence input w b f n v)) := TheoryTransport.sentence (source_formulaTypedUnique input w b f n v)

theorem native_formulaTypedUnique {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaTypedUniqueSentence input w b f n v)) := ZFReplay.replay (formulaTypedUnique_kernel_certificate input w b f n v)

def formulaTypedUniqueOutputSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((PureQuotationTypedSyntax.formulaValue input w b f n).imp ((PureQuotationTypedSyntax.formulaUnique input w b f n)))).close

theorem source_formulaTypedUniqueOutput {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaTypedUniqueOutputSentence input w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationTypedSyntax.formulaValue input w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureQuotationTypedSyntax.formulaValue input w b f n) := .hyp (Or.inl rfl)
  exact PureQuotationTypedFormulas.unique_output hZ input w b f n h0 h1

theorem formulaTypedUniqueOutput_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaTypedUniqueOutputSentence input w b f n)) := TheoryTransport.sentence (source_formulaTypedUniqueOutput input w b f n)

theorem native_formulaTypedUniqueOutput {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaTypedUniqueOutputSentence input w b f n)) := ZFReplay.replay (formulaTypedUniqueOutput_kernel_certificate input w b f n)

def formulaTypedFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length b).imp ((SyntaxNumeralSyntax.numeral free.length f).imp ((PureQuotationTypedSyntax.formulaFiber input w b f))))).close

theorem source_formulaTypedFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaTypedFiberSentence input w b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral free.length f) (Context.add (SyntaxNumeralSyntax.numeral bound.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f) := .hyp (Or.inl rfl)
  exact PureQuotationTypedFormulas.actual_fiber hZ input w b f h0 h1 h2

theorem formulaTypedFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaTypedFiberSentence input w b f)) := TheoryTransport.sentence (source_formulaTypedFiber input w b f)

theorem native_formulaTypedFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaTypedFiberSentence input w b f)) := ZFReplay.replay (formulaTypedFiber_kernel_certificate input w b f)

def nullaryTypeSentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w b f).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w n).imp ((FormulaCodeSyntax.formulaCode w n b f))))).close

theorem source_nullaryType {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryTypeSentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w n) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w n) := .hyp (Or.inl rfl)
  exact OriginalQuotationFormulaFields.nullary_type hZ truth w b f n h0 h1 h2

theorem nullaryType_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryTypeSentence truth w b f n)) := TheoryTransport.sentence (source_nullaryType truth w b f n)

theorem native_nullaryType {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryTypeSentence truth w b f n)) := ZFReplay.replay (nullaryType_kernel_certificate truth w b f n)

def equalTypeSentence {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.tree (.node 3 [left,right]) w n).imp ((OriginalTreeQuotationSyntax.tree left w x).imp ((OriginalTreeQuotationSyntax.tree right w y).imp ((SyntaxTermSyntax.term w b f x).imp ((SyntaxTermSyntax.term w b f y).imp ((FormulaCodeSyntax.formulaCode w n b f)))))))).close

theorem source_equalType {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalTypeSentence left right w b f n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w b f y) (Context.add (SyntaxTermSyntax.term w b f x) (Context.add (OriginalTreeQuotationSyntax.tree right w y) (Context.add (OriginalTreeQuotationSyntax.tree left w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node 3 [left,right]) w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 3 [left,right]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree left w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree right w y) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTermSyntax.term w b f x) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxTermSyntax.term w b f y) := .hyp (Or.inl rfl)
  exact OriginalQuotationFormulaFields.equal_type hZ left right w b f n x y h0 h1 h2 h3 h4 h5

theorem equalType_kernel_certificate {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalTypeSentence left right w b f n x y)) := TheoryTransport.sentence (source_equalType left right w b f n x y)

theorem native_equalType {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalTypeSentence left right w b f n x y)) := ZFReplay.replay (equalType_kernel_certificate left right w b f n x y)

def memberTypeSentence {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n s x y : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,left,right]) w n).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0) w s).imp ((OriginalTreeQuotationSyntax.tree left w x).imp ((OriginalTreeQuotationSyntax.tree right w y).imp ((SyntaxTermSyntax.term w b f x).imp ((SyntaxTermSyntax.term w b f y).imp ((FormulaCodeSyntax.formulaCode w n b f))))))))).close

theorem source_memberType {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n s x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberTypeSentence left right w b f n s x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w b f y) (Context.add (SyntaxTermSyntax.term w b f x) (Context.add (OriginalTreeQuotationSyntax.tree right w y) (Context.add (OriginalTreeQuotationSyntax.tree left w x) (Context.add (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0) w s) (Context.add (OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,left,right]) w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,left,right]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0) w s) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree left w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree right w y) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxTermSyntax.term w b f x) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxTermSyntax.term w b f y) := .hyp (Or.inl rfl)
  exact OriginalQuotationFormulaFields.member_type hZ left right w b f n s x y h0 h1 h2 h3 h4 h5 h6

theorem memberType_kernel_certificate {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberTypeSentence left right w b f n s x y)) := TheoryTransport.sentence (source_memberType left right w b f n s x y)

theorem native_memberType {m} (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n s x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberTypeSentence left right w b f n s x y)) := ZFReplay.replay (memberType_kernel_certificate left right w b f n s x y)

def negationTypeSentence {m} (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w b f).imp ((OriginalTreeQuotationSyntax.tree (.node 4 [body]) w n).imp ((OriginalTreeQuotationSyntax.tree body w x).imp ((FormulaCodeSyntax.formulaCode w x b f).imp ((FormulaCodeSyntax.formulaCode w n b f))))))).close

theorem source_negationType {m} (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationTypeSentence body w b f n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w x b f) (Context.add (OriginalTreeQuotationSyntax.tree body w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node 4 [body]) w n) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 4 [body]) w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree body w x) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaCodeSyntax.formulaCode w x b f) := .hyp (Or.inl rfl)
  exact OriginalQuotationFormulaFields.negation_type hZ body w b f n x h0 h1 h2 h3 h4

theorem negationType_kernel_certificate {m} (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationTypeSentence body w b f n x)) := TheoryTransport.sentence (source_negationType body w b f n x)

theorem native_negationType {m} (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationTypeSentence body w b f n x)) := ZFReplay.replay (negationType_kernel_certificate body w b f n x)

def binaryTypeSentence {m} (kind : Fin 4) (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w b f).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n).imp ((OriginalTreeQuotationSyntax.tree left w x).imp ((OriginalTreeQuotationSyntax.tree right w y).imp ((FormulaCodeSyntax.formulaCode w x b f).imp ((FormulaCodeSyntax.formulaCode w y b f).imp ((FormulaCodeSyntax.formulaCode w n b f))))))))).close

theorem source_binaryType {m} (kind : Fin 4) (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryTypeSentence kind left right w b f n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w y b f) (Context.add (FormulaCodeSyntax.formulaCode w x b f) (Context.add (OriginalTreeQuotationSyntax.tree right w y) (Context.add (OriginalTreeQuotationSyntax.tree left w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree left w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree right w y) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (FormulaCodeSyntax.formulaCode w x b f) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (FormulaCodeSyntax.formulaCode w y b f) := .hyp (Or.inl rfl)
  exact OriginalQuotationFormulaFields.binary_type hZ kind left right w b f n x y h0 h1 h2 h3 h4 h5 h6

theorem binaryType_kernel_certificate {m} (kind : Fin 4) (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryTypeSentence kind left right w b f n x y)) := TheoryTransport.sentence (source_binaryType kind left right w b f n x y)

theorem native_binaryType {m} (kind : Fin 4) (left right : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryTypeSentence kind left right w b f n x y)) := ZFReplay.replay (binaryType_kernel_certificate kind left right w b f n x y)

def quantifiedTypeSentence {m} (universal : Bool) (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w b f).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n).imp ((OriginalTreeQuotationSyntax.tree body w x).imp ((successor k b).imp ((FormulaCodeSyntax.formulaCode w x k f).imp ((FormulaCodeSyntax.formulaCode w n b f)))))))).close

theorem source_quantifiedType {m} (universal : Bool) (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifiedTypeSentence universal body w b f n x k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w x k f) (Context.add (successor k b) (Context.add (OriginalTreeQuotationSyntax.tree body w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree body w x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor k b) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaCodeSyntax.formulaCode w x k f) := .hyp (Or.inl rfl)
  exact OriginalQuotationFormulaFields.quantified_type hZ universal body w b f n x k h0 h1 h2 h3 h4 h5

theorem quantifiedType_kernel_certificate {m} (universal : Bool) (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifiedTypeSentence universal body w b f n x k)) := TheoryTransport.sentence (source_quantifiedType universal body w b f n x k)

theorem native_quantifiedType {m} (universal : Bool) (body : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w b f n x k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifiedTypeSentence universal body w b f n x k)) := ZFReplay.replay (quantifiedType_kernel_certificate universal body w b f n x k)

end PPAC.Migration.Internal.ObjectQuotationFields
