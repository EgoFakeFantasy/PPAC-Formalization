import PPAC.Migration.Internal.RawCodeFieldAtConstructor

/-! 输入零码全内部get归纳、field组合及实际有限构造槽位的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectRawCodeField
open Source SourceAlgebra SourceLogic OmegaSyntax

def rawGetZeroAllInternalIndicesSentence {m} (w z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (RawCodeGetZeroSyntax.correct w.castSucc z.castSucc (Fin.last m))))))).close

theorem source_rawGetZeroAllInternalIndices {m} (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetZeroAllInternalIndicesSentence w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact RawCodeGetZero.all_indices hZ w z h0 h1

theorem rawGetZeroAllInternalIndices_kernel_certificate {m} (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetZeroAllInternalIndicesSentence w z)) := TheoryTransport.sentence (source_rawGetZeroAllInternalIndices w z)

theorem native_rawGetZeroAllInternalIndices {m} (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetZeroAllInternalIndicesSentence w z)) := ZFReplay.replay (rawGetZeroAllInternalIndices_kernel_certificate w z)

def rawGetZeroInputIffSentence {m} (w z i y : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((Formula.mem i w).imp (((RawCodeGetSyntax.get w z i y).iff (empty y)))))).close

theorem source_rawGetZeroInputIff {m} (w z i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetZeroInputIffSentence w z i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeGetZero.checked_iff hZ w z i y h0 h1 h2

theorem rawGetZeroInputIff_kernel_certificate {m} (w z i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetZeroInputIffSentence w z i y)) := TheoryTransport.sentence (source_rawGetZeroInputIff w z i y)

theorem native_rawGetZeroInputIff {m} (w z i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetZeroInputIffSentence w z i y)) := ZFReplay.replay (rawGetZeroInputIff_kernel_certificate w z i y)

def rawFieldExistsSentence {m} (w x i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeFieldSyntax.existsField w x i)))).close

theorem source_rawFieldExists {m} (w x i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldExistsSentence w x i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeField.exists_value hZ w x i h0 h1

theorem rawFieldExists_kernel_certificate {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldExistsSentence w x i)) := TheoryTransport.sentence (source_rawFieldExists w x i)

theorem native_rawFieldExists {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldExistsSentence w x i)) := ZFReplay.replay (rawFieldExists_kernel_certificate w x i)

def rawFieldUniqueSentence {m} (w x i y z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeFieldSyntax.field w x i y).imp ((RawCodeFieldSyntax.field w x i z).imp ((Formula.equal y z)))))).close

theorem source_rawFieldUnique {m} (w x i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldUniqueSentence w x i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeFieldSyntax.field w x i z) (Context.add (RawCodeFieldSyntax.field w x i y) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (RawCodeFieldSyntax.field w x i y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeFieldSyntax.field w x i z) := .hyp (Or.inl rfl)
  exact RawCodeField.unique hZ w x i y z h0 h1 h2 h3

theorem rawFieldUnique_kernel_certificate {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldUniqueSentence w x i y z)) := TheoryTransport.sentence (source_rawFieldUnique w x i y z)

theorem native_rawFieldUnique {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldUniqueSentence w x i y z)) := ZFReplay.replay (rawFieldUnique_kernel_certificate w x i y z)

def rawFieldFiberSentence {m} (w x i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((RawCodeFieldSyntax.fiber w x i)))).close

theorem source_rawFieldFiber {m} (w x i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldFiberSentence w x i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeField.exists_unique hZ w x i h0 h1

theorem rawFieldFiber_kernel_certificate {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldFiberSentence w x i)) := TheoryTransport.sentence (source_rawFieldFiber w x i)

theorem native_rawFieldFiber {m} (w x i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldFiberSentence w x i)) := ZFReplay.replay (rawFieldFiber_kernel_certificate w x i)

def rawFieldRangeSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((RawCodeFieldSyntax.field w x i y).imp ((Formula.mem y w)))).close

theorem source_rawFieldRange {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldRangeSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeFieldSyntax.field w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (RawCodeFieldSyntax.field w x i y) := .hyp (Or.inl rfl)
  exact RawCodeField.range hZ w x i y h0 h1

theorem rawFieldRange_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldRangeSentence w x i y)) := TheoryTransport.sentence (source_rawFieldRange w x i y)

theorem native_rawFieldRange {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldRangeSentence w x i y)) := ZFReplay.replay (rawFieldRange_kernel_certificate w x i y)

def rawFieldAtActualPayloadIffSentence {m} (w x p i y : Fin m) : Source.Sentence := ((omega w).imp ((PairingProjectionSyntax.step true false w x p).imp (((RawCodeFieldSyntax.field w x i y).iff (RawCodeGetSyntax.get w p i y))))).close

theorem source_rawFieldAtActualPayloadIff {m} (w x p i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldAtActualPayloadIffSentence w x p i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PairingProjectionSyntax.step true false w x p) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PairingProjectionSyntax.step true false w x p) := .hyp (Or.inl rfl)
  exact RawCodeField.at_payload_iff hZ w x p i y h0 h1

theorem rawFieldAtActualPayloadIff_kernel_certificate {m} (w x p i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldAtActualPayloadIffSentence w x p i y)) := TheoryTransport.sentence (source_rawFieldAtActualPayloadIff w x p i y)

theorem native_rawFieldAtActualPayloadIff {m} (w x p i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldAtActualPayloadIffSentence w x p i y)) := ZFReplay.replay (rawFieldAtActualPayloadIff_kernel_certificate w x p i y)

def rawFieldAtArbitraryRawTagIffSentence {m} (w tag p x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem tag w).imp ((Formula.mem p w).imp ((StructuralNodeSyntax.raw w tag p x).imp (((RawCodeFieldSyntax.field w x i y).iff (RawCodeGetSyntax.get w p i y))))))).close

theorem source_rawFieldAtArbitraryRawTagIff {m} (w tag p x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldAtArbitraryRawTagIffSentence w tag p x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w tag p x) (Context.add (Formula.mem p w) (Context.add (Formula.mem tag w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem tag w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralNodeSyntax.raw w tag p x) := .hyp (Or.inl rfl)
  exact RawCodeField.on_raw_iff hZ w tag p x i y h0 h1 h2 h3

theorem rawFieldAtArbitraryRawTagIff_kernel_certificate {m} (w tag p x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldAtArbitraryRawTagIffSentence w tag p x i y)) := TheoryTransport.sentence (source_rawFieldAtArbitraryRawTagIff w tag p x i y)

theorem native_rawFieldAtArbitraryRawTagIff {m} (w tag p x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldAtArbitraryRawTagIffSentence w tag p x i y)) := ZFReplay.replay (rawFieldAtArbitraryRawTagIff_kernel_certificate w tag p x i y)

def rawFieldZeroInputIffSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((empty x).imp ((Formula.mem i w).imp (((RawCodeFieldSyntax.field w x i y).iff (empty y)))))).close

theorem source_rawFieldZeroInputIff {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldZeroInputIffSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (empty x) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty x) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact RawCodeField.zero_iff hZ w x i y h0 h1 h2

theorem rawFieldZeroInputIff_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldZeroInputIffSentence w x i y)) := TheoryTransport.sentence (source_rawFieldZeroInputIff w x i y)

theorem native_rawFieldZeroInputIff {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldZeroInputIffSentence w x i y)) := ZFReplay.replay (rawFieldZeroInputIff_kernel_certificate w x i y)

def rawHeadTailOnActualConsIffSentence {m} (head : Bool) (w h t n y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp (((RawCodeProjectionSyntax.step head w n y).iff (Formula.equal y (if head then h else t)))))))).close

theorem source_rawHeadTailOnActualConsIff {m} (head : Bool) (w h t n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawHeadTailOnActualConsIffSentence head w h t n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inl rfl)
  exact RawCodeProjectionCanonical.on_cons_iff hZ head w h t n y h0 h1 h2 h3

theorem rawHeadTailOnActualConsIff_kernel_certificate {m} (head : Bool) (w h t n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawHeadTailOnActualConsIffSentence head w h t n y)) := TheoryTransport.sentence (source_rawHeadTailOnActualConsIff head w h t n y)

theorem native_rawHeadTailOnActualConsIff {m} (head : Bool) (w h t n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawHeadTailOnActualConsIffSentence head w h t n y)) := ZFReplay.replay (rawHeadTailOnActualConsIff_kernel_certificate head w h t n y)

def rawGetAtFiniteForestIffSentence {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxForestSyntax.forest k w xs n).imp ((SyntaxNumeralSyntax.numeral j.val i).imp (((RawCodeGetSyntax.get w n i y).iff (Formula.equal y (xs j))))))).close

theorem source_rawGetAtFiniteForestIff {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawGetAtFiniteForestIffSentence k xs j w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (SyntaxForestSyntax.forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxForestSyntax.forest k w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inl rfl)
  exact RawCodeFieldAtConstructor.forest_at hZ k w xs n j i y h0 h1 h2

theorem rawGetAtFiniteForestIff_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawGetAtFiniteForestIffSentence k xs j w n i y)) := TheoryTransport.sentence (source_rawGetAtFiniteForestIff k xs j w n i y)

theorem native_rawGetAtFiniteForestIff {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawGetAtFiniteForestIffSentence k xs j w n i y)) := ZFReplay.replay (rawGetAtFiniteForestIff_kernel_certificate k xs j w n i y)

def rawFieldAtFiniteNodeIffSentence {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w tag n i y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.node k w tag xs n).imp ((SyntaxNumeralSyntax.numeral j.val i).imp (((RawCodeFieldSyntax.field w n i y).iff (Formula.equal y (xs j))))))).close

theorem source_rawFieldAtFiniteNodeIff {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w tag n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldAtFiniteNodeIffSentence k xs j w tag n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (SyntaxNodeSyntax.node k w tag xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.node k w tag xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inl rfl)
  exact RawCodeFieldAtConstructor.node_at hZ k w tag xs n j i y h0 h1 h2

theorem rawFieldAtFiniteNodeIff_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w tag n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldAtFiniteNodeIffSentence k xs j w tag n i y)) := TheoryTransport.sentence (source_rawFieldAtFiniteNodeIff k xs j w tag n i y)

theorem native_rawFieldAtFiniteNodeIff {m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (w tag n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldAtFiniteNodeIffSentence k xs j w tag n i y)) := ZFReplay.replay (rawFieldAtFiniteNodeIff_kernel_certificate k xs j w tag n i y)

def rawFieldAtFiniteConstructorIffSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k tag w xs n).imp ((SyntaxNumeralSyntax.numeral j.val i).imp (((RawCodeFieldSyntax.field w n i y).iff (Formula.equal y (xs j))))))).close

theorem source_rawFieldAtFiniteConstructorIff {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawFieldAtFiniteConstructorIffSentence k tag xs j w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (SyntaxNodeSyntax.constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inl rfl)
  exact RawCodeFieldAtConstructor.constructor_at hZ k tag w xs n j i y h0 h1 h2

theorem rawFieldAtFiniteConstructorIff_kernel_certificate {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawFieldAtFiniteConstructorIffSentence k tag xs j w n i y)) := TheoryTransport.sentence (source_rawFieldAtFiniteConstructorIff k tag xs j w n i y)

theorem native_rawFieldAtFiniteConstructorIff {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawFieldAtFiniteConstructorIffSentence k tag xs j w n i y)) := ZFReplay.replay (rawFieldAtFiniteConstructorIff_kernel_certificate k tag xs j w n i y)

end PPAC.Migration.Internal.ObjectRawCodeField
