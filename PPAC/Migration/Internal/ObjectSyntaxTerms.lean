import PPAC.Migration.Internal.SyntaxTermReject

/-! 原字段反向解码、变量唯一索引及纯项全内部作用域正确性的原核闭句模式。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxTerms
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNodeSyntax SyntaxVariableSyntax SyntaxVariableDecodeSyntax SyntaxTermSyntax

def forestInputSentence {m} (k : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((forest k w ys n).imp (Formula.equal (xs i) (ys i))))).close

def nodeInputSentence {m} (k : Nat) (w a b : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k) : Source.Sentence := ((omega w).imp ((node k w a xs n).imp ((node k w b ys n).imp (Formula.equal (xs i) (ys i))))).close

def constructorInputSentence {m} (k a b : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k) : Source.Sentence := ((omega w).imp ((constructor k a w xs n).imp ((constructor k b w ys n).imp (Formula.equal (xs i) (ys i))))).close

def forestAritySentence {m} (k l : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) : Source.Sentence := ((omega w).imp ((forest k w xs n).imp ((forest l w ys n).imp (Formula.bot)))).close

def nodeAritySentence {m} (k l : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) : Source.Sentence := ((omega w).imp ((node k w a xs n).imp ((node l w b ys n).imp (Formula.bot)))).close

def indexNaturalSentence {m} (bound : Bool) (w i n : Fin m) : Source.Sentence := ((code bound w i n).imp (Formula.mem i w)).close

def indexInjectiveSentence {m} (bound : Bool) (w i j n : Fin m) : Source.Sentence := ((omega w).imp ((code bound w i n).imp ((code bound w j n).imp (Formula.equal i j)))).close

def variableDecodeSentence {m} (bound : Bool) (w n : Fin m) : Source.Sentence := ((omega w).imp ((recognized bound w n).iff (indexFiber bound w n))).close

def indexFiberSentence {m} (bound : Bool) (w n i : Fin m) : Source.Sentence := ((omega w).imp ((code bound w i n).imp (indexFiber bound w n))).close

def branchScopeSentence {m} (bound : Bool) (w l n i : Fin m) : Source.Sentence := ((omega w).imp ((code bound w i n).imp ((branch bound w l n).iff (.mem i l)))).close

def branchDecodeSentence {m} (bound : Bool) (w l n : Fin m) : Source.Sentence := ((omega w).imp ((branch bound w l n).iff (decodedBranch bound w l n))).close

def scopeSentence {m} (bound : Bool) (w b f n i : Fin m) : Source.Sentence := ((omega w).imp ((code bound w i n).imp ((term w b f n).iff (scope bound w b f i)))).close

def termExistsSentence {m} (bound : Bool) (w b f i : Fin m) : Source.Sentence := ((omega w).imp ((scope bound w b f i).imp (existsAt bound w b f i))).close

def termRangeSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((term w b f n).imp (Formula.mem n w))).close

def termDecodeSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((term w b f n).iff (decoded w b f n))).close

def branchExclusiveSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((branch true w b n).imp ((branch false w f n).imp (Formula.bot)))).close

def decodedExclusiveSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((decodedBranch true w b n).imp ((decodedBranch false w f n).imp (Formula.bot)))).close

def rejectScopeSentence {m} (bound : Bool) (w b f n i : Fin m) : Source.Sentence := ((omega w).imp ((code bound w i n).imp (((Formula.mem i (limit bound b f)).neg).imp ((term w b f n).neg)))).close

def rejectEmptySentence {m} (w b f n : Fin m) : Source.Sentence := ((OmegaSyntax.empty b).imp ((OmegaSyntax.empty f).imp ((term w b f n).neg))).close

def rejectTagSentence {m} (k label : Nat) (w b f n : Fin m) (xs : Fin k → Fin m) : Source.Sentence := ((omega w).imp ((constructor k label w xs n).imp ((term w b f n).neg))).close

def rejectFunctionSentence {m} (k : Nat) (w b f n : Fin m) (xs : Fin k → Fin m) : Source.Sentence := ((omega w).imp ((constructor k 2 w xs n).imp ((term w b f n).neg))).close

def rejectAritySentence {m} (k : Nat) (w a b f n : Fin m) (xs : Fin k → Fin m) : Source.Sentence := ((omega w).imp ((node k w a xs n).imp ((term w b f n).neg))).close

def rejectScalarSentence {m} (w a b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.scalar w a n).imp ((term w b f n).neg))).close

def branchEmptySentence {m} (bound : Bool) (w l n : Fin m) : Source.Sentence := ((OmegaSyntax.empty l).imp ((branch bound w l n).neg)).close

def rawRejectTagSentence {m} (label : Nat) (w b f t p n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral label t).imp ((Formula.mem p w).imp ((StructuralNodeSyntax.raw w t p n).imp ((term w b f n).neg))))).close

def rawRejectFunctionSentence {m} (w b f t p n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 t).imp ((Formula.mem p w).imp ((StructuralNodeSyntax.raw w t p n).imp ((term w b f n).neg))))).close

theorem source_forestInput {m} (k : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : Derives (Source.SetLanguage.ZF.at 0) (forestInputSentence k w xs ys n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (forest k w ys n) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxForestInjective.input_eq hZ k w xs ys n i (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem forestInput_kernel_certificate {m} (k : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestInputSentence k w xs ys n i)) := TheoryTransport.sentence (source_forestInput k w xs ys n i )

theorem native_forestInput {m} (k : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestInputSentence k w xs ys n i)) := ZFReplay.replay (forestInput_kernel_certificate k w xs ys n i )

theorem source_nodeInput {m} (k : Nat) (w a b : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : Derives (Source.SetLanguage.ZF.at 0) (nodeInputSentence k w a b xs ys n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (node k w b ys n) (Context.add (node k w a xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodeInjective.input_eq hZ k w a b xs ys n i (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nodeInput_kernel_certificate {m} (k : Nat) (w a b : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeInputSentence k w a b xs ys n i)) := TheoryTransport.sentence (source_nodeInput k w a b xs ys n i )

theorem native_nodeInput {m} (k : Nat) (w a b : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeInputSentence k w a b xs ys n i)) := ZFReplay.replay (nodeInput_kernel_certificate k w a b xs ys n i )

theorem source_constructorInput {m} (k a b : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : Derives (Source.SetLanguage.ZF.at 0) (constructorInputSentence k a b w xs ys n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor k b w ys n) (Context.add (constructor k a w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodeInjective.constructor_input_eq hZ k a b w xs ys n i (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem constructorInput_kernel_certificate {m} (k a b : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constructorInputSentence k a b w xs ys n i)) := TheoryTransport.sentence (source_constructorInput k a b w xs ys n i )

theorem native_constructorInput {m} (k a b : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constructorInputSentence k a b w xs ys n i)) := ZFReplay.replay (constructorInput_kernel_certificate k a b w xs ys n i )

theorem source_forestArity {m} (k l : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : Derives (Source.SetLanguage.ZF.at 0) (forestAritySentence k l w xs ys n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (forest l w ys n) (Context.add (forest k w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxForestArity.disjoint hZ k l hkl w xs ys n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem forestArity_kernel_certificate {m} (k l : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestAritySentence k l w xs ys n)) := TheoryTransport.sentence (source_forestArity k l w xs ys n hkl)

theorem native_forestArity {m} (k l : Nat) (w : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestAritySentence k l w xs ys n)) := ZFReplay.replay (forestArity_kernel_certificate k l w xs ys n hkl)

theorem source_nodeArity {m} (k l : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : Derives (Source.SetLanguage.ZF.at 0) (nodeAritySentence k l w a b xs ys n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (node l w b ys n) (Context.add (node k w a xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxNodeArity.disjoint hZ k l hkl w a b xs ys n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nodeArity_kernel_certificate {m} (k l : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nodeAritySentence k l w a b xs ys n)) := TheoryTransport.sentence (source_nodeArity k l w a b xs ys n hkl)

theorem native_nodeArity {m} (k l : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hkl : k ≠ l) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nodeAritySentence k l w a b xs ys n)) := ZFReplay.replay (nodeArity_kernel_certificate k l w a b xs ys n hkl)

theorem source_indexNatural {m} (bound : Bool) (w i n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (indexNaturalSentence bound w i n) := by
  apply close_derives
  apply Derives.impI
  exact SyntaxVariableDecode.index_natural bound w i n (.hyp (Or.inl rfl))

theorem indexNatural_kernel_certificate {m} (bound : Bool) (w i n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (indexNaturalSentence bound w i n)) := TheoryTransport.sentence (source_indexNatural bound w i n )

theorem native_indexNatural {m} (bound : Bool) (w i n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (indexNaturalSentence bound w i n)) := ZFReplay.replay (indexNatural_kernel_certificate bound w i n )

theorem source_indexInjective {m} (bound : Bool) (w i j n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (indexInjectiveSentence bound w i j n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w j n) (Context.add (code bound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxVariableDecode.index_eq hZ bound w i j n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem indexInjective_kernel_certificate {m} (bound : Bool) (w i j n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (indexInjectiveSentence bound w i j n)) := TheoryTransport.sentence (source_indexInjective bound w i j n )

theorem native_indexInjective {m} (bound : Bool) (w i j n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (indexInjectiveSentence bound w i j n)) := ZFReplay.replay (indexInjective_kernel_certificate bound w i j n )

theorem source_variableDecode {m} (bound : Bool) (w n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (variableDecodeSentence bound w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxVariableDecode.decode_iff hZ bound w n (.hyp (Or.inl rfl))

theorem variableDecode_kernel_certificate {m} (bound : Bool) (w n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableDecodeSentence bound w n)) := TheoryTransport.sentence (source_variableDecode bound w n )

theorem native_variableDecode {m} (bound : Bool) (w n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableDecodeSentence bound w n)) := ZFReplay.replay (variableDecode_kernel_certificate bound w n )

theorem source_indexFiber {m} (bound : Bool) (w n i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (indexFiberSentence bound w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxVariableDecode.fiber_at_code hZ bound w n i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem indexFiber_kernel_certificate {m} (bound : Bool) (w n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (indexFiberSentence bound w n i)) := TheoryTransport.sentence (source_indexFiber bound w n i )

theorem native_indexFiber {m} (bound : Bool) (w n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (indexFiberSentence bound w n i)) := ZFReplay.replay (indexFiber_kernel_certificate bound w n i )

theorem source_branchScope {m} (bound : Bool) (w l n i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (branchScopeSentence bound w l n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermBranches.iff_member hZ bound w l n i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem branchScope_kernel_certificate {m} (bound : Bool) (w l n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchScopeSentence bound w l n i)) := TheoryTransport.sentence (source_branchScope bound w l n i )

theorem native_branchScope {m} (bound : Bool) (w l n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchScopeSentence bound w l n i)) := ZFReplay.replay (branchScope_kernel_certificate bound w l n i )

theorem source_branchDecode {m} (bound : Bool) (w l n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (branchDecodeSentence bound w l n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermBranches.decode_iff hZ bound w l n (.hyp (Or.inl rfl))

theorem branchDecode_kernel_certificate {m} (bound : Bool) (w l n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchDecodeSentence bound w l n)) := TheoryTransport.sentence (source_branchDecode bound w l n )

theorem native_branchDecode {m} (bound : Bool) (w l n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchDecodeSentence bound w l n)) := ZFReplay.replay (branchDecode_kernel_certificate bound w l n )

theorem source_scope {m} (bound : Bool) (w b f n i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (scopeSentence bound w b f n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTerms.scope_iff hZ bound w b f n i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem scope_kernel_certificate {m} (bound : Bool) (w b f n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (scopeSentence bound w b f n i)) := TheoryTransport.sentence (source_scope bound w b f n i )

theorem native_scope {m} (bound : Bool) (w b f n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (scopeSentence bound w b f n i)) := ZFReplay.replay (scope_kernel_certificate bound w b f n i )

theorem source_termExists {m} (bound : Bool) (w b f i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (termExistsSentence bound w b f i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (scope bound w b f i) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTerms.exists_at hZ bound w b f i (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem termExists_kernel_certificate {m} (bound : Bool) (w b f i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termExistsSentence bound w b f i)) := TheoryTransport.sentence (source_termExists bound w b f i )

theorem native_termExists {m} (bound : Bool) (w b f i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termExistsSentence bound w b f i)) := ZFReplay.replay (termExists_kernel_certificate bound w b f i )

theorem source_termRange {m} (w b f n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (termRangeSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTerms.range hZ w b f n (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem termRange_kernel_certificate {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termRangeSentence w b f n)) := TheoryTransport.sentence (source_termRange w b f n )

theorem native_termRange {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termRangeSentence w b f n)) := ZFReplay.replay (termRange_kernel_certificate w b f n )

theorem source_termDecode {m} (w b f n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (termDecodeSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTerms.decode_iff hZ w b f n (.hyp (Or.inl rfl))

theorem termDecode_kernel_certificate {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termDecodeSentence w b f n)) := TheoryTransport.sentence (source_termDecode w b f n )

theorem native_termDecode {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termDecodeSentence w b f n)) := ZFReplay.replay (termDecode_kernel_certificate w b f n )

theorem source_branchExclusive {m} (w b f n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (branchExclusiveSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (branch false w f n) (Context.add (branch true w b n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermBranches.exclusive hZ w b f n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem branchExclusive_kernel_certificate {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchExclusiveSentence w b f n)) := TheoryTransport.sentence (source_branchExclusive w b f n )

theorem native_branchExclusive {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchExclusiveSentence w b f n)) := ZFReplay.replay (branchExclusive_kernel_certificate w b f n )

theorem source_decodedExclusive {m} (w b f n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (decodedExclusiveSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (decodedBranch false w f n) (Context.add (decodedBranch true w b n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.decoded_exclusive hZ w b f n (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decodedExclusive_kernel_certificate {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedExclusiveSentence w b f n)) := TheoryTransport.sentence (source_decodedExclusive w b f n )

theorem native_decodedExclusive {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedExclusiveSentence w b f n)) := ZFReplay.replay (decodedExclusive_kernel_certificate w b f n )

theorem source_rejectScope {m} (bound : Bool) (w b f n i : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (rejectScopeSentence bound w b f n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem i (limit bound b f)).neg) (Context.add (code bound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTerms.reject_scope hZ bound w b f n i (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectScope_kernel_certificate {m} (bound : Bool) (w b f n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectScopeSentence bound w b f n i)) := TheoryTransport.sentence (source_rejectScope bound w b f n i )

theorem native_rejectScope {m} (bound : Bool) (w b f n i : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectScopeSentence bound w b f n i)) := ZFReplay.replay (rejectScope_kernel_certificate bound w b f n i )

theorem source_rejectEmpty {m} (w b f n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (rejectEmptySentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact SyntaxTerms.reject_empty_contexts w b f n (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectEmpty_kernel_certificate {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectEmptySentence w b f n)) := TheoryTransport.sentence (source_rejectEmpty w b f n )

theorem native_rejectEmpty {m} (w b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectEmptySentence w b f n)) := ZFReplay.replay (rejectEmpty_kernel_certificate w b f n )

theorem source_rejectTag {m} (k label : Nat) (w b f n : Fin m) (xs : Fin k → Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : Derives (Source.SetLanguage.ZF.at 0) (rejectTagSentence k label w b f n xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor k label w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.other_tag hZ k label h0 h1 w b f n xs (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectTag_kernel_certificate {m} (k label : Nat) (w b f n : Fin m) (xs : Fin k → Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectTagSentence k label w b f n xs)) := TheoryTransport.sentence (source_rejectTag k label w b f n xs h0 h1)

theorem native_rejectTag {m} (k label : Nat) (w b f n : Fin m) (xs : Fin k → Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectTagSentence k label w b f n xs)) := ZFReplay.replay (rejectTag_kernel_certificate k label w b f n xs h0 h1)

theorem source_rejectFunction {m} (k : Nat) (w b f n : Fin m) (xs : Fin k → Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (rejectFunctionSentence k w b f n xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor k 2 w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.other_tag hZ k 2 (by decide) (by decide) w b f n xs (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectFunction_kernel_certificate {m} (k : Nat) (w b f n : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectFunctionSentence k w b f n xs)) := TheoryTransport.sentence (source_rejectFunction k w b f n xs )

theorem native_rejectFunction {m} (k : Nat) (w b f n : Fin m) (xs : Fin k → Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectFunctionSentence k w b f n xs)) := ZFReplay.replay (rejectFunction_kernel_certificate k w b f n xs )

theorem source_rejectArity {m} (k : Nat) (w a b f n : Fin m) (xs : Fin k → Fin m) (hk : k ≠ 1) : Derives (Source.SetLanguage.ZF.at 0) (rejectAritySentence k w a b f n xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (node k w a xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.wrong_arity hZ k hk w a b f n xs (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectArity_kernel_certificate {m} (k : Nat) (w a b f n : Fin m) (xs : Fin k → Fin m) (hk : k ≠ 1) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectAritySentence k w a b f n xs)) := TheoryTransport.sentence (source_rejectArity k w a b f n xs hk)

theorem native_rejectArity {m} (k : Nat) (w a b f n : Fin m) (xs : Fin k → Fin m) (hk : k ≠ 1) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectAritySentence k w a b f n xs)) := ZFReplay.replay (rejectArity_kernel_certificate k w a b f n xs hk)

theorem source_rejectScalar {m} (w a b f n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (rejectScalarSentence w a b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.scalar w a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.scalar hZ w a b f n (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectScalar_kernel_certificate {m} (w a b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectScalarSentence w a b f n)) := TheoryTransport.sentence (source_rejectScalar w a b f n )

theorem native_rejectScalar {m} (w a b f n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectScalarSentence w a b f n)) := ZFReplay.replay (rejectScalar_kernel_certificate w a b f n )

theorem source_branchEmpty {m} (bound : Bool) (w l n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (branchEmptySentence bound w l n) := by
  apply close_derives
  apply Derives.impI
  exact SyntaxTermBranches.empty bound w l n (.hyp (Or.inl rfl))

theorem branchEmpty_kernel_certificate {m} (bound : Bool) (w l n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchEmptySentence bound w l n)) := TheoryTransport.sentence (source_branchEmpty bound w l n )

theorem native_branchEmpty {m} (bound : Bool) (w l n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchEmptySentence bound w l n)) := ZFReplay.replay (branchEmpty_kernel_certificate bound w l n )

theorem source_rawRejectTag {m} (label : Nat) (w b f t p n : Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : Derives (Source.SetLanguage.ZF.at 0) (rawRejectTagSentence label w b f t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add (Formula.mem p w) (Context.add (SyntaxNumeralSyntax.numeral label t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.raw_tag hZ label h0 h1 w b f t p n (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rawRejectTag_kernel_certificate {m} (label : Nat) (w b f t p n : Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawRejectTagSentence label w b f t p n)) := TheoryTransport.sentence (source_rawRejectTag label w b f t p n h0 h1)

theorem native_rawRejectTag {m} (label : Nat) (w b f t p n : Fin m) (h0 : label ≠ 0) (h1 : label ≠ 1) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawRejectTagSentence label w b f t p n)) := ZFReplay.replay (rawRejectTag_kernel_certificate label w b f t p n h0 h1)

theorem source_rawRejectFunction {m} (w b f t p n : Fin m)  : Derives (Source.SetLanguage.ZF.at 0) (rawRejectFunctionSentence w b f t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add (Formula.mem p w) (Context.add (SyntaxNumeralSyntax.numeral 2 t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.raw_tag hZ 2 (by decide) (by decide) w b f t p n (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rawRejectFunction_kernel_certificate {m} (w b f t p n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawRejectFunctionSentence w b f t p n)) := TheoryTransport.sentence (source_rawRejectFunction w b f t p n )

theorem native_rawRejectFunction {m} (w b f t p n : Fin m)  : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawRejectFunctionSentence w b f t p n)) := ZFReplay.replay (rawRejectFunction_kernel_certificate w b f t p n )

def rawRejectUnknownTagSentence {m} (w b f t p n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem t w).imp ((Formula.mem p w).imp (((SyntaxNumeralSyntax.numeral 0 t).neg).imp (((SyntaxNumeralSyntax.numeral 1 t).neg).imp ((StructuralNodeSyntax.raw w t p n).imp ((term w b f n).neg))))))).close

theorem source_rawRejectUnknownTag {m} (w b f t p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawRejectUnknownTagSentence w b f t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add ((SyntaxNumeralSyntax.numeral 1 t).neg) (Context.add ((SyntaxNumeralSyntax.numeral 0 t).neg) (Context.add (Formula.mem p w) (Context.add (Formula.mem t w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  exact SyntaxTermReject.unknown_raw_tag hZ w b f t p n (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rawRejectUnknownTag_kernel_certificate {m} (w b f t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawRejectUnknownTagSentence w b f t p n)) := TheoryTransport.sentence (source_rawRejectUnknownTag w b f t p n)

theorem native_rawRejectUnknownTag {m} (w b f t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawRejectUnknownTagSentence w b f t p n)) := ZFReplay.replay (rawRejectUnknownTag_kernel_certificate w b f t p n)

end PPAC.Migration.Internal.ObjectSyntaxTerms
