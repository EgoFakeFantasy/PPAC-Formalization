import PPAC.Migration.Internal.StructuralListLengthFiber

/-! 实际列表长度、精确前缀、严格尾码归纳唯一性和真实唯一长度纤维的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListLength
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListLengthSyntax

def prefixTraceSentence : Source.Sentence := ((omega (0 : Fin 9)).imp ((Formula.mem 7 0).imp ((successor 3 7).imp ((trace 0 1 2 3 4 5 6).imp ((edge 5 7 8).imp (existsTrace 0 1 2 7 3 8)))))).close

def knownTailEdgeSentence : Source.Sentence := ((omega (0 : Fin 10)).imp ((Formula.mem 8 0).imp ((Formula.mem 9 0).imp ((successor 3 7).imp ((trace 0 1 2 3 4 5 6).imp ((consCode 0 8 9 6).imp (edge 5 7 9))))))).close

def nilEmptySentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((nilCode 0 1).imp ((hasLength 0 1 2).imp (empty 2)))).close

def consPredecessorSentence : Source.Sentence := ((omega (0 : Fin 5)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((consCode 0 1 2 3).imp ((hasLength 0 3 4).imp (predecessorLength 0 2 4)))))).close

def uniqueSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((hasLength 0 1 2).imp ((hasLength 0 1 3).imp (Formula.equal 2 3)))).close

def traceUniqueSentence : Source.Sentence := ((omega (0 : Fin 12)).imp ((trace 0 1 2 3 4 5 6).imp ((trace 0 7 8 9 10 11 6).imp (Formula.equal 3 9)))).close

def fiberSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((valid 0 1).imp (StructuralListLengthSyntax.fiber 0 1))).close

def rangeSentence : Source.Sentence := ((hasLength (0 : Fin 3) 1 2).imp ((Formula.mem 1 0).conj (.mem 2 0))).close

def existsSentence : Source.Sentence := ((valid (0 : Fin 2) 1).imp (existsLength 0 1)).close

theorem source_prefixTrace : Derives (Source.SetLanguage.ZF.at 0) prefixTraceSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 9 := (Context.add (edge 5 7 8) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (successor 3 7) (Context.add (Formula.mem 7 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 9))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 9
  exact StructuralListTracePrefix.exists_prefix_trace hZ 0 1 2 3 4 5 6 7 8
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem prefixTrace_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence prefixTraceSentence) := TheoryTransport.sentence source_prefixTrace

theorem native_prefixTrace : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence prefixTraceSentence) :=
  ZFReplay.replay prefixTrace_kernel_certificate

theorem source_knownTailEdge : Derives (Source.SetLanguage.ZF.at 0) knownTailEdgeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 10 := (Context.add (consCode 0 8 9 6) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (successor 3 7) (Context.add (Formula.mem 9 0) (Context.add (Formula.mem 8 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10
  exact StructuralListTerminal.known_tail_edge hZ 0 1 2 3 4 5 6 7 8 9
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem knownTailEdge_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence knownTailEdgeSentence) := TheoryTransport.sentence source_knownTailEdge

theorem native_knownTailEdge : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence knownTailEdgeSentence) :=
  ZFReplay.replay knownTailEdge_kernel_certificate

theorem source_nilEmpty : Derives (Source.SetLanguage.ZF.at 0) nilEmptySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (hasLength 0 1 2) (Context.add (nilCode 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListLengthRules.nil_empty hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem nilEmpty_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence nilEmptySentence) := TheoryTransport.sentence source_nilEmpty

theorem native_nilEmpty : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence nilEmptySentence) :=
  ZFReplay.replay nilEmpty_kernel_certificate

theorem source_consPredecessor : Derives (Source.SetLanguage.ZF.at 0) consPredecessorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := (Context.add (hasLength 0 3 4) (Context.add (consCode 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralListLengthRules.cons_predecessor hZ 0 1 2 3 4
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem consPredecessor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consPredecessorSentence) := TheoryTransport.sentence source_consPredecessor

theorem native_consPredecessor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence consPredecessorSentence) :=
  ZFReplay.replay consPredecessor_kernel_certificate

theorem source_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (hasLength 0 1 3) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListLengthUnique.unique hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  ZFReplay.replay unique_kernel_certificate

theorem source_traceUnique : Derives (Source.SetLanguage.ZF.at 0) traceUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 12 := (Context.add (trace 0 7 8 9 10 11 6) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 12))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 12
  exact StructuralListLengthFiber.trace_unique hZ 0 1 2 3 4 5 6 7 8 9 10 11
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem traceUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence traceUniqueSentence) := TheoryTransport.sentence source_traceUnique

theorem native_traceUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence traceUniqueSentence) :=
  ZFReplay.replay traceUnique_kernel_certificate

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListLengthFiber.unique_fiber hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence fiberSentence) :=
  ZFReplay.replay fiber_kernel_certificate

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  exact .conjI (StructuralListLengthBasic.code_member 0 1 2 (.hyp (Or.inl rfl))) (StructuralListLengthBasic.length_member 0 1 2 (.hyp (Or.inl rfl)))

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) :=
  ZFReplay.replay range_kernel_certificate

theorem source_exists : Derives (Source.SetLanguage.ZF.at 0) existsSentence := by
  apply close_derives
  apply Derives.impI
  exact StructuralListLengthBasic.exists_length 0 1
    (.hyp (Or.inl rfl))

theorem exists_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existsSentence) := TheoryTransport.sentence source_exists

theorem native_exists : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existsSentence) :=
  ZFReplay.replay exists_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralListLength
