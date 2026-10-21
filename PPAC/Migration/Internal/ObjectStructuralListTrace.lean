import PPAC.Migration.Internal.StructuralListDecode

/-! 全内部长度列表轨迹、精确Nil/Cons递归式与零码排除的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListTrace
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListDecodeSyntax

def baseSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((empty 1).imp ((successor 2 1).imp (existsTrace 0 1 2 1 2 2)))).close

def appendSentence : Source.Sentence := ((omega (0 : Fin 10)).imp ((Formula.mem 7 0).imp ((trace 0 1 2 3 4 5 6).imp ((consCode 0 7 6 8).imp ((successor 9 4).imp (existsTrace 0 1 2 4 9 8)))))).close

def nilValidSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((nilCode 0 1).imp (valid 0 1))).close

def consValidSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((valid 0 2).imp ((consCode 0 1 2 3).imp (valid 0 3))))).close

def rangeSentence : Source.Sentence := ((valid (0 : Fin 2) 1).imp (Formula.mem 1 0)).close

def recursiveSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((valid 0 1).iff (decomposition 0 1))).close

def consIffSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((consCode 0 1 2 3).imp ((valid 0 3).iff (valid 0 2)))))).close

def positiveSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((valid 0 1).imp ((empty 1).neg))).close

def zeroRejectedSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((empty 1).imp ((valid 0 1).neg))).close

def prefixSentence : Source.Sentence := ((omega (0 : Fin 9)).imp ((Formula.mem 7 0).imp ((successor 3 7).imp ((trace 0 1 2 3 4 5 6).imp ((edge 5 7 8).imp (valid 0 8)))))).close

theorem source_base : Derives (Source.SetLanguage.ZF.at 0) baseSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListTraceBase.exists_base hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem base_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence baseSentence) := TheoryTransport.sentence source_base

theorem native_base : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence baseSentence) :=
  ZFReplay.replay base_kernel_certificate

theorem source_append : Derives (Source.SetLanguage.ZF.at 0) appendSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 10 := (Context.add (successor 9 4) (Context.add (consCode 0 7 6 8) (Context.add (trace 0 1 2 3 4 5 6) (Context.add (Formula.mem 7 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10
  exact StructuralListTraceAppend.exists_append hZ 0 1 2 3 4 5 6 7 8 9
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem append_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence appendSentence) := TheoryTransport.sentence source_append

theorem native_append : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence appendSentence) :=
  ZFReplay.replay append_kernel_certificate

theorem source_nilValid : Derives (Source.SetLanguage.ZF.at 0) nilValidSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (nilCode 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListTraceBase.valid_nil hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem nilValid_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence nilValidSentence) := TheoryTransport.sentence source_nilValid

theorem native_nilValid : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence nilValidSentence) :=
  ZFReplay.replay nilValid_kernel_certificate

theorem source_consValid : Derives (Source.SetLanguage.ZF.at 0) consValidSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (consCode 0 1 2 3) (Context.add (valid 0 2) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListValidity.cons_valid hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem consValid_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consValidSentence) := TheoryTransport.sentence source_consValid

theorem native_consValid : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence consValidSentence) :=
  ZFReplay.replay consValid_kernel_certificate

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  exact StructuralListValidity.range 0 1
    (.hyp (Or.inl rfl))

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) :=
  ZFReplay.replay range_kernel_certificate

theorem source_recursive : Derives (Source.SetLanguage.ZF.at 0) recursiveSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 2 := (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListDecode.recursive_iff hZ 0 1
    (.hyp (Or.inl rfl))

theorem recursive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence recursiveSentence) := TheoryTransport.sentence source_recursive

theorem native_recursive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence recursiveSentence) :=
  ZFReplay.replay recursive_kernel_certificate

theorem source_consIff : Derives (Source.SetLanguage.ZF.at 0) consIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (consCode 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListDecode.cons_iff hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem consIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consIffSentence) := TheoryTransport.sentence source_consIff

theorem native_consIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence consIffSentence) :=
  ZFReplay.replay consIff_kernel_certificate

theorem source_positive : Derives (Source.SetLanguage.ZF.at 0) positiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListDecode.positive hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem positive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence positiveSentence) := TheoryTransport.sentence source_positive

theorem native_positive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence positiveSentence) :=
  ZFReplay.replay positive_kernel_certificate

theorem source_zeroRejected : Derives (Source.SetLanguage.ZF.at 0) zeroRejectedSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListDecode.zero_rejected hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem zeroRejected_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroRejectedSentence) := TheoryTransport.sentence source_zeroRejected

theorem native_zeroRejected : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroRejectedSentence) :=
  ZFReplay.replay zeroRejected_kernel_certificate

theorem source_prefix : Derives (Source.SetLanguage.ZF.at 0) prefixSentence := by
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
  exact StructuralListTracePrefix.valid_prefix hZ 0 1 2 3 4 5 6 7 8
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem prefix_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence prefixSentence) := TheoryTransport.sentence source_prefix

theorem native_prefix : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence prefixSentence) :=
  ZFReplay.replay prefix_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralListTrace
