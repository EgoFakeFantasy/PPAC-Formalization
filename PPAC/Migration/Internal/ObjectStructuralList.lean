import PPAC.Migration.Internal.StructuralConsUnique

/-! 原Nil/Cons构造器及零叶封装值的完整对象ZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralList
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax

def nilValueSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((empty 1).imp ((successor 2 1).imp ((nilCode 0 3).iff (.equal 3 2))))).close

def nilFiberSentence : Source.Sentence := ((omega (0 : Fin 1)).imp (fiberNil 0)).close

def consTagSentence : Source.Sentence := ((empty (1 : Fin 6)).imp ((successor 2 1).imp ((consCode 0 3 4 5).iff (consAt 0 2 3 4 5)))).close

def consFiberSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp (fiberCons 0 1 2)))).close

def closureSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((consCode 0 1 2 3).imp ((Formula.mem 3 0).conj (empty 3).neg))).close

def boundsSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((consCode 0 1 2 3).imp ((Formula.mem 1 3).conj (.mem 2 3)))))).close

def injectiveSentence : Source.Sentence := ((omega (0 : Fin 6)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 3 0).imp ((Formula.mem 4 0).imp ((consCode 0 1 2 5).imp ((consCode 0 3 4 5).imp ((Formula.equal 1 3).conj (.equal 2 4))))))))).close

def disjointSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((nilCode 0 3).imp ((consCode 0 1 2 3).imp (Formula.bot)))).close

def leafZeroSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((empty 1).imp ((successor 2 1).imp ((successor 3 2).imp ((nilCode 0 2).conj (StructuralNodeSyntax.raw 0 1 2 3)))))).close

theorem source_nilValue : Derives (Source.SetLanguage.ZF.at 0) nilValueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralNil.value_iff hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem nilValue_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence nilValueSentence) := TheoryTransport.sentence source_nilValue

theorem native_nilValue : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence nilValueSentence) :=
  ZFReplay.replay nilValue_kernel_certificate

theorem source_nilFiber : Derives (Source.SetLanguage.ZF.at 0) nilFiberSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 1 := (Context.add (omega 0) (Source.SetLanguage.ZF.at 1))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 1
  exact StructuralNil.unique_fiber hZ 0
    (.hyp (Or.inl rfl))

theorem nilFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence nilFiberSentence) := TheoryTransport.sentence source_nilFiber

theorem native_nilFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence nilFiberSentence) :=
  ZFReplay.replay nilFiber_kernel_certificate

theorem source_consTag : Derives (Source.SetLanguage.ZF.at 0) consTagSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (successor 2 1) (Context.add (empty 1) (Source.SetLanguage.ZF.at 6)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralConsCore.tag_iff hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem consTag_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consTagSentence) := TheoryTransport.sentence source_consTag

theorem native_consTag : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence consTagSentence) :=
  ZFReplay.replay consTag_kernel_certificate

theorem source_consFiber : Derives (Source.SetLanguage.ZF.at 0) consFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralConsUnique.unique_fiber hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem consFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consFiberSentence) := TheoryTransport.sentence source_consFiber

theorem native_consFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence consFiberSentence) :=
  ZFReplay.replay consFiber_kernel_certificate

theorem source_closure : Derives (Source.SetLanguage.ZF.at 0) closureSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (consCode 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact .conjI (StructuralConsCore.range hZ 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))) (StructuralConsCore.positive 0 1 2 3 (.hyp (Or.inl rfl)))

theorem closure_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence closureSentence) := TheoryTransport.sentence source_closure

theorem native_closure : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence closureSentence) :=
  ZFReplay.replay closure_kernel_certificate

theorem source_bounds : Derives (Source.SetLanguage.ZF.at 0) boundsSentence := by
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
  exact StructuralConsCore.components hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem bounds_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence boundsSentence) := TheoryTransport.sentence source_bounds

theorem native_bounds : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence boundsSentence) :=
  ZFReplay.replay bounds_kernel_certificate

theorem source_injective : Derives (Source.SetLanguage.ZF.at 0) injectiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (consCode 0 3 4 5) (Context.add (consCode 0 1 2 5) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralConsUnique.injective hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem injective_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence injectiveSentence) := TheoryTransport.sentence source_injective

theorem native_injective : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence injectiveSentence) :=
  ZFReplay.replay injective_kernel_certificate

theorem source_disjoint : Derives (Source.SetLanguage.ZF.at 0) disjointSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (consCode 0 1 2 3) (Context.add (nilCode 0 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralConsUnique.disjoint hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem disjoint_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence disjointSentence) := TheoryTransport.sentence source_disjoint

theorem native_disjoint : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence disjointSentence) :=
  ZFReplay.replay disjoint_kernel_certificate

theorem source_leafZero : Derives (Source.SetLanguage.ZF.at 0) leafZeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (successor 3 2) (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact .conjI (StructuralNil.at_unit hZ 0 1 2 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))))
    (StructuralNil.leaf_zero hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))

theorem leafZero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leafZeroSentence) := TheoryTransport.sentence source_leafZero

theorem native_leafZero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leafZeroSentence) :=
  ZFReplay.replay leafZero_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralList
