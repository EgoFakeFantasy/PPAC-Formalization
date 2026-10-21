import PPAC.Migration.Internal.GodelPairInjective

/-! 原Gödel配数的全内部自然闭句及原YesMetaZFC推导核证书。 -/
namespace PPAC.Migration.Internal.ObjectGodelPair
open Source SourceAlgebra SourceLogic OmegaSyntax GodelPairSyntax GodelPairBandSyntax
open NaturalAdditionBounds (below)

def fiberSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp (GodelPairSyntax.fiber 0 1 2)))).close

def closureSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((code 0 1 2 3).imp (Formula.mem 3 0))).close

def valueUniqueSentence : Source.Sentence := ((omega (0 : Fin 5)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((code 0 1 2 3).imp ((code 0 1 2 4).imp (Formula.equal 3 4)))))).close

def componentsSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((code 0 1 2 3).imp ((below 1 3).conj (below 2 3)))))).close

def injectiveSentence : Source.Sentence := ((omega (0 : Fin 6)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 3 0).imp ((Formula.mem 4 0).imp ((code 0 1 2 5).imp ((code 0 3 4 5).imp ((Formula.equal 1 3).conj (.equal 2 4))))))))).close

def lowerBandSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 1 2).imp ((lower 0 1 2 3).imp (band 0 2 3)))))).close

def upperBandSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp (((Formula.mem 1 2).neg).imp ((upper 0 1 2 3).imp (band 0 1 3)))))).close

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
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
  exact GodelPairCore.exists_unique hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence fiberSentence) :=
  ZFReplay.replay fiber_kernel_certificate

theorem source_closure : Derives (Source.SetLanguage.ZF.at 0) closureSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (code 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact GodelPairCore.range hZ 0 1 2 3
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem closure_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence closureSentence) := TheoryTransport.sentence source_closure

theorem native_closure : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence closureSentence) :=
  ZFReplay.replay closure_kernel_certificate

theorem source_valueUnique : Derives (Source.SetLanguage.ZF.at 0) valueUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := (Context.add (code 0 1 2 4) (Context.add (code 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact GodelPairCore.unique hZ 0 1 2 3 4
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem valueUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence valueUniqueSentence) := TheoryTransport.sentence source_valueUnique

theorem native_valueUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence valueUniqueSentence) :=
  ZFReplay.replay valueUnique_kernel_certificate

theorem source_components : Derives (Source.SetLanguage.ZF.at 0) componentsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (code 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact GodelPairBounds.components hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem components_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence componentsSentence) := TheoryTransport.sentence source_components

theorem native_components : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence componentsSentence) :=
  ZFReplay.replay components_kernel_certificate

theorem source_injective : Derives (Source.SetLanguage.ZF.at 0) injectiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (code 0 3 4 5) (Context.add (code 0 1 2 5) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact GodelPairInjective.injective hZ 0 1 2 3 4 5
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

theorem source_lowerBand : Derives (Source.SetLanguage.ZF.at 0) lowerBandSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (lower 0 1 2 3) (Context.add (Formula.mem 1 2) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact GodelPairBands.lower_band hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem lowerBand_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence lowerBandSentence) := TheoryTransport.sentence source_lowerBand

theorem native_lowerBand : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence lowerBandSentence) :=
  ZFReplay.replay lowerBand_kernel_certificate

theorem source_upperBand : Derives (Source.SetLanguage.ZF.at 0) upperBandSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (upper 0 1 2 3) (Context.add ((Formula.mem 1 2).neg) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact GodelPairBands.upper_band hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem upperBand_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence upperBandSentence) := TheoryTransport.sentence source_upperBand

theorem native_upperBand : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence upperBandSentence) :=
  ZFReplay.replay upperBand_kernel_certificate

end PPAC.Migration.Internal.ObjectGodelPair
