import PPAC.Migration.HierarchyLayerZero

/-! 每个内部原序数的幂集并递归层值实际存在唯一；未假定秩覆盖或层代数性质。 -/
namespace PPAC.Migration.ObjectCumulativeHierarchy
open Source SourceAlgebra SourceLogic OrdinalSyntax HierarchyLayerSyntax

def existenceSentence : Source.Sentence := ((ordinal (0 : Fin 1)).imp (layerExists 0)).close

def uniquenessSentence : Source.Sentence := ((ordinal (0 : Fin 1)).imp (layerFiber 0)).close

def equalitySentence : Source.Sentence := ((ordinal (0 : Fin 3)).imp ((layer 0 1).imp ((layer 0 2).imp (.equal 1 2)))).close

def zeroSentence : Source.Sentence := ((OmegaSyntax.empty (0 : Fin 2)).imp ((layer 0 1).imp (OmegaSyntax.empty 1))).close

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact HierarchyLayerZero.layer_empty 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := by
  apply close_derives
  apply Derives.impI
  have hh := ObjectTransitiveCover.closed_at HierarchyRecursion.source_existence 1
  exact HierarchyLayerExistence.exists_layer (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 1) _)
    0 (add hh _) (.hyp (Or.inl rfl))

theorem source_uniqueness : Derives (Source.SetLanguage.ZF.at 0) uniquenessSentence := by
  apply close_derives
  apply Derives.impI
  let M := ordinal (0 : Fin 1)
  let Δ := Context.add M (Source.SetLanguage.ZF.at 1)
  have hA : OrdinalRecursionContext.Evidence Δ := OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 1) M
  have hOrd : Derives Δ M := .hyp (Or.inl rfl)
  have hh := ObjectTransitiveCover.closed_at HierarchyRecursion.source_existence 1
  have hd := ObjectTransitiveCover.closed_at ObjectPowerUnion.source_ZF_deterministic 1
  have hx := HierarchyLayerExistence.exists_layer hA (0 : Fin 1) (add hh M) hOrd
  exact HierarchyLayerUnique.fiber_of_exists hA 0 (HierarchyLayerUnique.deterministic_at (add hd M)) hOrd hx

theorem source_equality : Derives (Source.SetLanguage.ZF.at 0) equalitySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have hd := ObjectTransitiveCover.closed_at ObjectPowerUnion.source_ZF_deterministic 3
  exact HierarchyLayerUnique.layers_unique
    (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.add (OrdinalRecursionContext.source_ZF 3) _) _) _)
    0 1 2 (HierarchyLayerUnique.deterministic_at (add (add (add hd _) _) _))
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ZFReplay.replay existence_kernel_certificate

theorem uniqueness_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence uniquenessSentence) := TheoryTransport.sentence source_uniqueness

theorem native_uniqueness : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ZFReplay.replay uniqueness_kernel_certificate

theorem equality_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence equalitySentence) := TheoryTransport.sentence source_equality

theorem native_equality : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence equalitySentence) :=
  ZFReplay.replay equality_kernel_certificate
theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate
end PPAC.Migration.ObjectCumulativeHierarchy
