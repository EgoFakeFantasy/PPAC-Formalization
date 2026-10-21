import PPAC.Migration.HierarchyFamilyUnion

/-! 内部零/极限层并公式、实际早层精确族及原UnionOf的闭句证书。 -/
namespace PPAC.Migration.ObjectHierarchyLimit
open Source SourceAlgebra SourceLogic OrdinalSyntax HierarchyLayerSyntax
open HierarchyLimitSyntax HierarchyFamilySyntax

def equationSentence : Source.Sentence := ((limitIndex (0 : Fin 2)).imp
  ((layer 0 1).imp (unionEquation 0 1))).close

def rangeSentence : Source.Sentence := ((ordinal (0 : Fin 1)).imp (rangeExists 0)).close

def rangeEqualitySentence : Source.Sentence := ((range (1 : Fin 3) 0).imp ((range 2 0).imp (.equal 1 2))).close

def unionSentence : Source.Sentence := ((limitIndex (0 : Fin 3)).imp ((layer 0 1).imp
  ((range 2 0).imp (InsertSyntax.unionOf 1 2)))).close

def assembledSentence : Source.Sentence := ((limitIndex (0 : Fin 2)).imp
  ((layer 0 1).imp (assembled 0 1))).close

def zeroSentence : Source.Sentence := ((OmegaSyntax.empty (0 : Fin 1)).imp (limitIndex 0)).close

theorem closed_empty {m} {Γ : Context m} (a : Fin m) (hz : Derives Γ (OmegaSyntax.empty a)) : Derives Γ (closedSuccessor a) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (OmegaSyntax.empty a.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact .botE (.impE (add (OmegaSyntax.empty_at a.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  have hf : Derives (Source.SetLanguage.ZF.at 1) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  have hz : Derives (Context.add (OmegaSyntax.empty 0) (Source.SetLanguage.ZF.at 1)) (OmegaSyntax.empty 0) := .hyp (Or.inl rfl)
  exact .conjI (OrdinalEmpty.ordinal 0 (add hf _) hz) (closed_empty 0 hz)

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  have hu := ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_uniqueness 1
  have hr : Derives (Source.SetLanguage.ZF.at 1) ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩
  exact HierarchyLayerCollection.exists_range 0 (add hu _) (add hr _) (.hyp (Or.inl rfl))

theorem source_rangeEquality : Derives (Source.SetLanguage.ZF.at 0) rangeEqualitySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (Source.SetLanguage.ZF.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  exact HierarchyLayerCollection.range_unique 1 2 0 (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_equation : Derives (Source.SetLanguage.ZF.at 0) equationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (layer 0 1) (Context.add (limitIndex 0) (Source.SetLanguage.ZF.at 2)))
  have hEx : Derives Δ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_existence 2) _) _)
  have hSucc : Derives Δ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_successor 2) _) _)
  have hMem : Derives Δ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_membership 2) _) _)
  exact HierarchyLimitMembership.layer_union_equation 0 1 hEx hSucc hMem
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_union : Derives (Source.SetLanguage.ZF.at 0) unionSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (range 2 0) (Context.add (layer 0 1) (Context.add (limitIndex 0) (Source.SetLanguage.ZF.at 3))))
  have hEx : Derives Δ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_existence 3) _) _) _)
  have hSucc : Derives Δ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_successor 3) _) _) _)
  have hMem : Derives Δ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_membership 3) _) _) _)
  have heq := HierarchyLimitMembership.layer_union_equation 0 1 hEx hSucc hMem
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl)))
  exact HierarchyFamilyUnion.union_of_equation 2 0 1 (.hyp (Or.inl rfl)) heq

theorem source_assembled : Derives (Source.SetLanguage.ZF.at 0) assembledSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (layer 0 1) (Context.add (limitIndex 0) (Source.SetLanguage.ZF.at 2)))
  have hEx : Derives Δ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_existence 2) _) _)
  have hSucc : Derives Δ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_successor 2) _) _)
  have hMem : Derives Δ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := (SourceLogic.add (SourceLogic.add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_membership 2) _) _)
  have hl : Derives Δ (limitIndex 0) := .hyp (Or.inr (Or.inl rfl))
  have heq := HierarchyLimitMembership.layer_union_equation 0 1 hEx hSucc hMem hl (.hyp (Or.inl rfl))
  have hUnique : Derives Δ (ObjectCumulativeHierarchy.uniquenessSentence.rename Fin.elim0) :=
    add (add (ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_uniqueness 2) _) _
  have hr : Derives Δ ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    add (add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩) _) _
  have hx := HierarchyLayerCollection.exists_range 0 hUnique hr (.conjL hl)
  exact HierarchyFamilyUnion.exists_union 0 1 hx heq

theorem equation_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence equationSentence) := TheoryTransport.sentence source_equation

theorem native_equation : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence equationSentence) :=
  ZFReplay.replay equation_kernel_certificate

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) :=
  ZFReplay.replay range_kernel_certificate

theorem rangeEquality_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence rangeEqualitySentence) := TheoryTransport.sentence source_rangeEquality

theorem native_rangeEquality : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeEqualitySentence) :=
  ZFReplay.replay rangeEquality_kernel_certificate

theorem union_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence unionSentence) := TheoryTransport.sentence source_union

theorem native_union : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence unionSentence) :=
  ZFReplay.replay union_kernel_certificate

theorem assembled_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence assembledSentence) := TheoryTransport.sentence source_assembled

theorem native_assembled : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence assembledSentence) :=
  ZFReplay.replay assembled_kernel_certificate

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate
end PPAC.Migration.ObjectHierarchyLimit
