import PPAC.Migration.LayerCoverMembership

/-! 全部内部集合的实际层覆盖、实际唯一秩及成员覆盖，均有原核闭句证书。 -/
namespace PPAC.Migration.ObjectRankCover
open Source SourceAlgebra SourceLogic OrdinalSyntax LayerCoverSyntax LayerRankSyntax

def coverSentence : Source.Sentence := (cover (0 : Fin 1)).close

def rankSentence : Source.Sentence := (fiber (0 : Fin 1)).close

def memberSentence : Source.Sentence := (memberCover (0 : Fin 1)).close

def rangeSentence : Source.Sentence := (rangeExists (0 : Fin 1)).close

def equalitySentence : Source.Sentence := ((rank (0 : Fin 3) 1).imp ((rank 0 2).imp (.equal 1 2))).close

def propertySentence : Source.Sentence := ((rank (0 : Fin 2) 1).imp (atIndex 0 1)).close

theorem source_cover : Derives (Source.SetLanguage.ZF.at 0) coverSentence := by
  have hUnique := ObjectTransitiveCover.closed_at (ObjectOrdinalLeast.source_uniqueness containsMatrix) 0
  have hBound := ObjectTransitiveCover.closed_at ObjectOrdinalUnion.source_ZF_strict 0
  have hEx := ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_existence 0
  have hMem := ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_membership 0
  have hRep : Derives (Source.SetLanguage.ZF.at 0) ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩
  have hSep : Derives (Source.SetLanguage.ZF.at 0) ((Source.SetLanguage.separation coverMatrix.neg).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation coverMatrix.neg, rfl⟩
  have hFnd : Derives (Source.SetLanguage.ZF.at 0) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  have hTC := ObjectTransitiveCover.closed_at ObjectTransitiveCover.source_cover 0
  have hall := LayerCoverInduction.all_covers hUnique hBound hEx hMem hRep hSep hFnd hTC
  have h0 : Fin.last 0 = (0 : Fin 1) := rfl
  simpa only [coverSentence, Formula.close, SetInductionSyntax.holds, cover_pred, h0] using hall

theorem cover_at {m} {Γ : Context m} (x : Fin m) (hc : Derives Γ (coverSentence.rename Fin.elim0)) : Derives Γ (cover x) := by
  have hi := specialize_close (cover (0 : Fin 1)) (fun _ => x) hc
  simpa only [cover_rename] using hi

theorem all_members {m} {Γ : Context m} (x : Fin m) (hc : Derives Γ (coverSentence.rename Fin.elim0)) :
    Derives Γ (membersCovered x) := by
  apply Derives.allI
  have hc' : Derives (Context.image Formula.raise Γ) (coverSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  exact cover_at (Fin.last m) (add hc' _)

theorem source_rank : Derives (Source.SetLanguage.ZF.at 0) rankSentence := by
  apply close_derives
  have hUnique := ObjectTransitiveCover.closed_at (ObjectOrdinalLeast.source_uniqueness containsMatrix) 1
  have hc := ObjectTransitiveCover.closed_at source_cover 1
  exact LayerCoverClosedInstances.rank_fiber 0 hUnique (cover_at 0 hc)

theorem source_member : Derives (Source.SetLanguage.ZF.at 0) memberSentence := by
  apply close_derives
  have hc := ObjectTransitiveCover.closed_at source_cover 1
  have hEx := ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_existence 1
  have hSucc := ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_successor 1
  have hp : Derives (Source.SetLanguage.ZF.at 1) (Source.SetLanguage.pairing.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  have hu : Derives (Source.SetLanguage.ZF.at 1) (Source.SetLanguage.union.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  have hf : Derives (Source.SetLanguage.ZF.at 1) (Source.SetLanguage.foundation.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  exact LayerCoverMembership.from_cover 0 hp hu hf hEx hSucc (cover_at 0 hc)

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  have hUnique := ObjectTransitiveCover.closed_at (ObjectOrdinalLeast.source_uniqueness containsMatrix) 1
  have hc := ObjectTransitiveCover.closed_at source_cover 1
  have hr : Derives (Source.SetLanguage.ZF.at 1) ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩
  exact LayerRankCollection.exists_range 0 hUnique hr (all_members 0 hc)

theorem source_equality : Derives (Source.SetLanguage.ZF.at 0) equalitySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalLeastLogic.least_values_equal containsMatrix (fun _ => (0 : Fin 3)) 1 2
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_property : Derives (Source.SetLanguage.ZF.at 0) propertySentence := by
  apply close_derives
  apply Derives.impI
  exact rank_property 0 1 (.hyp (Or.inl rfl))

theorem cover_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence coverSentence) := TheoryTransport.sentence source_cover

theorem native_cover : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence coverSentence) :=
  ZFReplay.replay cover_kernel_certificate

theorem rank_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence rankSentence) := TheoryTransport.sentence source_rank

theorem native_rank : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rankSentence) :=
  ZFReplay.replay rank_kernel_certificate

theorem member_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence memberSentence) := TheoryTransport.sentence source_member

theorem native_member : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence memberSentence) :=
  ZFReplay.replay member_kernel_certificate

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) :=
  ZFReplay.replay range_kernel_certificate

theorem equality_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence equalitySentence) := TheoryTransport.sentence source_equality

theorem native_equality : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence equalitySentence) :=
  ZFReplay.replay equality_kernel_certificate

theorem property_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence propertySentence) := TheoryTransport.sentence source_property

theorem native_property : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence propertySentence) :=
  ZFReplay.replay property_kernel_certificate
end PPAC.Migration.ObjectRankCover
