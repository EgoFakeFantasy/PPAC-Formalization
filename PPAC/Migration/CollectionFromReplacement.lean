import PPAC.Migration.WitnessRankBounds

/-! 完整原Collection由源Replacement版ZF推导，保留任意关系、全部参数和内部集合量词。 -/
namespace PPAC.Migration.CollectionFromReplacement
open Source SourceAlgebra SourceLogic WitnessRankSyntax
open ReplacementPredicates (paramsUp)

theorem collects {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m)
    (hRank : Derives Γ (ObjectRankCover.rankSentence.rename Fin.elim0))
    (hMin : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence (predicate p)).rename Fin.elim0))
    (hBound : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement (matrix p)).rename Fin.elim0))
    (ht : Derives Γ (ReplacementPredicates.totalRelation p ρ a)) : Derives Γ (ReplacementPredicates.collects p ρ a) := by
  have htotal := WitnessRankFibers.total_least p ρ a hRank hMin ht
  have hc := WitnessRankCollection.exists_range p ρ a hRank hMin hRep ht
  let C := range p (paramsUp ρ) (Fin.last m) a.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hc
  apply Derives.exE (p := C) hc
  have hBoundC : Derives Ξ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hBound C
  have hExC : Derives Ξ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx C
  have hMemC : Derives Ξ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMem C
  have htC : Derives Ξ (ReplacementPredicates.total (matrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename] using under htotal C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  simpa only [Formula.raise, ReplacementPredicates.collects_rename] using
    WitnessRankBounds.collects_from_range p (paramsUp ρ) (Fin.last m) a.castSucc hBoundC hExC hMemC htC hC

theorem source_collection {n} (p : Formula (n+2)) :
    Derives (Source.SetLanguage.ZF.at 0) (CollectionSyntax.collection p) := by
  apply close_derives
  rw [ReplacementInstances.collection_core]
  apply Derives.allI
  rw [theory_at_raise]
  apply Derives.impI
  let M := ReplacementPredicates.totalRelation p Fin.castSucc (Fin.last n)
  let Δ := Context.add M (Source.SetLanguage.ZF.at (n+1))
  have hRank : Derives Δ (ObjectRankCover.rankSentence.rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at ObjectRankCover.source_rank (n+1)) M
  have hMin : Derives Δ ((ObjectOrdinalLeast.uniquenessSentence (predicate p)).rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at (ObjectOrdinalLeast.source_uniqueness (predicate p)) (n+1)) M
  have hBound : Derives Δ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at ObjectOrdinalUnion.source_ZF_strict (n+1)) M
  have hEx : Derives Δ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at ObjectCumulativeHierarchy.source_existence (n+1)) M
  have hMem : Derives Δ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) :=
    add (ObjectTransitiveCover.closed_at ObjectHierarchyAlgebra.source_membership (n+1)) M
  have hRep : Derives Δ ((Source.SetLanguage.replacement (matrix p)).rename Fin.elim0) :=
    add (.hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement (matrix p), rfl⟩) M
  exact collects p Fin.castSucc (Fin.last n) hRank hMin hBound hEx hMem hRep (.hyp (Or.inl rfl))

theorem kernel_certificate {n} (p : Formula (n+2)) :
    YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
      (Translation.sentence (CollectionSyntax.collection p)) := TheoryTransport.sentence (source_collection p)

theorem native_source_matrix {n} (p : Formula (n+2)) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (CollectionSyntax.collection p)) :=
  ZFReplay.replay (kernel_certificate p)

theorem native_project_matrix {n} (s : YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n) :
    YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
      (YesMetaZFC.SetTheory.Definitional.Project.fo_sentence (YesMetaZFC.SetTheory.Axioms.Schema.collection s)) :=
  YesMetaZFC.Logic.FirstOrder.Derives.iff_elim_right (CollectionSyntax.native_collection_equivalent s)
    (kernel_certificate (ProjectDecode.reverse s.body s.freeClosed))
end PPAC.Migration.CollectionFromReplacement
