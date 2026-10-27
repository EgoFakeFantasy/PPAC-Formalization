/- Pinned MergerCones.Word.wordHeightCost:523, old_missed_costs:543 and
old_cost_supremum:563, consumed by mergerHeightCost:580 and MergerData.
Pure forall21 native-ZF certificate constructs the SAME 14 actual weight
objects plus full strict ACTUAL supremum margins and ALL old cap preservation.
All internal/nonstandard lengths retained. Final object Con remains open. -/
import PPAC.Migration.ConstructionMergerWordHeightCost

namespace PPAC.Migration.ConstructionMergerWordHeightCostSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 21
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 5)) (.imp (.mem (.bound
    5) (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 21) (1 : Fin 21)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 21) (1 : Fin 21) (2 : Fin 21)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 21) (8 : Fin 21) (7 : Fin 21) (7 : Fin 21)) (.imp
    (Project.Formula.isOrdinalOne (.bound 7)) (.imp (ConstructionRealCuts.principal (0 : Fin 21) (1 : Fin
    21) (8 : Fin 21) (9 : Fin 21)) (.imp (ConstructionProbeRaw.carrier (0 : Fin 21) (3     : Fin 21) (4 :
    Fin 21) (6 : Fin 21)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo     (10 : Fin 21) (3
    : Fin 21) (2 : Fin 21))) (.imp (ProjectSyntax.encode id     (Source.SetLanguage.mapsTo (11 : Fin 21)
    (3 : Fin 21) (2 : Fin 21))) (.imp (ConstructionCutWeights.rangeBound (9 : Fin 21) (10 : Fin 21))
    (.imp (ConstructionProbeGateCap.bounds (9 : Fin 21) (11 : Fin 21)) (.imp
    (ConstructionMergerHeightCost.copiesHeightCost (0 : Fin 21) (1 : Fin 21) (2 : Fin 21) (3 : Fin 21) (4
    : Fin 21) (16 : Fin 21) (9 : Fin 21) (12 : Fin 21) (13 : Fin 21)) (.imp
    (ConstructionMergerWordAction.actionTable (0 : Fin 21) (3 : Fin 21) (4 : Fin 21) (5 : Fin 21) (15 :
    Fin 21) (16 : Fin 21) (17 : Fin 21)) (.imp (ConstructionMergerWordProduct.laws (0 : Fin 21) (3 : Fin
    21) (4 : Fin 21) (5 : Fin 21) (17 : Fin 21) (18 : Fin 21)) (.imp
    (ConstructionProbeLetters.representatives (6 : Fin 21) (6 : Fin 21) (19 : Fin 21)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (18 : Fin 21) (19 : Fin 21) (6 : Fin 21))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (6 : Fin 21) (18 : Fin 21) (20 : Fin
    21))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (6 : Fin 21) (18 : Fin 21) (20 :
    Fin 21))) (.imp (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 21) (1 : Fin 21) (3 : Fin
    21) (15 : Fin 21) (10 : Fin 21) (11 : Fin 21)) (.imp (.mem (.bound 14) (.bound 3)) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.conj (.conj (.conj (ConstructionBaseWeights.digits     (14 : Fin 35)
    (21 : Fin 35) (13 : Fin 35) (12 : Fin 35)) (.conj (Project.Formula.isSuccessor     (.bound 11)
    (.bound 12)) (.conj (.mem (.bound 11) (.bound 14)) (.conj     (Project.Formula.isSuccessor (.bound
    10) (.bound 11)) (.conj (Project.Formula.isSuccessor     (.bound 9) (.bound 10)) (.conj
    (Project.Formula.isSuccessor (.bound 8) (.bound 9)) (.conj     (Project.Formula.isSuccessor (.bound
    7) (.bound 8)) (.conj (.mem (.bound 7) (.bound 14)) (.conj     (ConstructionCutDivision.value (14 :
    Fin 35) (15 : Fin 35) (11 : Fin 35) (23 : Fin 35) (6 : Fin 35)) (.conj (ConstructionCutDivision.value
    (14 : Fin 35) (15 : Fin 35) (7 : Fin 35) (23 : Fin 35) (5 : Fin 35)) (.conj (.mem (.bound 6) (.bound
    16)) (.conj (.mem (.bound 5) (.bound 16))     (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (4 : Fin 35) (18 : Fin 35) (16 : Fin 35))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (3 : Fin 35) (18 : Fin 35) (16     : Fin 35))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 35) (18 : Fin 35) (16 : Fin 35))) (.conj
    (ConstructionMergerWordParameters.graph 0 (14 : Fin 35) (15 : Fin 35)     (11 : Fin 35) (23 : Fin 35)
    (6 : Fin 35) (5 : Fin 35) (18 : Fin 35) (26 : Fin 35) (27 : Fin 35)     (4 : Fin 35)) (.conj
    (ConstructionMergerWordParameters.graph 1 (14 : Fin 35) (15 : Fin 35) (11 :     Fin 35) (23 : Fin 35)
    (6 : Fin 35) (5 : Fin 35) (18 : Fin 35) (26 : Fin 35) (27 : Fin 35) (3 :     Fin 35)) (.conj
    (ConstructionMergerWordParameters.graph 2 (14 : Fin 35) (15 : Fin 35) (11 : Fin 35) (23 : Fin 35) (6
    : Fin 35) (5 : Fin 35) (18 : Fin 35) (26 : Fin 35) (27 : Fin 35) (2 : Fin 35)) (.conj (.forallE
    (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id     (Source.SetLanguage.edge (8 : Fin
    39) (3 : Fin 39) (2 : Fin 39))) (.imp (ProjectSyntax.encode id     (Source.SetLanguage.edge (7 : Fin
    39) (3 : Fin 39) (1 : Fin 39))) (.imp (ProjectSyntax.encode id     (Source.SetLanguage.edge (6 : Fin
    39) (3 : Fin 39) (0 : Fin 39)))     (ConstructionMergerWordParameters.recipe (18 : Fin 39) (19 : Fin
    39) (15 : Fin 39) (27 : Fin 39)     (10 : Fin 39) (9 : Fin 39) (30 : Fin 39) (31 : Fin 39) (3 : Fin
    39) (2 : Fin 39) (1 : Fin 39) (0     : Fin 39))))))))) (.conj (ConstructionCutWeights.rangeBound (23
    : Fin 35) (4 : Fin 35)) (.conj     (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (5 : Fin 37) (1 :     Fin 37) (0 : Fin 37))) (.existsE (.mem (.bound 0)
    (.bound 1))))))     (ConstructionProbeGateCap.bounds (5 : Fin 35) (2 : Fin 35)))))))))))))))))))))))
    (.conj     (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 35) (20 : Fin 35) (16 : Fin
    35)))     (.conj (ConstructionProbeHeightFoldSyntax.laws (14 : Fin 35) (17 : Fin 35) (18 : Fin 35)
    (19 :     Fin 35) (20 : Fin 35) (15 : Fin 35) (24 : Fin 35) (4 : Fin 35) (3 : Fin 35) (1 : Fin 35))
    (.conj     (ConstructionMergerWordHeights.literalLaws (14 : Fin 35) (15 : Fin 35) (17 : Fin 35) (18 :
    Fin 35) (19 : Fin 35) (23 : Fin 35) (24 : Fin 35) (4 : Fin 35) (1 : Fin 35)) (.conj
    (ConstructionCutWeights.rangeBound (23 : Fin 35) (1 : Fin 35)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 35) (20 : Fin 35) (16 : Fin 35))) (.conj (.forallE (.forallE
    (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin 37) (1 : Fin 37) (0 : Fin 37)))
    (.conj (.mem (.bound 1) (.bound 22)) (ConstructionMergerWordCosts.value (16 : Fin 37) (17 : Fin 37)
    (19 : Fin 37) (20 : Fin 37) (21 : Fin 37) (25 : Fin 37) (3 : Fin 37) (27 : Fin 37) (4 : Fin 37) (1 :
    Fin 37) (0 : Fin 37)))))) (.conj (ConstructionProbeGateCap.bounds (23 : Fin 35) (0 :     Fin 35))
    (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old (22 : Fin 38) (20     : Fin 38)
    (2 : Fin 38) (1 : Fin 38)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (3     : Fin 38)
    (1 : Fin 38) (0 : Fin 38))) (ProjectSyntax.encode id (Source.SetLanguage.edge (28 :     Fin 38) (2 :
    Fin 38) (0 : Fin 38)))))))) (.forallE (.forallE (.forallE (.forallE (.imp
    (ConstructionProbeRaw.cons (18 : Fin 39) (21 : Fin 39) (22 : Fin 39) (3 : Fin 39) (2 : Fin 39)     (1
    : Fin 39)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin 39) (1 : Fin 39)     (0 :
    Fin 39))) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id     (Source.SetLanguage.edge
    (8 : Fin 42) (5 : Fin 42) (2 : Fin 42))) (.conj     (ConstructionCutDifference.value (21 : Fin 42)
    (22 : Fin 42) (2 : Fin 42) (30 : Fin 42) (1 : Fin 42)) (.conj (ConstructionCutAddition.sumCut (21 :
    Fin 42) (22 : Fin 42) (2 : Fin 42) (1 : Fin 42) (30 : Fin 42)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (9 : Fin 42) (6 :     Fin 42) (0 : Fin 42))) (ConstructionCutProduct.value
    (21 : Fin 42) (22 : Fin 42) (1 : Fin 42) (0     : Fin 42) (3 : Fin 42)))))))))))))))))))))))) (.conj
    (ConstructionProbeIntervalsSyntax.uniformMargins (14 : Fin 35) (15 : Fin 35) (20 : Fin 35) (32 : Fin
    35) (1 : Fin 35) (0 : Fin 35)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 39) (3 : Fin 39) (1 : Fin 39))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 39) (2 : Fin 39) (0 : Fin 39))) (.imp
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (24 : Fin 39) (36 : Fin 39) (3 : Fin 39) (2
    : Fin 39))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides (24 : Fin 39) (36 :
    Fin 39) (2 : Fin 39) (3 : Fin 39)))) (.existsE (.existsE (.conj (ConstructionRealCuts.cut (20 : Fin
    41) (21 : Fin 41) (1 : Fin 41)) (.conj (ConstructionProbeCostSupremum.cap (26 : Fin 41) (38 : Fin 41)
    (6 : Fin 41) (5 : Fin 41) (4 : Fin 41) (1 : Fin 41)) (.conj (ConstructionCutAddition.sumCut (20 : Fin
    41) (21 : Fin 41) (3 : Fin 41) (1 : Fin 41) (0 : Fin 41)) (.conj (.conj (Project.Formula.subset
    (.bound (0 : Fin 41)) (.bound (2 : Fin 41))) (.neg (Project.Formula.subset (.bound (2 : Fin 41))
    (.bound (0 : Fin 41))))) (ConstructionProbeIntervalsSyntax.missedBound (26 : Fin 41) (38 : Fin 41) (6
    : Fin 41) (5 : Fin 41) (4 : Fin 41) (1 : Fin 41)))))))))))))))) (.forallE (.forallE (.forallE
    (.forallE (.imp (ConstructionProbeRaw.old (23 : Fin 39) (21 : Fin 39) (3 : Fin 39) (1 : Fin 39))
    (.imp (ConstructionProbeRaw.old (23 : Fin 39) (21 : Fin 39) (2 : Fin 39) (0 : Fin 39)) (.conj
    (.forallE (.iff (ConstructionProbeCostSupremum.costMember (25 : Fin 40) (37 : Fin 40) (5 : Fin 40) (2
    : Fin 40) (1 : Fin 40) (0 : Fin 40)) (ConstructionProbeCostSupremum.costMember (22 : Fin 40) (34 :
    Fin 40) (30 : Fin 40) (4 : Fin 40) (3 : Fin 40) (0 : Fin 40)))) (.conj (.forallE (.iff
    (ConstructionProbeCostSupremum.cap (25 : Fin 40) (37 : Fin 40) (5 : Fin 40) (2 : Fin 40) (1 : Fin 40)
    (0 : Fin 40)) (ConstructionProbeCostSupremum.cap (22 : Fin 40) (34 : Fin 40) (30 : Fin 40) (4 : Fin
    40) (3 : Fin 40) (0 : Fin 40)))) (.existsE (.conj (ConstructionRealCuts.cut (19 : Fin 40) (20 : Fin
    40) (0 : Fin 40)) (.conj (ConstructionProbeCostSupremum.cap (22 : Fin 40) (34 : Fin 40) (30 : Fin 40)
    (4 : Fin 40) (3 : Fin 40) (0 : Fin 40)) (.conj (ConstructionProbeCostSupremum.cap (25 : Fin 40) (37 :
    Fin 40) (5 : Fin 40) (2 : Fin 40) (1 : Fin 40) (0 : Fin 40)) (.forallE (.forallE (.imp
    (ConstructionProbeCostSupremum.cap (24 : Fin 42) (36 : Fin 42) (32 : Fin 42) (6 : Fin 42) (5 : Fin
    42) (1 : Fin 42)) (.imp (ConstructionProbeCostSupremum.cap (27 : Fin 42) (39 : Fin 42) (7 : Fin 42)
    (4 : Fin 42) (3 : Fin 42) (0 : Fin 42)) (Project.Formula.extensionalEq (.bound (1 : Fin 42)) (.bound
    (0 : Fin 42))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinalOne,Project.Formula.isSuccessor,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeRaw.carrier_freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed,
      ConstructionBaseWeights.digits_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionProbeGateCap.bounds_freeClosed,ConstructionCutDivision.value_freeClosed,
      ConstructionCutDifference.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed,ConstructionCutProduct.value_freeClosed,
      ConstructionMergerWordParameters.graph_freeClosed,ConstructionMergerWordParameters.recipe_freeClosed,
      ConstructionMergerWordHeights.literalLaws_freeClosed,ConstructionMergerWordCosts.value_freeClosed,
      ConstructionProbeHeightFoldSyntax.laws_freeClosed,
      ConstructionMergerHeightCost.copiesHeightCost_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,ConstructionMergerWordProduct.laws_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionProbeCostSupremum.cap_freeClosed,ConstructionProbeCostSupremum.costMember_freeClosed,
      ConstructionProbeIntervalsSyntax.missedBound_freeClosed,ConstructionRealCuts.cut_freeClosed,
      Project.Formula.extensionalEq]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionFractionOrder.carrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionRealCuts.principal_semantics hM,ConstructionProbeRaw.carrier_semantics hM,
    ConstructionProbeRaw.old_semantics hM,ConstructionProbeRaw.cons_semantics hM,
    ConstructionBaseWeights.digits_semantics,ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionProbeGateCap.bounds_semantics hM,ConstructionCutDivision.value_semantics hM,
    ConstructionCutDifference.value_semantics hM,ConstructionCutAddition.sumCut_semantics hM,ConstructionCutProduct.value_semantics hM,
    ConstructionMergerWordParameters.graph_semantics hM,ConstructionMergerWordParameters.recipe_semantics hM,
    ConstructionMergerWordHeights.literalLaws_semantics hM,ConstructionMergerWordCosts.value_semantics hM,
    ConstructionProbeHeightFoldSyntax.laws_semantics hM,
    ConstructionMergerHeightCost.copiesHeightCost_semantics hM,
    ConstructionMergerWordAction.actionTable_semantics hM,ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,
    ConstructionProbeCostSupremum.cap_semantics hM,ConstructionProbeCostSupremum.costMember_semantics hM,
    ConstructionProbeIntervalsSyntax.missedBound_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionBaseMonoid.divides_semantics (M := M)]
  intro hw hz hzw hQ hR hu hone hunit hW hH hC hHB hCB hCopies hTable hMult hPair hG hWordM hWordCon hOldUniform he
  exact ConstructionMergerWordHeightCost.exists_heightCost hM hw hz hzw hQ hR hu hone hunit hW hH hC hHB hCB hCopies hTable hMult hPair hG hWordM hWordCon hOldUniform he

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerWordHeightCostSyntax
