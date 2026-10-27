/- Original-kernel certificate for pinned MergerCones.copiesHeight_pos,
copiesCost_pos/le_cap/le_copy. Actual quotient representation and existing
coordinate bounds supply positivity; actual old Height(e)/2 supplies cap.
No new bound/positivity oracle; all internal/nonstandard finite lengths.
Full height upper/strict bounds and uniform supremum margins remain open. -/
import PPAC.Migration.ConstructionMergerWeightEstimates
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionWordArithmeticSyntax

namespace PPAC.Migration.ConstructionMergerWeightEstimatesSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 26
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 4)) (.imp (.mem (.bound
    4) (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 26) (1 : Fin 26)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 26) (1 : Fin 26) (3 : Fin 26)) (.imp (.mem (.bound 2) (.bound
    0)) (.imp (.existsE (.mem (.bound 0) (.bound 3))) (.imp (ConstructionFractionOrder.coordinates (0 : Fin
    26) (9 : Fin 26) (8 : Fin 26) (8 : Fin 26)) (.imp (Project.Formula.isOrdinalOne (.bound 8)) (.imp
    (ConstructionRealCuts.principal (0 : Fin 26) (1 : Fin 26) (9 : Fin 26) (10 : Fin 26)) (.imp
    (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (3 : Fin 26) (7 : Fin 26))) (.imp
    (ConstructionCutArithmeticSyntax.graph (0 : Fin 26) (1 : Fin 26) (3 : Fin 26) (5 : Fin 26)) (.imp
    (ConstructionWordArithmeticSyntax.graph (0 : Fin 26) (1 : Fin 26) (3 : Fin 26) (6 : Fin 26)) (.imp
    (ConstructionProbeLetters.representatives (2 : Fin 26) (13 : Fin 26) (16 : Fin 26)) (.imp
    (ConstructionMergerCopies.copies (2 : Fin 26) (13 : Fin 26) (14 : Fin 26) (15 : Fin 26) (16 : Fin 26) (17
    : Fin 26)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (18 : Fin 26) (16 : Fin 26) (17 :
    Fin 26))) (.imp (ConstructionMergerCopies.projectionGraph (2 : Fin 26) (13 : Fin 26) (14 : Fin 26) (15 :
    Fin 26) (16 : Fin 26) (18 : Fin 26)) (.imp (ConstructionMergerCopies.equalityLaw (2 : Fin 26) (13 : Fin
    26) (14 : Fin 26) (15 : Fin 26) (18 : Fin 26)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (19 : Fin 26) (13 : Fin 26) (3 : Fin 26))) (.imp (ConstructionCutWeights.rangeBound (10 : Fin 26) (19 :
    Fin 26)) (.imp (ConstructionProbeGateCap.bounds (10 : Fin 26) (20 : Fin 26)) (.imp
    (ConstructionMergerCoordinates.graph (2 : Fin 26) (17 : Fin 26) (18 : Fin 26) (19 : Fin 26) (4 : Fin 26)
    (11 : Fin 26)) (.imp (ConstructionMergerCoordinates.graph (2 : Fin 26) (17 : Fin 26) (18 : Fin 26) (20 :
    Fin 26) (10 : Fin 26) (12 : Fin 26)) (.imp (ConstructionProbeLetters.representatives (2 : Fin 26) (17 :
    Fin 26) (21 : Fin 26)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 26) (21 : Fin
    26) (3 : Fin 26))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (19 : Fin 26) (22 : Fin 26)
    (23 : Fin 26))) (.imp (Project.Formula.isSuccessor (.bound 24) (.bound 8)) (.imp (.mem (.bound 24)
    (.bound 0)) (.imp (ConstructionCutDivision.value (0 : Fin 26) (1 : Fin 26) (24 : Fin 26) (23 : Fin 26)
    (25 : Fin 26)) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound 19)) (.conj (.imp
    (ConstructionMergerFiniteWeights.heightValue (2 : Fin 28) (3 : Fin 28) (4 : Fin 28) (5 : Fin 28) (7 : Fin
    28) (9 : Fin 28) (6 : Fin 28) (13 : Fin 28) (1 : Fin 28) (0 : Fin 28)) (.existsE (.mem (.bound 0) (.bound
    1)))) (.imp (ConstructionMergerFiniteWeights.costValue (2 : Fin 28) (3 : Fin 28) (4 : Fin 28) (5 : Fin
    28) (8 : Fin 28) (9 : Fin 28) (12 : Fin 28) (27 : Fin 28) (14 : Fin 28) (1 : Fin 28) (0 : Fin 28)) (.conj
    (.existsE (.mem (.bound 0) (.bound 1))) (.conj (.forallE (.imp (ConstructionCutDivision.value (3 : Fin
    29) (4 : Fin 29) (5 : Fin 29) (28 : Fin 29) (0 : Fin 29)) (Project.Formula.subset (.bound 1) (.bound
    0)))) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
    (24 : Fin 32) (3 : Fin 32) (2 : Fin 32) (5 : Fin 32))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (26 : Fin 32) (2 : Fin 32) (1 : Fin 32))) (.imp (ConstructionCutDivision.value
    (6 : Fin 32) (7 : Fin 32) (8 : Fin 32) (1 : Fin 32) (0 : Fin 32)) (Project.Formula.subset (.bound 4)
    (.bound 0)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isSuccessor,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionWordArithmeticSyntax.graph_freeClosed,ConstructionCutDivision.value_freeClosed,
      ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,
      ConstructionMergerCopies.copies_freeClosed,ConstructionMergerCopies.projectionGraph_freeClosed,
      ConstructionMergerCopies.equalityLaw_freeClosed,ConstructionMergerCoordinates.graph_freeClosed,
      ConstructionMergerFiniteWeights.heightValue_freeClosed,ConstructionMergerFiniteWeights.costValue_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingConditionGraphs.identityGraph_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),
    KuratowskiZF.source_edge,ConstructionCutArithmeticSyntax.graph_semantics hM,
    ConstructionWordArithmeticSyntax.graph_semantics hM,ConstructionCutDivision.value_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,ConstructionMergerCoordinates.graph_semantics hM,
    ConstructionMergerFiniteWeights.heightValue_semantics hM,ConstructionMergerFiniteWeights.costValue_semantics hM]
  intro hw hz hzw hQ hR hn hnp hu hone hunit hId hAdd hMul hC hL hp hProj hEq hHeight hHB hCB hCH hCoordC hJ hCC hEdge htwo htwow hCap
  exact ConstructionMergerWeightEstimates.copies_estimates hM hw hz hzw hQ hR hn hnp hu hone hunit hId hAdd hMul hC hL hp hProj hEq hHeight hHB hCB hCH hCoordC hJ hCC hEdge htwo htwow hCap

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerWeightEstimatesSyntax
