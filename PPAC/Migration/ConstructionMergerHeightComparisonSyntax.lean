/- Native original-kernel certificate for the pinned copiesHeight
strictMono and copiesCost_le_one. Actual sum rows, original quotient/copy
laws and old UniformMargins supply strictness. Actual Height(e)/2/n supplies
the cost bound. All internal lengths; canonical Principal(1) identifies top.
Height<1, coordinate gap and complete uniform margins remain open. -/
import PPAC.Migration.ConstructionMergerHeightComparison
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionProbeIntervalsSyntax

namespace PPAC.Migration.ConstructionMergerHeightComparisonSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 27
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound
    3) (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 27) (1 : Fin 27)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 27) (1 : Fin 27) (2 : Fin 27)) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.identityGraph (2 : Fin 27) (5 : Fin 27))) (.imp
    (ConstructionCutArithmeticSyntax.graph (0 : Fin 27) (1 : Fin 27) (2 : Fin 27) (4 : Fin 27)) (.imp (.mem
    (.bound 6) (.bound 0)) (.imp (.existsE (.mem (.bound 0) (.bound 7))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (8 : Fin 27) (9 : Fin 27) (10 : Fin 27))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (8 : Fin 27) (9 : Fin 27) (10 : Fin 27))) (.imp
    (ConstructionProbeLetters.representatives (6 : Fin 27) (8 : Fin 27) (12 : Fin 27)) (.imp
    (ConstructionMergerCopies.copies (6 : Fin 27) (8 : Fin 27) (9 : Fin 27) (11 : Fin 27) (12 : Fin 27) (13 :
    Fin 27)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 27) (12 : Fin 27) (13 : Fin
    27))) (.imp (ConstructionMergerCopies.projectionGraph (6 : Fin 27) (8 : Fin 27) (9 : Fin 27) (11 : Fin 27)
    (12 : Fin 27) (14 : Fin 27)) (.imp (ConstructionMergerCopies.equalityLaw (6 : Fin 27) (8 : Fin 27) (9 :
    Fin 27) (11 : Fin 27) (14 : Fin 27)) (.imp (ConstructionMergerAction.copyLaw (8 : Fin 27) (9 : Fin 27) (14
    : Fin 27) (15 : Fin 27)) (.imp (ConstructionProbeLetters.representatives (6 : Fin 27) (13 : Fin 27) (19 :
    Fin 27)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 27) (19 : Fin 27) (2 : Fin
    27))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (16 : Fin 27) (8 : Fin 27) (2 : Fin 27)))
    (.imp (ConstructionCutWeights.rangeBound (18 : Fin 27) (16 : Fin 27)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 27) (1 : Fin 27) (8 : Fin 27) (9 : Fin 27) (16 :
    Fin 27) (17 : Fin 27)) (.imp (ConstructionMergerCoordinates.graph (6 : Fin 27) (13 : Fin 27) (14 : Fin 27)
    (16 : Fin 27) (3 : Fin 27) (7 : Fin 27)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 27) (21 :
    Fin 27) (20 : Fin 27) (20 : Fin 27)) (.imp (Project.Formula.isOrdinalOne (.bound 20)) (.imp
    (ConstructionRealCuts.principal (0 : Fin 27) (1 : Fin 27) (21 : Fin 27) (18 : Fin 27)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (16 : Fin 27) (10 : Fin 27) (22 : Fin 27))) (.imp
    (Project.Formula.isSuccessor (.bound 23) (.bound 20)) (.imp (.mem (.bound 23) (.bound 0)) (.imp
    (ConstructionCutDivision.value (0 : Fin 27) (1 : Fin 27) (23 : Fin 27) (22 : Fin 27) (24 : Fin 27)) (.conj
    (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound 17)) (.imp (.mem (.bound 2) (.bound
    17)) (.imp (ConstructionMergerFiniteWeights.heightValue (4 : Fin 31) (5 : Fin 31) (10 : Fin 31) (6 : Fin
    31) (8 : Fin 31) (9 : Fin 31) (7 : Fin 31) (11 : Fin 31) (3 : Fin 31) (1 : Fin 31)) (.imp
    (ConstructionMergerFiniteWeights.heightValue (4 : Fin 31) (5 : Fin 31) (10 : Fin 31) (6 : Fin 31) (8 : Fin
    31) (9 : Fin 31) (7 : Fin 31) (11 : Fin 31) (2 : Fin 31) (0 : Fin 31)) (.imp
    (ConstructionMergerCopyCones.reaches (12 : Fin 31) (19 : Fin 31) (3 : Fin 31) (2 : Fin 31)) (.conj
    (Project.Formula.subset (.bound 1) (.bound 0)) (.imp (.neg (Project.Formula.extensionalEq (.bound 3)
    (.bound 2))) (.conj (Project.Formula.subset (.bound 1) (.bound 0)) (.neg (Project.Formula.subset (.bound
    0) (.bound 1))))))))))))))) (.forallE (.forallE (.imp (ConstructionMergerFiniteWeights.costValue (2 : Fin
    29) (3 : Fin 29) (8 : Fin 29) (4 : Fin 29) (27 : Fin 29) (7 : Fin 29) (20 : Fin 29) (26 : Fin 29) (28 :
    Fin 29) (1 : Fin 29) (0 : Fin 29)) (.conj (Project.Formula.subset (.bound 0) (.bound 20)) (.neg
    (Project.Formula.subset (.bound 20) (.bound 0))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isSuccessor,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionCutDivision.value_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionMergerCopies.copies_freeClosed,ConstructionMergerCopies.projectionGraph_freeClosed,
      ConstructionMergerCopies.equalityLaw_freeClosed,ConstructionMergerAction.copyLaw_freeClosed,
      ConstructionMergerCoordinates.graph_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionMergerCopyCones.reaches_freeClosed,ConstructionMergerFiniteWeights.heightValue_freeClosed,
      ConstructionMergerFiniteWeights.costValue_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingConditionGraphs.identityGraph_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionCutArithmeticSyntax.graph_semantics hM,ConstructionCutDivision.value_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,ConstructionMergerCopies.copies_semantics hM,
    ConstructionMergerCopies.projectionGraph_semantics hM,ConstructionMergerCopies.equalityLaw_semantics hM,
    ConstructionMergerAction.copyLaw_semantics hM,ConstructionMergerCoordinates.graph_semantics hM,
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,ConstructionMergerCopyCones.reaches_semantics hM,
    ConstructionMergerFiniteWeights.heightValue_semantics hM,ConstructionMergerFiniteWeights.costValue_semantics hM]
  intro hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hL hp hProj hEq hCopy hJ hCH hHeight hHB hUniform hGraph hu hone _hUnit hEdge htwo htwow hCap
  constructor
  · intro z t a b hzL htL ha hb hReach
    exact ConstructionMergerHeightComparison.copiesHeight_order hM hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hL hp hProj hEq hCopy hJ hCH hHeight hHB hUniform hGraph hzL htL ha hb hReach
  · intro z a ha
    exact ConstructionMergerHeightComparison.copiesCost_unit_bound hM hw hQ hR hu.1 hone hn hnp htwo htwow hHeight hHB hEdge hCap ha

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerHeightComparisonSyntax
