/- Native original-kernel certificate for pinned copiesHeight_gap:234.
Returns actual coordinate difference, its /n value and actual average
difference, with all three cut facts and both exact addition equations.
No strict-comparison restriction, new gap/linearity/monotonicity oracle,
external standard-length restriction or new Choice/recursion backend.
Full coordinate/uniform margins and final Con remain open. -/
import PPAC.Migration.ConstructionMergerAverageGap
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionProbeIntervalsSyntax

namespace PPAC.Migration.ConstructionMergerAverageGapSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 19
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound
    3) (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 19) (1 : Fin 19)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 19) (1 : Fin 19) (2 : Fin 19)) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.identityGraph (2 : Fin 19) (5 : Fin 19))) (.imp
    (ConstructionCutArithmeticSyntax.graph (0 : Fin 19) (1 : Fin 19) (2 : Fin 19) (4 : Fin 19)) (.imp (.mem
    (.bound 6) (.bound 0)) (.imp (.existsE (.mem (.bound 0) (.bound 7))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (8 : Fin 19) (9 : Fin 19) (10 : Fin 19))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.conical (8 : Fin 19) (9 : Fin 19) (10 : Fin 19))) (.imp
    (ConstructionProbeLetters.representatives (6 : Fin 19) (8 : Fin 19) (12 : Fin 19)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 19) (12 : Fin 19) (13 : Fin 19))) (.imp
    (ConstructionMergerCopies.equalityLaw (6 : Fin 19) (8 : Fin 19) (9 : Fin 19) (11 : Fin 19) (14 : Fin 19))
    (.imp (ConstructionMergerAction.copyLaw (8 : Fin 19) (9 : Fin 19) (14 : Fin 19) (15 : Fin 19)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (16 : Fin 19) (8 : Fin 19) (2 : Fin 19))) (.imp
    (ConstructionCutWeights.rangeBound (18 : Fin 19) (16 : Fin 19)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 19) (1 : Fin 19) (8 : Fin 19) (9 : Fin 19) (16 :
    Fin 19) (17 : Fin 19)) (.imp (ConstructionMergerCoordinates.graph (6 : Fin 19) (13 : Fin 19) (14 : Fin 19)
    (16 : Fin 19) (3 : Fin 19) (7 : Fin 19)) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.forallE (.imp (ConstructionMergerFiniteWeights.heightValue (7 : Fin 26) (8 : Fin 26) (13 : Fin 26) (9 :
    Fin 26) (11 : Fin 26) (12 : Fin 26) (10 : Fin 26) (14 : Fin 26) (6 : Fin 26) (4 : Fin 26)) (.imp
    (ConstructionMergerFiniteWeights.heightValue (7 : Fin 26) (8 : Fin 26) (13 : Fin 26) (9 : Fin 26) (11 : Fin
    26) (12 : Fin 26) (10 : Fin 26) (14 : Fin 26) (5 : Fin 26) (3 : Fin 26)) (.imp (.mem (.bound 2) (.bound
    13)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product (14 : Fin 26) (2 : Fin 26) (6 : Fin 26) (1
    : Fin 26))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product (14 : Fin 26) (2 : Fin 26) (5 : Fin
    26) (0 : Fin 26))) (.imp (ConstructionMergerCopyCones.reaches (15 : Fin 26) (22 : Fin 26) (6 : Fin 26) (5 :
    Fin 26)) (.existsE (.existsE (.existsE (.conj (ConstructionRealCuts.cut (10 : Fin 29) (11 : Fin 29) (2 :
    Fin 29)) (.conj (ConstructionCutDifference.value (10 : Fin 29) (11 : Fin 29) (4 : Fin 29) (3 : Fin 29) (2 :
    Fin 29)) (.conj (ConstructionCutAddition.sumCut (10 : Fin 29) (11 : Fin 29) (4 : Fin 29) (2 : Fin 29) (3 :
    Fin 29)) (.conj (ConstructionRealCuts.cut (10 : Fin 29) (11 : Fin 29) (1 : Fin 29)) (.conj
    (ConstructionCutDivision.value (10 : Fin 29) (11 : Fin 29) (16 : Fin 29) (2 : Fin 29) (1 : Fin 29)) (.conj
    (ConstructionRealCuts.cut (10 : Fin 29) (11 : Fin 29) (0 : Fin 29)) (.conj (ConstructionCutDifference.value
    (10 : Fin 29) (11 : Fin 29) (7 : Fin 29) (6 : Fin 29) (0 : Fin 29)) (.conj (ConstructionCutAddition.sumCut
    (10 : Fin 29) (11 : Fin 29) (7 : Fin 29) (0 : Fin 29) (6 : Fin 29)) (Project.Formula.subset (.bound 1)
    (.bound 0)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionCutArithmeticSyntax.graph_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,
      ConstructionMergerCopies.equalityLaw_freeClosed,ConstructionMergerAction.copyLaw_freeClosed,
      ConstructionMergerCoordinates.graph_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,
      ConstructionMergerCopyCones.reaches_freeClosed,ConstructionMergerFiniteWeights.heightValue_freeClosed,
      ConstructionCutDifference.value_freeClosed,ConstructionCutDivision.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ConstructionCutArithmeticSyntax.graph_semantics hM,
    ConstructionCutWeights.rangeBound_semantics hM,ConstructionMergerCopies.equalityLaw_semantics hM,
    ConstructionMergerAction.copyLaw_semantics hM,ConstructionMergerCoordinates.graph_semantics hM,
    ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,ConstructionMergerCopyCones.reaches_semantics hM,
    ConstructionMergerFiniteWeights.heightValue_semantics hM,ConstructionCutDifference.value_semantics hM,
    ConstructionCutDivision.value_semantics hM,ConstructionCutAddition.sumCut_semantics hM]
  intro hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hp hEq hCopy hHeight hHB hUniform hGraph
  intro z t a b i c d ha hb hi hzc htd hReach
  exact ConstructionMergerAverageGap.copiesHeight_gap hM hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hp hEq hCopy hHeight hHB hUniform hGraph ha hb hi hzc htd hReach

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerAverageGapSyntax
