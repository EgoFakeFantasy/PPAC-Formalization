/- Native original-kernel certificate for pinned copiesHeight_lt_one:211.
Actual constant row and existing Raw evaluator identify sum_const with the
principal cut at internal n/1; positive-natural division gives the SAME
canonical unit cut. Existing coordinate bounds supply strictness for all
internal/nonstandard n. Coordinate gap and full uniform margin stay open. -/
import PPAC.Migration.ConstructionMergerHeightUpper
import PPAC.Migration.ConstructionCutArithmeticSyntax

namespace PPAC.Migration.ConstructionMergerHeightUpperSyntax
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
    (ConstructionRealCuts.cutCarrier (0 : Fin 19) (1 : Fin 19) (2 : Fin 19)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 19) (5 : Fin 19) (4 : Fin 19) (4 : Fin 19)) (.imp
    (Project.Formula.isOrdinalOne (.bound 4)) (.imp (ConstructionRealCuts.principal (0 : Fin 19) (1 : Fin 19)
    (5 : Fin 19) (6 : Fin 19)) (.imp (.mem (.bound 7) (.bound 0)) (.imp (.existsE (.mem (.bound 0) (.bound
    8))) (.imp (ConstructionProbeLetters.representatives (2 : Fin 19) (2 : Fin 19) (8 : Fin 19)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 19) (8 : Fin 19) (2 : Fin 19))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 19) (2 : Fin 19) (2 : Fin 19))) (.imp
    (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (2 : Fin 19) (10 : Fin 19))) (.imp
    (ConstructionCutArithmeticSyntax.graph (0 : Fin 19) (1 : Fin 19) (2 : Fin 19) (9 : Fin 19)) (.imp
    (ConstructionCutWeights.rangeBound (6 : Fin 19) (13 : Fin 19)) (.imp (ConstructionProbeGateCap.bounds (6
    : Fin 19) (14 : Fin 19)) (.imp (ConstructionMergerCoordinates.graph (7 : Fin 19) (11 : Fin 19) (12 : Fin
    19) (13 : Fin 19) (3 : Fin 19) (15 : Fin 19)) (.imp (ConstructionMergerCoordinates.graph (7 : Fin 19) (11
    : Fin 19) (12 : Fin 19) (14 : Fin 19) (6 : Fin 19) (16 : Fin 19)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (13 : Fin 19) (17 : Fin 19) (18 : Fin 19))) (.forallE (.forallE (.imp
    (ConstructionMergerFiniteWeights.heightValue (2 : Fin 21) (3 : Fin 21) (9 : Fin 21) (4 : Fin 21) (11 :
    Fin 21) (12 : Fin 21) (5 : Fin 21) (17 : Fin 21) (1 : Fin 21) (0 : Fin 21)) (.conj
    (Project.Formula.subset (.bound 0) (.bound 8)) (.neg (Project.Formula.subset (.bound 8) (.bound
    0)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,
      ConstructionMergerCoordinates.graph_freeClosed,ConstructionMergerFiniteWeights.heightValue_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingConditionGraphs.identityGraph_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionCutArithmeticSyntax.graph_semantics hM,ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionProbeGateCap.bounds_semantics hM,ConstructionMergerCoordinates.graph_semantics hM,
    ConstructionMergerFiniteWeights.heightValue_semantics hM]
  intro hw hz hzw hQ hR hu hone hUnit hn hnp hJ hAddMap hIdMap hId hAdd hHB hCB hCH hCC hEdge
  exact ConstructionMergerHeightUpper.copiesHeight_lt_one hM hw hz hzw hQ hR hu hone hUnit hn hnp hJ hAddMap hIdMap hId hAdd hHB hCB hCH hCC hEdge

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerHeightUpperSyntax
