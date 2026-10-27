/- Pure-membership, original-kernel certificate for the literal copies
finite-average / finite-product weight functions. Same supplied coordinate
tables; actual operations, canonical seeds and old-unit-height/2 cap are
constructed. Complete HeightCost inequalities and final Con remain open. -/
import PPAC.Migration.ConstructionMergerFiniteWeights
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionWordArithmeticSyntax

namespace PPAC.Migration.ConstructionMergerFiniteWeightsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 15
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 15) (1 :
    Fin 15)) (.imp (.mem (.bound 2) (.bound 0)) (.imp (.existsE (.mem (.bound 0) (.bound 3))) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 15) (1 : Fin 15) (4 : Fin 15)) (.imp
    (ConstructionProbeLetters.representatives (2 : Fin 15) (3 : Fin 15) (5 : Fin 15)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 15) (5 : Fin 15) (4 : Fin 15))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 15) (5 : Fin 15) (4 : Fin 15))) (.imp
    (Project.Formula.isEmpty (.bound 8)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (10 : Fin
    15) (9 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound 9)) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (10 : Fin 15) (11 : Fin 15)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 15) (12 : Fin 15) (4 : Fin 15))) (.imp
    (.mem (.bound 13) (.bound 12)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (24 : Fin 25) (23
    : Fin 25) (9 : Fin 25))) (.conj (ConstructionProbeLetters.representatives (14 : Fin 25) (14 : Fin 25) (8
    : Fin 25)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 25) (8 : Fin 25) (14 :
    Fin 25))) (.conj (ConstructionCutArithmeticSyntax.graph (10 : Fin 25) (11 : Fin 25) (14 : Fin 25) (7 :
    Fin 25)) (.conj (ConstructionProbeLetters.representatives (14 : Fin 25) (14 : Fin 25) (6 : Fin 25))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 25) (6 : Fin 25) (14 : Fin 25)))
    (.conj (ConstructionWordArithmeticSyntax.graph (10 : Fin 25) (11 : Fin 25) (14 : Fin 25) (5 : Fin 25))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (4 : Fin 25) (14 : Fin 25) (14 : Fin 25)))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (14 : Fin 25) (4 : Fin 25)))
    (.conj (Project.Formula.isSuccessor (.bound 3) (.bound 19)) (.conj (.mem (.bound 3) (.bound 10)) (.conj
    (.mem (.bound 2) (.bound 14)) (.conj (ConstructionCutDivision.value (10 : Fin 25) (11 : Fin 25) (3 : Fin
    25) (9 : Fin 25) (2 : Fin 25)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 25)
    (13 : Fin 25) (14 : Fin 25))) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (3 : Fin 27) (1 : Fin 27) (0 : Fin 27))) (.conj (.mem (.bound 1) (.bound 15))
    (ConstructionMergerFiniteWeights.heightValue (12 : Fin 27) (13 : Fin 27) (14 : Fin 27) (16 : Fin 27) (9
    : Fin 27) (6 : Fin 27) (20 : Fin 27) (18 : Fin 27) (1 : Fin 27) (0 : Fin 27)))))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 25) (13 : Fin 25) (14 : Fin 25))) (.conj
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin 27) (1 : Fin 27) (0
    : Fin 27))) (.conj (.mem (.bound 1) (.bound 15)) (ConstructionMergerFiniteWeights.costValue (12 : Fin
    27) (13 : Fin 27) (14 : Fin 27) (16 : Fin 27) (7 : Fin 27) (6 : Fin 27) (23 : Fin 27) (4 : Fin 27) (19 :
    Fin 27) (1 : Fin 27) (0 : Fin 27)))))) (.conj (.forallE (.imp (.mem (.bound 0) (.bound 15))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (6 : Fin 26) (0 : Fin 26) (22 : Fin 26) (0 : Fin
    26))))) (.forallE (.imp (.mem (.bound 0) (.bound 15)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (8 : Fin 26) (19 : Fin 26) (0 : Fin 26) (0 : Fin
    26)))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isSuccessor,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionWordArithmeticSyntax.graph_freeClosed,ConstructionCutDivision.value_freeClosed,
      ConstructionMergerFiniteWeights.heightValue_freeClosed,ConstructionMergerFiniteWeights.costValue_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingConditionGraphs.identityGraph_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),
    KuratowskiZF.source_edge,ConstructionCutArithmeticSyntax.graph_semantics hM,
    ConstructionWordArithmeticSyntax.graph_semantics hM,ConstructionCutDivision.value_semantics hM,
    ConstructionMergerFiniteWeights.heightValue_semantics hM,ConstructionMergerFiniteWeights.costValue_semantics hM]
  intro hw hQ hn hnp hR hJ hCH hCC hz hu hone hunit hHeight he
  exact ConstructionMergerFiniteWeights.exists_system hM hw hQ hn hnp hR hJ hCH hCC hz hu hone hunit hHeight he

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerFiniteWeightsSyntax
