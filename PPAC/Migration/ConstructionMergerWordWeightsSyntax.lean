/- Native object-kernel certificate for actual Merger Word height/cost graphs
and all pointwise bounds, pinned MergerCones:371-420. Literal source equations,
canonical 1/4 and 1/8, ALL internal/nonstandard lengths, SAME Raw carrier.
Complete Word supremum margins/HeightCost and final object Con remain open. -/
import PPAC.Migration.ConstructionMergerWordCosts

namespace PPAC.Migration.ConstructionMergerWordWeightsSyntax
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
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 5)) (.imp
    (.mem (.bound 5) (.bound 0)) (.imp (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15))
    (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 15) (8 : Fin 15) (7 : Fin 15) (7 : Fin 15))
    (.imp (Project.Formula.isOrdinalOne (.bound 7)) (.imp (ConstructionRealCuts.principal (0 : Fin
    15) (1 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (ConstructionProbeRaw.carrier (0 : Fin 15) (3
    : Fin 15) (4 : Fin 15) (6 : Fin 15)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (10 : Fin 15) (3 : Fin 15) (2 : Fin 15))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (11 : Fin 15) (3 : Fin 15) (2 : Fin 15))) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (12 : Fin 15) (4 : Fin 15) (2 : Fin 15))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 15) (4 : Fin 15) (2 : Fin 15)))
    (.imp (ConstructionCutWeights.rangeBound (9 : Fin 15) (10 : Fin 15)) (.imp
    (ConstructionProbeGateCap.bounds (9 : Fin 15) (11 : Fin 15)) (.imp
    (ConstructionCutWeights.rangeBound (9 : Fin 15) (12 : Fin 15)) (.imp
    (ConstructionProbeGateCap.bounds (9 : Fin 15) (13 : Fin 15)) (.imp (.mem (.bound 14) (.bound 3))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.conj (ConstructionBaseWeights.digits
    (14 : Fin 29) (21 : Fin 29) (13 : Fin 29) (12 : Fin 29)) (.conj (Project.Formula.isSuccessor
    (.bound 11) (.bound 12)) (.conj (.mem (.bound 11) (.bound 14)) (.conj
    (Project.Formula.isSuccessor (.bound 10) (.bound 11)) (.conj (Project.Formula.isSuccessor
    (.bound 9) (.bound 10)) (.conj (Project.Formula.isSuccessor (.bound 8) (.bound 9)) (.conj
    (Project.Formula.isSuccessor (.bound 7) (.bound 8)) (.conj (.mem (.bound 7) (.bound 14)) (.conj
    (ConstructionCutDivision.value (14 : Fin 29) (15 : Fin 29) (11 : Fin 29) (23 : Fin 29) (6 : Fin
    29)) (.conj (ConstructionCutDivision.value (14 : Fin 29) (15 : Fin 29) (7 : Fin 29) (23 : Fin
    29) (5 : Fin 29)) (.conj (.mem (.bound 6) (.bound 16)) (.conj (.mem (.bound 5) (.bound 16))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (4 : Fin 29) (18 : Fin 29) (16 : Fin
    29))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 29) (18 : Fin 29) (16
    : Fin 29))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 29) (18 : Fin
    29) (16 : Fin 29))) (.conj (ConstructionMergerWordParameters.graph 0 (14 : Fin 29) (15 : Fin 29)
    (11 : Fin 29) (23 : Fin 29) (6 : Fin 29) (5 : Fin 29) (18 : Fin 29) (26 : Fin 29) (27 : Fin 29)
    (4 : Fin 29)) (.conj (ConstructionMergerWordParameters.graph 1 (14 : Fin 29) (15 : Fin 29) (11 :
    Fin 29) (23 : Fin 29) (6 : Fin 29) (5 : Fin 29) (18 : Fin 29) (26 : Fin 29) (27 : Fin 29) (3 :
    Fin 29)) (.conj (ConstructionMergerWordParameters.graph 2 (14 : Fin 29) (15 : Fin 29) (11 : Fin
    29) (23 : Fin 29) (6 : Fin 29) (5 : Fin 29) (18 : Fin 29) (26 : Fin 29) (27 : Fin 29) (2 : Fin
    29)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (8 : Fin 33) (3 : Fin 33) (2 : Fin 33))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (7 : Fin 33) (3 : Fin 33) (1 : Fin 33))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (6 : Fin 33) (3 : Fin 33) (0 : Fin 33)))
    (ConstructionMergerWordParameters.recipe (18 : Fin 33) (19 : Fin 33) (15 : Fin 33) (27 : Fin 33)
    (10 : Fin 33) (9 : Fin 33) (30 : Fin 33) (31 : Fin 33) (3 : Fin 33) (2 : Fin 33) (1 : Fin 33) (0
    : Fin 33))))))))) (.conj (ConstructionCutWeights.rangeBound (23 : Fin 29) (4 : Fin 29)) (.conj
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 31) (1 :
    Fin 31) (0 : Fin 31))) (.existsE (.mem (.bound 0) (.bound 1))))))
    (ConstructionProbeGateCap.bounds (5 : Fin 29) (2 : Fin 29))))))))))))))))))))))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 29) (20 : Fin 29) (16 : Fin 29)))
    (.conj (ConstructionProbeHeightFoldSyntax.laws (14 : Fin 29) (17 : Fin 29) (18 : Fin 29) (19 :
    Fin 29) (20 : Fin 29) (15 : Fin 29) (24 : Fin 29) (4 : Fin 29) (3 : Fin 29) (1 : Fin 29)) (.conj
    (ConstructionMergerWordHeights.literalLaws (14 : Fin 29) (15 : Fin 29) (17 : Fin 29) (18 : Fin
    29) (19 : Fin 29) (23 : Fin 29) (24 : Fin 29) (4 : Fin 29) (1 : Fin 29)) (.conj
    (ConstructionCutWeights.rangeBound (23 : Fin 29) (1 : Fin 29)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 29) (20 : Fin 29) (16 : Fin 29))) (.conj (.forallE (.forallE
    (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin 31) (1 : Fin 31) (0 : Fin 31)))
    (.conj (.mem (.bound 1) (.bound 22)) (ConstructionMergerWordCosts.value (16 : Fin 31) (17 : Fin
    31) (19 : Fin 31) (20 : Fin 31) (21 : Fin 31) (25 : Fin 31) (3 : Fin 31) (27 : Fin 31) (4 : Fin
    31) (1 : Fin 31) (0 : Fin 31)))))) (.conj (ConstructionProbeGateCap.bounds (23 : Fin 29) (0 :
    Fin 29)) (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old (22 : Fin 32) (20
    : Fin 32) (2 : Fin 32) (1 : Fin 32)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (3
    : Fin 32) (1 : Fin 32) (0 : Fin 32))) (ProjectSyntax.encode id (Source.SetLanguage.edge (28 :
    Fin 32) (2 : Fin 32) (0 : Fin 32)))))))) (.forallE (.forallE (.forallE (.forallE (.imp
    (ConstructionProbeRaw.cons (18 : Fin 33) (21 : Fin 33) (22 : Fin 33) (3 : Fin 33) (2 : Fin 33)
    (1 : Fin 33)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin 33) (1 : Fin 33)
    (0 : Fin 33))) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (8 : Fin 36) (5 : Fin 36) (2 : Fin 36))) (.conj
    (ConstructionCutDifference.value (21 : Fin 36) (22 : Fin 36) (2 : Fin 36) (30 : Fin 36) (1 : Fin
    36)) (.conj (ConstructionCutAddition.sumCut (21 : Fin 36) (22 : Fin 36) (2 : Fin 36) (1 : Fin
    36) (30 : Fin 36)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (9 : Fin 36) (6 :
    Fin 36) (0 : Fin 36))) (ConstructionCutProduct.value (21 : Fin 36) (22 : Fin 36) (1 : Fin 36) (0
    : Fin 36) (3 : Fin 36))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
      ConstructionProbeHeightFoldSyntax.laws_freeClosed]

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
    ConstructionProbeHeightFoldSyntax.laws_semantics hM]
  intro hw hz hzw hQ hR hu hone hunit hW hH hC hHD hCD hHB hCB hHDB hCDB he
  exact ConstructionMergerWordCosts.exists_system hM hw hz hzw hQ hR hu hone hunit hW hH hC hHD hCD hHB hCB hHDB hCDB he

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerWordWeightsSyntax
