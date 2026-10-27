/- Native original-kernel contract for complete copiesHeightCost:351,
constructed from original weighted parent/prescription, on SAME actual copies
and Word/inclusion/profile/roots. Both literal weight graphs, every pointwise
field and actual strict missed-cost supremum are retained in ONE output.
Word weight extension and final object Con remain open. -/
import PPAC.Migration.ConstructionMergerHeightCost
import PPAC.Migration.ConstructionMergerCoordinateSyntax
import PPAC.Migration.ConstructionCutArithmeticSyntax
import PPAC.Migration.ConstructionWordArithmeticSyntax

namespace PPAC.Migration.ConstructionMergerHeightCostSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 14
    (.imp (ConstructionFractionOrder.carrier (0 : Fin 14) (7 : Fin 14)) (.imp (.mem (.bound 1)
    (.bound 0)) (.imp (.existsE (.mem (.bound 0) (.bound 2))) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 14) (13 : Fin 14) (12 : Fin 14) (12 : Fin 14))
    (.imp (Project.Formula.isOrdinalOne (.bound 12)) (.imp (ConstructionRealCuts.principal (0 : Fin
    14) (7 : Fin 14) (13 : Fin 14) (11 : Fin 14)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin
    14) (7 : Fin 14) (8 : Fin 14)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 :
    Fin 14) (2 : Fin 14) (8 : Fin 14))) (.imp (ConstructionCutWeights.rangeBound (11 : Fin 14) (9 :
    Fin 14)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 14) (2 : Fin 14) (8
    : Fin 14))) (.imp (ConstructionProbeGateCap.bounds (11 : Fin 14) (10 : Fin 14)) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 14) (7 : Fin 14) (2 : Fin 14) (3 : Fin
    14) (9 : Fin 14) (10 : Fin 14)) (.imp (Project.Formula.isOmega (.bound (0 : Fin 14))) (.imp
    (Project.Formula.isEmpty (.bound (6 : Fin 14))) (.imp (.mem (.bound (6 : Fin 14)) (.bound (0 :
    Fin 14))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 14) (3 :
    Fin 14) (4 : Fin 14))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (2 : Fin 14)
    (3 : Fin 14) (4 : Fin 14))) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (2 :
    Fin 14) (3 : Fin 14)) (.imp (ConstructionMergerRelations.prescription (1 : Fin 14) (2 : Fin 14)
    (5 : Fin 14)) (.imp (ConstructionMergerRelations.valid (1 : Fin 14) (2 : Fin 14) (3 : Fin 14) (5
    : Fin 14)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.conj
    (ConstructionProbeLetters.representatives (17 : Fin 30) (18 : Fin 30) (15 : Fin 30)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 30) (15 : Fin 30) (14 : Fin 30)))
    (.conj (ConstructionMergerCopies.copies (17 : Fin 30) (18 : Fin 30) (19 : Fin 30) (21 : Fin 30)
    (15 : Fin 30) (14 : Fin 30)) (.conj (ConstructionMergerCopies.projectionGraph (17 : Fin 30) (18
    : Fin 30) (19 : Fin 30) (21 : Fin 30) (15 : Fin 30) (13 : Fin 30)) (.conj
    (ConstructionMergerCopies.equalityLaw (17 : Fin 30) (18 : Fin 30) (19 : Fin 30) (21 : Fin 30)
    (13 : Fin 30)) (.conj (ConstructionProbeLetters.representatives (14 : Fin 30) (18 : Fin 30) (12
    : Fin 30)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 30) (12 : Fin
    30) (14 : Fin 30))) (.conj (ConstructionMergerAction.actionTable (18 : Fin 30) (19 : Fin 30) (13
    : Fin 30) (11 : Fin 30)) (.conj (ConstructionMergerAction.rightFreeAction (19 : Fin 30) (20 :
    Fin 30) (14 : Fin 30) (11 : Fin 30)) (.conj (ConstructionMergerAction.copyLaw (18 : Fin 30) (19
    : Fin 30) (13 : Fin 30) (11 : Fin 30)) (.conj (ConstructionProbeRaw.carrier (16 : Fin 30) (18 :
    Fin 30) (14 : Fin 30) (10 : Fin 30)) (.conj (ConstructionProbeLetters.representatives (10 : Fin
    30) (18 : Fin 30) (9 : Fin 30)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 :
    Fin 30) (9 : Fin 30) (10 : Fin 30))) (.conj (ConstructionMergerWordAction.actionTable (16 : Fin
    30) (18 : Fin 30) (14 : Fin 30) (22 : Fin 30) (19 : Fin 30) (11 : Fin 30) (8 : Fin 30)) (.conj
    (ConstructionMergerAction.rightFreeAction (19 : Fin 30) (20 : Fin 30) (10 : Fin 30) (8 : Fin
    30)) (.conj (ConstructionProbeLetters.representatives (10 : Fin 30) (10 : Fin 30) (7 : Fin 30))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 30) (7 : Fin 30) (10 : Fin
    30))) (ConstructionMergerWordProduct.laws (16 : Fin 30) (18 : Fin 30) (14 : Fin 30) (22 : Fin
    30) (8 : Fin 30) (6 : Fin 30))))))))))))))))))) (.conj (ConstructionProbeRaw.old (22 : Fin 30)
    (18 : Fin 30) (20 : Fin 30) (5 : Fin 30)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (10 : Fin 30) (6 : Fin 30) (5 : Fin 30))) (.conj
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (10 : Fin 30) (6 : Fin 30) (5 : Fin 30)))
    (.conj (ConstructionMergerCopyCones.hasConeJoins (18 : Fin 30) (14 : Fin 30) (11 : Fin 30))
    (.conj (ConstructionProbeSharedIntersections.conditionalJoins (10 : Fin 30) (6 : Fin 30)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (22 : Fin 30) (18 : Fin 30) (4 : Fin 30)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (18 : Fin 30) (10 : Fin 30) (19 : Fin 30) (6 :
    Fin 30) (4 : Fin 30)) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (19 : Fin 30) (6
    : Fin 30) (4 : Fin 30)) (.conj (ConstructionPersistentProfiles.hasOldGates (18 : Fin 30) (10 :
    Fin 30) (19 : Fin 30) (6 : Fin 30) (4 : Fin 30)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.edge (4 : Fin 30) (20 : Fin 30) (5 : Fin 30))) (.conj (.forallE (.forallE
    (.forallE (.forallE (.forallE (.imp (ConstructionPersistentProfiles.probeProfile (21 : Fin 35)
    (23 : Fin 35) (24 : Fin 35) (4 : Fin 35) (3 : Fin 35) (2 : Fin 35) (1 : Fin 35) (0 : Fin 35))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (5 : Fin 40) (14 : Fin 40) (4 : Fin 40)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 40) (9 : Fin 40) (3 : Fin 40)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 40) (8 : Fin 40) (2 : Fin
    40))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 40) (7 : Fin 40) (1 :
    Fin 40))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 40) (6 : Fin 40) (0
    : Fin 40))) (ConstructionPersistentProfiles.probeProfile (26 : Fin 40) (20 : Fin 40) (16 : Fin
    40) (3 : Fin 40) (2 : Fin 40) (1 : Fin 40) (0 : Fin 40) (4 : Fin 40)))))))))))))))))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 30) (17 : Fin 30) (10 : Fin 30)))
    (.conj (ConstructionMergerRoots.rootGraph (16 : Fin 30) (18 : Fin 30) (14 : Fin 30) (20 : Fin
    30) (13 : Fin 30) (5 : Fin 30) (3 : Fin 30)) (.conj (ConstructionMergerRoots.rootLaws (16 : Fin
    30) (18 : Fin 30) (14 : Fin 30) (17 : Fin 30) (19 : Fin 30) (21 : Fin 30) (13 : Fin 30) (5 : Fin
    30) (6 : Fin 30) (4 : Fin 30) (3 : Fin 30)) (.conj (ConstructionProbeLetters.representatives (17
    : Fin 30) (14 : Fin 30) (2 : Fin 30)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (1 : Fin 30) (2 : Fin 30) (24 : Fin 30))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 30) (2 : Fin 30) (24 : Fin 30))) (.conj
    (ConstructionMergerCoordinates.graph (17 : Fin 30) (14 : Fin 30) (13 : Fin 30) (25 : Fin 30) (22
    : Fin 30) (1 : Fin 30)) (.conj (ConstructionMergerCoordinates.graph (17 : Fin 30) (14 : Fin 30)
    (13 : Fin 30) (26 : Fin 30) (27 : Fin 30) (0 : Fin 30)) (.conj
    (ConstructionMergerCoordinateLaws.laws (17 : Fin 30) (18 : Fin 30) (14 : Fin 30) (11 : Fin 30)
    (13 : Fin 30) (25 : Fin 30) (26 : Fin 30) (22 : Fin 30) (27 : Fin 30) (1 : Fin 30) (0 : Fin 30))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.conj (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (35 : Fin 40) (30 :
    Fin 40) (9 : Fin 40))) (.conj (ConstructionProbeLetters.representatives (34 : Fin 40) (34 : Fin
    40) (8 : Fin 40)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 40) (8 :
    Fin 40) (34 : Fin 40))) (.conj (ConstructionCutArithmeticSyntax.graph (26 : Fin 40) (33 : Fin
    40) (34 : Fin 40) (7 : Fin 40)) (.conj (ConstructionProbeLetters.representatives (34 : Fin 40)
    (34 : Fin 40) (6 : Fin 40)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin
    40) (6 : Fin 40) (34 : Fin 40))) (.conj (ConstructionWordArithmeticSyntax.graph (26 : Fin 40)
    (33 : Fin 40) (34 : Fin 40) (5 : Fin 40)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (4 : Fin 40) (34 : Fin 40) (34 : Fin 40))) (.conj
    (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (34 : Fin 40) (4 : Fin 40)))
    (.conj (Project.Formula.isSuccessor (.bound 3) (.bound 38)) (.conj (.mem (.bound 3) (.bound 26))
    (.conj (.mem (.bound 2) (.bound 34)) (.conj (ConstructionCutDivision.value (26 : Fin 40) (33 :
    Fin 40) (3 : Fin 40) (9 : Fin 40) (2 : Fin 40)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (1 : Fin 40) (24 : Fin 40) (34 : Fin 40))) (.conj (.forallE (.forallE
    (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin 42) (1 : Fin 42) (0 : Fin 42)))
    (.conj (.mem (.bound 1) (.bound 26)) (ConstructionMergerFiniteWeights.heightValue (28 : Fin 42)
    (35 : Fin 42) (29 : Fin 42) (36 : Fin 42) (9 : Fin 42) (6 : Fin 42) (34 : Fin 42) (13 : Fin 42)
    (1 : Fin 42) (0 : Fin 42)))))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 :
    Fin 40) (24 : Fin 40) (34 : Fin 40))) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (2 : Fin 42) (1 : Fin 42) (0 : Fin 42))) (.conj (.mem (.bound 1)
    (.bound 26)) (ConstructionMergerFiniteWeights.costValue (28 : Fin 42) (35 : Fin 42) (29 : Fin
    42) (36 : Fin 42) (7 : Fin 42) (6 : Fin 42) (39 : Fin 42) (4 : Fin 42) (12 : Fin 42) (1 : Fin
    42) (0 : Fin 42)))))) (.conj (.forallE (.imp (.mem (.bound 0) (.bound 35)) (ProjectSyntax.encode
    id (ForcingDiagramOrder.product (6 : Fin 41) (0 : Fin 41) (38 : Fin 41) (0 : Fin 41)))))
    (.forallE (.imp (.mem (.bound 0) (.bound 35)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (8 : Fin 41) (33 : Fin 41) (0 : Fin 41) (0 : Fin
    41))))))))))))))))))))))) (ConstructionMergerHeightCost.copiesHeightCost (26 : Fin 40) (33 : Fin
    40) (34 : Fin 40) (28 : Fin 40) (24 : Fin 40) (21 : Fin 40) (37 : Fin 40) (1 : Fin 40) (0 : Fin
    40))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionMergerCopies.copies_freeClosed,
      ConstructionMergerCopies.projectionGraph_freeClosed,ConstructionMergerCopies.equalityLaw_freeClosed,
      ConstructionMergerAction.actionTable_freeClosed,ConstructionMergerAction.rightFreeAction_freeClosed,
      ConstructionMergerAction.copyLaw_freeClosed,ConstructionProbeRaw.carrier_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,ConstructionMergerWordProduct.laws_freeClosed,
      ConstructionProbeRaw.old_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionMergerCopyCones.hasConeJoins_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionPersistentProfiles.hasOldGates_freeClosed,ConstructionPersistentProfiles.probeProfile_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionMergerRoots.rootGraph_freeClosed,
      ConstructionMergerRoots.rootLaws_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,ConstructionMergerCoordinates.graph_freeClosed,ConstructionMergerCoordinateLaws.laws_freeClosed,
      Project.Formula.isOrdinalOne,Project.Formula.isSuccessor,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      ConstructionRealCuts.principal_freeClosed,ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionWordArithmeticSyntax.graph_freeClosed,ConstructionCutDivision.value_freeClosed,
      ConstructionMergerFiniteWeights.heightValue_freeClosed,ConstructionMergerFiniteWeights.costValue_freeClosed,
      ConstructionMergerHeightCost.copiesHeightCost_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeRaw.old_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeLetters.representatives_semantics hM,ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,ConstructionMergerCopies.copies_semantics hM,
    ConstructionMergerCopies.projectionGraph_semantics hM,ConstructionMergerCopies.equalityLaw_semantics hM,
    ConstructionMergerAction.actionTable_semantics hM,ConstructionMergerAction.rightFreeAction_semantics hM,
    ConstructionMergerAction.copyLaw_semantics hM,ConstructionProbeRaw.carrier_semantics hM,
    ConstructionMergerWordAction.actionTable_semantics hM,ConstructionMergerWordProduct.laws_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionMergerCopyCones.hasConeJoins_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,ConstructionPersistentProfiles.hasOldGates_semantics hM,
    ConstructionPersistentProfiles.probeProfile_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    KuratowskiZF.source_edge,ConstructionMergerRoots.rootGraph_semantics hM,ConstructionMergerRoots.rootLaws_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,ConstructionMergerCoordinates.graph_semantics hM,ConstructionMergerCoordinateLaws.laws_semantics hM,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_isSuccessor_iff,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionFractionOrder.coordinates_semantics hM,
    ConstructionRealCuts.principal_semantics hM,ConstructionCutArithmeticSyntax.graph_semantics hM,
    ConstructionWordArithmeticSyntax.graph_semantics hM,ConstructionCutDivision.value_semantics hM,
    ForcingConditionGraphs.identityGraph_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),
    ConstructionMergerFiniteWeights.heightValue_semantics hM,ConstructionMergerFiniteWeights.costValue_semantics hM,
    ConstructionMergerHeightCost.copiesHeightCost_semantics hM]
  intro hQ hn hnp hu hone hunit hR hHeight hHB hCost hCB hUniform hw hz hzw hm hc hJoins hP hValid
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hHeightCost⟩ :=
    ConstructionMergerHeightCost.exists_system hM hw hz hzw hm hc hJoins hP hValid hQ hn hnp hu hone hunit hR hHeight hHB hCost hCB hUniform
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,O,F,J,CH,CC,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,hO,hCons,hPres,hGates,hEdge,hProfiles,hF,hRoots,hRootLaws,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hHeightCost⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerHeightCostSyntax
