/- Original-kernel certificate for actual Merger coordinate tables and laws.
Keeps SAME copies/Word/old inclusion/roots and every old profile, under old
weighted parent contracts and supplied old unit-bound cut. Literal defaults
are empty cut and that unit cut; complete averaged/product weights and Con
remain open. No new coordinate graph or monotonicity is assumed. -/
import PPAC.Migration.ConstructionMergerCoordinateLaws
import PPAC.Migration.ConstructionProbeMappedPathSyntax
import PPAC.Migration.ConstructionProbeIntervalsSyntax

namespace PPAC.Migration.ConstructionMergerCoordinateSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 12
    (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 12) (7 : Fin 12) (8 : Fin 12)) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (9 : Fin 12) (2 : Fin 12) (8 : Fin 12))) (.imp
    (ConstructionCutWeights.rangeBound (11 : Fin 12) (9 : Fin 12)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (10 : Fin 12) (2 : Fin 12) (8 : Fin 12))) (.imp (ConstructionProbeGateCap.bounds
    (11 : Fin 12) (10 : Fin 12)) (.imp (.mem (.bound (11 : Fin 12)) (.bound (8 : Fin 12))) (.imp
    (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 12) (7 : Fin 12) (2 : Fin 12) (3 : Fin 12) (9 :
    Fin 12) (10 : Fin 12)) (.imp (Project.Formula.isOmega (.bound (0 : Fin 12))) (.imp (Project.Formula.isEmpty
    (.bound (6 : Fin 12))) (.imp (.mem (.bound (6 : Fin 12)) (.bound (0 : Fin 12))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 12) (3 : Fin 12) (4 : Fin 12))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (2 : Fin 12) (3 : Fin 12) (4 : Fin 12))) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (2 : Fin 12) (3 : Fin 12)) (.imp
    (ConstructionMergerRelations.prescription (1 : Fin 12) (2 : Fin 12) (5 : Fin 12)) (.imp
    (ConstructionMergerRelations.valid (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (5 : Fin 12)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.conj (.conj (ConstructionProbeLetters.representatives (17 : Fin
    28) (18 : Fin 28) (15 : Fin 28)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 28)
    (15 : Fin 28) (14 : Fin 28))) (.conj (ConstructionMergerCopies.copies (17 : Fin 28) (18 : Fin 28) (19 : Fin
    28) (21 : Fin 28) (15 : Fin 28) (14 : Fin 28)) (.conj (ConstructionMergerCopies.projectionGraph (17 : Fin
    28) (18 : Fin 28) (19 : Fin 28) (21 : Fin 28) (15 : Fin 28) (13 : Fin 28)) (.conj
    (ConstructionMergerCopies.equalityLaw (17 : Fin 28) (18 : Fin 28) (19 : Fin 28) (21 : Fin 28) (13 : Fin 28))
    (.conj (ConstructionProbeLetters.representatives (14 : Fin 28) (18 : Fin 28) (12 : Fin 28)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 28) (12 : Fin 28) (14 : Fin 28))) (.conj
    (ConstructionMergerAction.actionTable (18 : Fin 28) (19 : Fin 28) (13 : Fin 28) (11 : Fin 28)) (.conj
    (ConstructionMergerAction.rightFreeAction (19 : Fin 28) (20 : Fin 28) (14 : Fin 28) (11 : Fin 28)) (.conj
    (ConstructionMergerAction.copyLaw (18 : Fin 28) (19 : Fin 28) (13 : Fin 28) (11 : Fin 28)) (.conj
    (ConstructionProbeRaw.carrier (16 : Fin 28) (18 : Fin 28) (14 : Fin 28) (10 : Fin 28)) (.conj
    (ConstructionProbeLetters.representatives (10 : Fin 28) (18 : Fin 28) (9 : Fin 28)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 28) (9 : Fin 28) (10 : Fin 28))) (.conj
    (ConstructionMergerWordAction.actionTable (16 : Fin 28) (18 : Fin 28) (14 : Fin 28) (22 : Fin 28) (19 : Fin
    28) (11 : Fin 28) (8 : Fin 28)) (.conj (ConstructionMergerAction.rightFreeAction (19 : Fin 28) (20 : Fin 28)
    (10 : Fin 28) (8 : Fin 28)) (.conj (ConstructionProbeLetters.representatives (10 : Fin 28) (10 : Fin 28) (7
    : Fin 28)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 28) (7 : Fin 28) (10 : Fin
    28))) (ConstructionMergerWordProduct.laws (16 : Fin 28) (18 : Fin 28) (14 : Fin 28) (22 : Fin 28) (8 : Fin
    28) (6 : Fin 28))))))))))))))))))) (.conj (ConstructionProbeRaw.old (22 : Fin 28) (18 : Fin 28) (20 : Fin
    28) (5 : Fin 28)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (10 : Fin 28) (6 :
    Fin 28) (5 : Fin 28))) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical (10 : Fin 28) (6 : Fin
    28) (5 : Fin 28))) (.conj (ConstructionMergerCopyCones.hasConeJoins (18 : Fin 28) (14 : Fin 28) (11 : Fin
    28)) (.conj (ConstructionProbeSharedIntersections.conditionalJoins (10 : Fin 28) (6 : Fin 28)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (22 : Fin 28) (18 : Fin 28) (4 : Fin 28)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (18 : Fin 28) (10 : Fin 28) (19 : Fin 28) (6 : Fin 28) (4
    : Fin 28)) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (19 : Fin 28) (6 : Fin 28) (4 : Fin 28))
    (.conj (ConstructionPersistentProfiles.hasOldGates (18 : Fin 28) (10 : Fin 28) (19 : Fin 28) (6 : Fin 28) (4
    : Fin 28)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin 28) (20 : Fin 28) (5 : Fin
    28))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (ConstructionPersistentProfiles.probeProfile (21 : Fin 33) (23 : Fin 33) (24 : Fin 33) (4 : Fin 33) (3 : Fin
    33) (2 : Fin 33) (1 : Fin 33) (0 : Fin 33)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (5 : Fin 38) (14 : Fin 38) (4 : Fin 38)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 38) (9 : Fin 38) (3 : Fin 38))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 38) (8 : Fin 38) (2 : Fin 38))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 38) (7 : Fin 38) (1 : Fin 38))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 38) (6 : Fin 38) (0 : Fin 38)))
    (ConstructionPersistentProfiles.probeProfile (26 : Fin 38) (20 : Fin 38) (16 : Fin 38) (3 : Fin 38) (2 : Fin
    38) (1 : Fin 38) (0 : Fin 38) (4 : Fin 38)))))))))))))))))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (3 : Fin 28) (17 : Fin 28) (10 : Fin 28))) (.conj
    (ConstructionMergerRoots.rootGraph (16 : Fin 28) (18 : Fin 28) (14 : Fin 28) (20 : Fin 28) (13 : Fin 28) (5
    : Fin 28) (3 : Fin 28)) (.conj (ConstructionMergerRoots.rootLaws (16 : Fin 28) (18 : Fin 28) (14 : Fin 28)
    (17 : Fin 28) (19 : Fin 28) (21 : Fin 28) (13 : Fin 28) (5 : Fin 28) (6 : Fin 28) (4 : Fin 28) (3 : Fin 28))
    (.conj (ConstructionProbeLetters.representatives (17 : Fin 28) (14 : Fin 28) (2 : Fin 28)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 28) (2 : Fin 28) (24 : Fin 28))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 28) (2 : Fin 28) (24 : Fin 28))) (.conj
    (ConstructionMergerCoordinates.graph (17 : Fin 28) (14 : Fin 28) (13 : Fin 28) (25 : Fin 28) (22 : Fin 28)
    (1 : Fin 28)) (.conj (ConstructionMergerCoordinates.graph (17 : Fin 28) (14 : Fin 28) (13 : Fin 28) (26 :
    Fin 28) (27 : Fin 28) (0 : Fin 28)) (ConstructionMergerCoordinateLaws.laws (17 : Fin 28) (18 : Fin 28) (14 :
    Fin 28) (11 : Fin 28) (13 : Fin 28) (25 : Fin 28) (26 : Fin 28) (22 : Fin 28) (27 : Fin 28) (1 : Fin 28) (0
    : Fin 28)))))))))))))))))))))))))))))))))))))))))))))))))))))
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
      ConstructionMergerRoots.rootLaws_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,ConstructionMergerCoordinates.graph_freeClosed,ConstructionMergerCoordinateLaws.laws_freeClosed]

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
    KuratowskiZF.source_edge,ConstructionMergerRoots.rootGraph_semantics hM,ConstructionMergerRoots.rootLaws_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,ConstructionMergerCoordinates.graph_semantics hM,ConstructionMergerCoordinateLaws.laws_semantics hM]
  intro hR hHeight hHB hCost hCB htop hUniform hw hz hzw hm hc hJoins hP hValid
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws⟩ :=
    ConstructionMergerCoordinateLaws.exists_system hM hw hz hzw hm hc hJoins hP hValid hR hHeight hHB hCost hCB htop hUniform
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,O,F,J,CH,CC,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,hO,hCons,hPres,hGates,hEdge,hProfiles,hF,hRoots,hRootLaws,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerCoordinateSyntax
