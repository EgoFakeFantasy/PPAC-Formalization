/- Original-kernel certificate for SAME actual Merger Word, old inclusion and roots.
Includes full Conservative, old gates, all old profile preservation and exact
prescribed root relation. No supplied new graph/law/profile or internal Choice.
Weights/cardinality/full MergerData and final Con remain open. -/
import PPAC.Migration.ConstructionMergerRoots
import PPAC.Migration.ConstructionProbeMappedPathSyntax

namespace PPAC.Migration.ConstructionMergerRootsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 7))) (.imp (Project.Formula.isEmpty (.bound (6 : Fin 7)))
    (.imp (.mem (.bound (6 : Fin 7)) (.bound (0 : Fin 7))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 7) (3 : Fin 7) (4 : Fin 7))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical (2 : Fin 7) (3 : Fin 7) (4 : Fin 7))) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (2 : Fin 7) (3 : Fin 7)) (.imp
    (ConstructionMergerRelations.prescription (1 : Fin 7) (2 : Fin 7) (5 : Fin 7)) (.imp
    (ConstructionMergerRelations.valid (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.conj (.conj (ConstructionProbeLetters.representatives (14 : Fin 20) (15 : Fin 20) (12 : Fin 20))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 20) (12 : Fin 20) (11 : Fin 20)))
    (.conj (ConstructionMergerCopies.copies (14 : Fin 20) (15 : Fin 20) (16 : Fin 20) (18 : Fin 20) (12 : Fin
    20) (11 : Fin 20)) (.conj (ConstructionMergerCopies.projectionGraph (14 : Fin 20) (15 : Fin 20) (16 : Fin
    20) (18 : Fin 20) (12 : Fin 20) (10 : Fin 20)) (.conj (ConstructionMergerCopies.equalityLaw (14 : Fin 20)
    (15 : Fin 20) (16 : Fin 20) (18 : Fin 20) (10 : Fin 20)) (.conj (ConstructionProbeLetters.representatives
    (11 : Fin 20) (15 : Fin 20) (9 : Fin 20)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 :
    Fin 20) (9 : Fin 20) (11 : Fin 20))) (.conj (ConstructionMergerAction.actionTable (15 : Fin 20) (16 : Fin
    20) (10 : Fin 20) (8 : Fin 20)) (.conj (ConstructionMergerAction.rightFreeAction (16 : Fin 20) (17 : Fin 20)
    (11 : Fin 20) (8 : Fin 20)) (.conj (ConstructionMergerAction.copyLaw (15 : Fin 20) (16 : Fin 20) (10 : Fin
    20) (8 : Fin 20)) (.conj (ConstructionProbeRaw.carrier (13 : Fin 20) (15 : Fin 20) (11 : Fin 20) (7 : Fin
    20)) (.conj (ConstructionProbeLetters.representatives (7 : Fin 20) (15 : Fin 20) (6 : Fin 20)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 20) (6 : Fin 20) (7 : Fin 20))) (.conj
    (ConstructionMergerWordAction.actionTable (13 : Fin 20) (15 : Fin 20) (11 : Fin 20) (19 : Fin 20) (16 : Fin
    20) (8 : Fin 20) (5 : Fin 20)) (.conj (ConstructionMergerAction.rightFreeAction (16 : Fin 20) (17 : Fin 20)
    (7 : Fin 20) (5 : Fin 20)) (.conj (ConstructionProbeLetters.representatives (7 : Fin 20) (7 : Fin 20) (4 :
    Fin 20)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 20) (4 : Fin 20) (7 : Fin 20)))
    (ConstructionMergerWordProduct.laws (13 : Fin 20) (15 : Fin 20) (11 : Fin 20) (19 : Fin 20) (5 : Fin 20) (3
    : Fin 20))))))))))))))))))) (.conj (ConstructionProbeRaw.old (19 : Fin 20) (15 : Fin 20) (17 : Fin 20) (2 :
    Fin 20)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (7 : Fin 20) (3 : Fin 20) (2
    : Fin 20))) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical (7 : Fin 20) (3 : Fin 20) (2 : Fin
    20))) (.conj (ConstructionMergerCopyCones.hasConeJoins (15 : Fin 20) (11 : Fin 20) (8 : Fin 20)) (.conj
    (ConstructionProbeSharedIntersections.conditionalJoins (7 : Fin 20) (3 : Fin 20)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph (19 : Fin 20) (15 : Fin 20) (1 : Fin 20)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (15 : Fin 20) (7 : Fin 20) (16 : Fin 20) (3 : Fin 20) (1 :
    Fin 20)) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (16 : Fin 20) (3 : Fin 20) (1 : Fin 20))
    (.conj (ConstructionPersistentProfiles.hasOldGates (15 : Fin 20) (7 : Fin 20) (16 : Fin 20) (3 : Fin 20) (1
    : Fin 20)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin 20) (17 : Fin 20) (2 : Fin
    20))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (ConstructionPersistentProfiles.probeProfile (18 : Fin 25) (20 : Fin 25) (21 : Fin 25) (4 : Fin 25) (3 : Fin
    25) (2 : Fin 25) (1 : Fin 25) (0 : Fin 25)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (5 : Fin 30) (11 : Fin 30) (4 : Fin 30)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin 30) (9 : Fin 30) (3 : Fin 30))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin 30) (8 : Fin 30) (2 : Fin 30))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin 30) (7 : Fin 30) (1 : Fin 30))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin 30) (6 : Fin 30) (0 : Fin 30)))
    (ConstructionPersistentProfiles.probeProfile (23 : Fin 30) (17 : Fin 30) (13 : Fin 30) (3 : Fin 30) (2 : Fin
    30) (1 : Fin 30) (0 : Fin 30) (4 : Fin 30)))))))))))))))))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 20) (14 : Fin 20) (7 : Fin 20))) (.conj
    (ConstructionMergerRoots.rootGraph (13 : Fin 20) (15 : Fin 20) (11 : Fin 20) (17 : Fin 20) (10 : Fin 20) (2
    : Fin 20) (0 : Fin 20)) (ConstructionMergerRoots.rootLaws (13 : Fin 20) (15 : Fin 20) (11 : Fin 20) (14 :
    Fin 20) (16 : Fin 20) (18 : Fin 20) (10 : Fin 20) (2 : Fin 20) (3 : Fin 20) (1 : Fin 20) (0 : Fin
    20)))))))))))))))))))))))))))))))))))))
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
      ConstructionMergerRoots.rootLaws_freeClosed]

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
    KuratowskiZF.source_edge,ConstructionMergerRoots.rootGraph_semantics hM,ConstructionMergerRoots.rootLaws_semantics hM]
  intro hw hz hzw hm hc hJoins hP hValid
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws⟩ :=
    ConstructionMergerRoots.exists_system hM hw hz hzw hm hc hJoins hP hValid
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,O,F,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,hO,hCons,hPres,hGates,hEdge,hProfiles,hF,hRoots,hRootLaws⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerRootsSyntax
