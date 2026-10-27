/- Pinned MonoidTowers.DirectedColimit.cocone/lift/isColimit:84-168.
Pure forall13 producer: SAME nine weighted/pointed limit objects, actual
canonical cocone graph family, full weighted conservative lift/fac/uniq.
The final tower/request schedule and internal Con sentence remain open. -/
import PPAC.Migration.ConstructionDirectedColimit
import PPAC.Migration.ConstructionProbeLiftHomSyntax

namespace PPAC.Migration.ConstructionDirectedColimitSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13 (.imp (.existsE (.mem (.bound (0 : Fin 14)) (.bound (1 : Fin
    14)))) (.imp (ConstructionDirectedSystem.indexLaws (0 : Fin 13) (1 : Fin 13)) (.imp
    (ConstructionDirectedSystem.transitionLaws (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (3 : Fin 13)) (.imp
    (ConstructionDirectedMonoidData.family (0 : Fin 13) (2 : Fin 13) (4 : Fin 13) (5 : Fin 13)) (.imp
    (ConstructionDirectedMonoidData.homLaws (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (3 : Fin 13) (4 : Fin 13)
    (5 : Fin 13)) (.imp (ConstructionDirectedConservativeData.conservativeTransitions (0 : Fin 13) (1 : Fin
    13) (2 : Fin 13) (3 : Fin 13) (4 : Fin 13)) (.imp (Project.Formula.isOmega (.bound (6 : Fin 13))) (.imp
    (ConstructionFractionOrder.carrier (6 : Fin 13) (7 : Fin 13)) (.imp (ConstructionRealCuts.cutCarrier (6
    : Fin 13) (7 : Fin 13) (8 : Fin 13)) (.imp (ConstructionRealCuts.cut (6 : Fin 13) (7 : Fin 13) (9 : Fin
    13)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 13) (2 : Fin 13) (8 : Fin 13) (10 : Fin
    13)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 13) (2 : Fin 13) (8 : Fin 13) (11 : Fin
    13)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (3 : Fin 13)
    (10 : Fin 13)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (3 :
    Fin 13) (11 : Fin 13)) (.imp (ConstructionDirectedWeightData.heightBounds (0 : Fin 13) (10 : Fin 13) (9
    : Fin 13)) (.imp (ConstructionDirectedWeightData.costBounds (0 : Fin 13) (11 : Fin 13) (9 : Fin 13))
    (.imp (ConstructionDirectedWeightData.uniformFamily (6 : Fin 13) (7 : Fin 13) (0 : Fin 13) (2 : Fin 13)
    (4 : Fin 13) (10 : Fin 13) (11 : Fin 13)) (.imp (ConstructionDirectedWeightData.supremumLaws (0 : Fin
    13) (1 : Fin 13) (2 : Fin 13) (3 : Fin 13) (4 : Fin 13) (11 : Fin 13)) (.imp
    (ConstructionDirectedMonoidData.conicalFamily (0 : Fin 13) (2 : Fin 13) (4 : Fin 13) (5 : Fin 13)) (.imp
    (ConstructionDirectedConservativeData.joinsFamily (0 : Fin 13) (2 : Fin 13) (4 : Fin 13) (5 : Fin 13))
    (.imp (ConstructionDirectedMarks.markFamily (0 : Fin 13) (2 : Fin 13) (5 : Fin 13) (12 : Fin 13)) (.imp
    (ConstructionDirectedMarks.stable (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (3 : Fin 13) (12 : Fin 13))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionDirectedLimitCarrier.representatives (7 : Fin 20) (9 : Fin 20) (6 : Fin 20)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (4 : Fin 20) (6 : Fin 20) (5 : Fin 20))) (.conj
    (ConstructionDirectedLimitCarrier.carrier (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 : Fin 20) (6 : Fin
    20) (5 : Fin 20)) (.conj (ConstructionDirectedLimitCarrier.projectionGraph (7 : Fin 20) (8 : Fin 20) (9
    : Fin 20) (10 : Fin 20) (6 : Fin 20) (4 : Fin 20)) (.conj (ConstructionDirectedLimitCarrier.equalityLaw
    (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 : Fin 20) (4 : Fin 20)) (.conj
    (ConstructionProbeLetters.representatives (5 : Fin 20) (5 : Fin 20) (3 : Fin 20)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 20) (3 : Fin 20) (5 : Fin 20))) (.conj
    (ConstructionDirectedProduct.graph (7 : Fin 20) (9 : Fin 20) (11 : Fin 20) (4 : Fin 20) (2 : Fin 20))
    (.conj (.mem (.bound (1 : Fin 20)) (.bound (5 : Fin 20))) (.conj (ConstructionDirectedMonoid.unitImage
    (7 : Fin 20) (9 : Fin 20) (12 : Fin 20) (4 : Fin 20) (1 : Fin 20)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (5 : Fin 20) (2 : Fin 20) (1 : Fin 20))) (.conj
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (5 : Fin 20) (2 : Fin 20) (1 : Fin 20))) (.conj
    (ConstructionProbeSharedIntersections.conditionalJoins (5 : Fin 20) (2 : Fin 20)) (.conj (.mem (.bound
    (0 : Fin 20)) (.bound (5 : Fin 20))) (.conj (.neg (Project.Formula.extensionalEq (.bound (0 : Fin 20))
    (.bound (1 : Fin 20)))) (.conj (ConstructionDirectedMarks.markImage (7 : Fin 20) (19 : Fin 20) (4 : Fin
    20) (0 : Fin 20)) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin 24))
    (.bound (11 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (13 : Fin 24) (3 : Fin
    24) (2 : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (15 : Fin 24) (3 : Fin 24) (1
    : Fin 24))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (16 : Fin 24) (3 : Fin 24) (0 : Fin
    24))) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 25) (3 : Fin 25) (10
    : Fin 25))) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin
    27) (1 : Fin 27) (0 : Fin 27))) (.conj (.mem (.bound (1 : Fin 27)) (.bound (5 : Fin 27)))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (11 : Fin 27) (6 : Fin 27) (1 : Fin 27) (0 : Fin
    27))))))) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (2 : Fin 25) (7 : Fin 25) (0 : Fin
    25)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin 25) (1 : Fin 25) (6 : Fin 25)))
    (.conj (ConstructionProbeConservativeSyntax.conservative (3 : Fin 25) (10 : Fin 25) (2 : Fin 25) (7 :
    Fin 25) (0 : Fin 25)) (.conj (ConstructionDirectedProfiles.profileTransport (12 : Fin 25) (13 : Fin 25)
    (14 : Fin 25) (15 : Fin 25) (16 : Fin 25) (4 : Fin 25) (3 : Fin 25) (10 : Fin 25) (7 : Fin 25) (0 : Fin
    25)) (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (25 : Fin 26) (5 : Fin 26) (0 :
    Fin 26))) (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin 26) (0 : Fin 26) (6 : Fin
    26)))))))))))))))))))) (.existsE (.existsE (.conj (ConstructionDirectedHeightCost.laws (15 : Fin 22) (16
    : Fin 22) (17 : Fin 22) (18 : Fin 22) (9 : Fin 22) (11 : Fin 22) (13 : Fin 22) (19 : Fin 22) (20 : Fin
    22) (7 : Fin 22) (6 : Fin 22) (4 : Fin 22) (1 : Fin 22) (0 : Fin 22))
    (.conj (ConstructionDirectedCardinality.boundProperty (9 : Fin 22) (11 : Fin 22) (7 : Fin
    22)) (ConstructionDirectedColimit.colimit (9 : Fin 22) (10 : Fin 22) (11 : Fin 22) (12 : Fin 22) (13 : Fin 22) (14 : Fin 22) (19 : Fin 22) (20 : Fin 22) (21 : Fin 22) (7 : Fin 22) (6 : Fin 22) (4 : Fin 22) (3 : Fin 22) (2 : Fin 22) (1 : Fin 22) (0 : Fin 22))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,
      ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedMonoidData.homLaws_freeClosed,
      ConstructionDirectedMonoidData.conicalFamily_freeClosed,ConstructionDirectedConservativeData.joinsFamily_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,
      ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,ConstructionDirectedLimitCarrier.equalityLaw_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionDirectedProduct.graph_freeClosed,
      ConstructionDirectedProfiles.profileTransport_freeClosed,ConstructionDirectedMonoid.unitImage_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionDirectedHeightCost.laws_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionDirectedWeightData.heightBounds_freeClosed,ConstructionDirectedWeightData.costBounds_freeClosed,ConstructionDirectedWeightData.uniformFamily_freeClosed,ConstructionDirectedWeightData.supremumLaws_freeClosed,Project.Formula.extensionalEq,ConstructionDirectedMarks.markFamily_freeClosed,ConstructionDirectedMarks.stable_freeClosed,ConstructionDirectedMarks.markImage_freeClosed,ConstructionDirectedCardinality.boundProperty_freeClosed,ConstructionDirectedColimit.colimit_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,
    ConstructionDirectedMonoidData.family_semantics hM,ConstructionDirectedMonoidData.homLaws_semantics hM,
    ConstructionDirectedMonoidData.conicalFamily_semantics hM,ConstructionDirectedConservativeData.joinsFamily_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionDirectedConservativeData.conservativeTransitions_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionDirectedLimitCarrier.representatives_semantics hM,ConstructionDirectedLimitCarrier.carrier_semantics hM,
    ConstructionDirectedLimitCarrier.projectionGraph_semantics hM,ConstructionDirectedLimitCarrier.equalityLaw_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ConstructionDirectedProduct.graph_semantics hM,
    ConstructionDirectedProfiles.profileTransport_semantics hM,ConstructionDirectedMonoid.unitImage_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionDirectedWeightData.heightBounds_semantics hM,ConstructionDirectedWeightData.costBounds_semantics hM,ConstructionDirectedWeightData.uniformFamily_semantics hM,ConstructionDirectedWeightData.supremumLaws_semantics hM,ConstructionDirectedHeightCost.laws_semantics hM,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionDirectedMarks.markFamily_semantics hM,ConstructionDirectedMarks.stable_semantics hM,ConstructionDirectedMarks.markImage_semantics hM,ConstructionDirectedCardinality.boundProperty_semantics hM,ConstructionDirectedColimit.colimit_semantics hM]
  intro hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable
  exact ConstructionDirectedColimit.exists_system hM (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) (bound 6) (bound 7) (bound 8) (bound 9) (bound 10) (bound 11) (bound 12) hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionDirectedColimitSyntax
