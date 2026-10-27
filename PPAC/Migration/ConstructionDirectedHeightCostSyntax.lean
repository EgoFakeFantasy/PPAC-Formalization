/- Pinned DirectLimits.height/cost/old_cost_supremum/heightCost. Pure forall12
native-ZF producer constructs SAME actual limit monoid plus BOTH weight graphs,
complete actual strict supremum margins and ALL old pair suprema. Source stage
weight/margin/stability/exact-supremum premises remain explicit. -/
import PPAC.Migration.ConstructionDirectedHeightCost
import PPAC.Migration.ConstructionProbeLiftHomSyntax

namespace PPAC.Migration.ConstructionDirectedHeightCostSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 12 (.imp (.existsE (.mem (.bound (0 : Fin 13)) (.bound (1 : Fin
    13)))) (.imp (ConstructionDirectedSystem.indexLaws (0 : Fin 12) (1 : Fin 12)) (.imp
    (ConstructionDirectedSystem.transitionLaws (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12)) (.imp
    (ConstructionDirectedMonoidData.family (0 : Fin 12) (2 : Fin 12) (4 : Fin 12) (5 : Fin 12)) (.imp
    (ConstructionDirectedMonoidData.homLaws (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 : Fin 12)
    (5 : Fin 12)) (.imp (ConstructionDirectedConservativeData.conservativeTransitions (0 : Fin 12) (1 : Fin
    12) (2 : Fin 12) (3 : Fin 12) (4 : Fin 12)) (.imp (Project.Formula.isOmega (.bound (6 : Fin 12))) (.imp
    (ConstructionFractionOrder.carrier (6 : Fin 12) (7 : Fin 12)) (.imp (ConstructionRealCuts.cutCarrier (6
    : Fin 12) (7 : Fin 12) (8 : Fin 12)) (.imp (ConstructionRealCuts.cut (6 : Fin 12) (7 : Fin 12) (9 : Fin
    12)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 12) (2 : Fin 12) (8 : Fin 12) (10 : Fin
    12)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 12) (2 : Fin 12) (8 : Fin 12) (11 : Fin
    12)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12)
    (10 : Fin 12)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 :
    Fin 12) (11 : Fin 12)) (.imp (ConstructionDirectedWeightData.heightBounds (0 : Fin 12) (10 : Fin 12) (9
    : Fin 12)) (.imp (ConstructionDirectedWeightData.costBounds (0 : Fin 12) (11 : Fin 12) (9 : Fin 12))
    (.imp (ConstructionDirectedWeightData.uniformFamily (6 : Fin 12) (7 : Fin 12) (0 : Fin 12) (2 : Fin 12)
    (4 : Fin 12) (10 : Fin 12) (11 : Fin 12)) (.imp (ConstructionDirectedWeightData.supremumLaws (0 : Fin
    12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 : Fin 12) (11 : Fin 12)) (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.conj (ConstructionDirectedLimitCarrier.representatives (6 : Fin 18) (8 :
    Fin 18) (5 : Fin 18)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 18) (5 : Fin
    18) (4 : Fin 18))) (.conj (ConstructionDirectedLimitCarrier.carrier (6 : Fin 18) (7 : Fin 18) (8 : Fin
    18) (9 : Fin 18) (5 : Fin 18) (4 : Fin 18)) (.conj (ConstructionDirectedLimitCarrier.projectionGraph (6
    : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (5 : Fin 18) (3 : Fin 18)) (.conj
    (ConstructionDirectedLimitCarrier.equalityLaw (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (3 :
    Fin 18)) (.conj (ConstructionProbeLetters.representatives (4 : Fin 18) (4 : Fin 18) (2 : Fin 18)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 18) (2 : Fin 18) (4 : Fin 18))) (.conj
    (ConstructionDirectedProduct.graph (6 : Fin 18) (8 : Fin 18) (10 : Fin 18) (3 : Fin 18) (1 : Fin 18))
    (.conj (.mem (.bound (0 : Fin 18)) (.bound (4 : Fin 18))) (.conj (ConstructionDirectedMonoid.unitImage
    (6 : Fin 18) (8 : Fin 18) (11 : Fin 18) (3 : Fin 18) (0 : Fin 18)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 18) (1 : Fin 18) (0 : Fin 18))) (.conj (.imp
    (ConstructionDirectedMonoidData.conicalFamily (6 : Fin 18) (8 : Fin 18) (10 : Fin 18) (11 : Fin 18))
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (4 : Fin 18) (1 : Fin 18) (0 : Fin 18)))) (.conj
    (.imp (ConstructionDirectedConservativeData.joinsFamily (6 : Fin 18) (8 : Fin 18) (10 : Fin 18) (11 :
    Fin 18)) (ConstructionProbeSharedIntersections.conditionalJoins (4 : Fin 18) (1 : Fin 18))) (.conj
    (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin 22)) (.bound (10 : Fin 22))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 22) (3 : Fin 22) (2 : Fin 22))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 22) (3 : Fin 22) (1 : Fin 22))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (15 : Fin 22) (3 : Fin 22) (0 : Fin 22))) (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 23) (3 : Fin 23) (9 : Fin 23)))
    (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin 25) (1 : Fin
    25) (0 : Fin 25))) (.conj (.mem (.bound (1 : Fin 25)) (.bound (5 : Fin 25))) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (10 : Fin 25) (6 : Fin 25) (1 : Fin 25) (0 : Fin 25))))))) (.conj
    (ConstructionProbeLiftHomSyntax.preservesProducts (2 : Fin 23) (6 : Fin 23) (0 : Fin 23)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin 23) (1 : Fin 23) (5 : Fin 23))) (.conj
    (ConstructionProbeConservativeSyntax.conservative (3 : Fin 23) (9 : Fin 23) (2 : Fin 23) (6 : Fin 23) (0
    : Fin 23)) (ConstructionDirectedProfiles.profileTransport (11 : Fin 23) (12 : Fin 23) (13 : Fin 23) (14
    : Fin 23) (15 : Fin 23) (4 : Fin 23) (3 : Fin 23) (9 : Fin 23) (6 : Fin 23) (0 : Fin 23))))))))))))))))
    (.existsE (.existsE (ConstructionDirectedHeightCost.laws (14 : Fin 20) (15 : Fin 20) (16 : Fin 20) (17 :
    Fin 20) (8 : Fin 20) (10 : Fin 20) (12 : Fin 20) (18 : Fin 20) (19 : Fin 20) (6 : Fin 20) (5 : Fin 20)
    (3 : Fin 20) (1 : Fin 20) (0 : Fin 20))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,
      ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedMonoidData.homLaws_freeClosed,
      ConstructionDirectedMonoidData.conicalFamily_freeClosed,ConstructionDirectedConservativeData.joinsFamily_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,
      ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,ConstructionDirectedLimitCarrier.equalityLaw_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionDirectedProduct.graph_freeClosed,
      ConstructionDirectedProfiles.profileTransport_freeClosed,ConstructionDirectedMonoid.unitImage_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionDirectedHeightCost.laws_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionDirectedWeightData.heightBounds_freeClosed,ConstructionDirectedWeightData.costBounds_freeClosed,ConstructionDirectedWeightData.uniformFamily_freeClosed,ConstructionDirectedWeightData.supremumLaws_freeClosed]

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
    ConstructionDirectedProfiles.profileTransport_semantics hM,ConstructionDirectedMonoid.unitImage_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionDirectedWeightData.heightBounds_semantics hM,ConstructionDirectedWeightData.costBounds_semantics hM,ConstructionDirectedWeightData.uniformFamily_semantics hM,ConstructionDirectedWeightData.supremumLaws_semantics hM,ConstructionDirectedHeightCost.laws_semantics hM]
  intro hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup
  exact ConstructionDirectedHeightCost.exists_system hM (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) (bound 6) (bound 7) (bound 8) (bound 9) (bound 10) (bound 11) hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionDirectedHeightCostSyntax
