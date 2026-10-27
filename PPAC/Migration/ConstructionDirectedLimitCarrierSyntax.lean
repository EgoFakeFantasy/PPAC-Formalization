/- Pinned DirectLimits.ConservativeLimit underlying carrier and of:19,
of_map:29, of_injective:62. Actual varying-carrier common-future quotient,
same global projection, EVERY actual stage inclusion graph and actual pair/triple common-stage representation, with exact
transition/equality laws. All internal arbitrary directed PREORDER indices.
Injectivity is conditional ONLY in conclusion. No chosen representatives,
external standardness/well-foundedness, new quotient or recursion backend.
Multiplication/conservativity/weights/final tower/Con are not claimed. -/
import PPAC.Migration.ConstructionDirectedLimitCarrier

namespace PPAC.Migration.ConstructionDirectedLimitCarrierSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (ConstructionDirectedSystem.indexLaws (0 : Fin 4) (1 : Fin 4)) (.imp
    (ConstructionDirectedSystem.transitionLaws (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)) (.existsE
    (.existsE (.existsE (.conj (ConstructionDirectedLimitCarrier.representatives (3 : Fin 7) (5 : Fin 7)
    (2 : Fin 7)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 7) (2 : Fin 7) (1 :
    Fin 7))) (.conj (ConstructionDirectedLimitCarrier.carrier (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (6 :
    Fin 7) (2 : Fin 7) (1 : Fin 7)) (.conj (ConstructionDirectedLimitCarrier.projectionGraph (3 : Fin 7)
    (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (2 : Fin 7) (0 : Fin 7)) (.conj
    (ConstructionDirectedLimitCarrier.equalityLaw (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7) (0 :
    Fin 7)) (.conj (.forallE (.forallE (.imp (ConstructionDirectedSystem.atStage (5 : Fin 9) (7 : Fin 9)
    (1 : Fin 9) (0 : Fin 9)) (.existsE (.conj (.mem (.bound (0 : Fin 10)) (.bound (4 : Fin 10)))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (3 : Fin 10) (2 : Fin 10) (1 : Fin 10) (0 : Fin
    10)))))))) (.conj (.forallE (.imp (.mem (.bound (0 : Fin 8)) (.bound (2 : Fin 8))) (.existsE
    (.existsE (.conj (ConstructionDirectedSystem.atStage (6 : Fin 10) (8 : Fin 10) (1 : Fin 10) (0 : Fin
    10)) (ProjectSyntax.encode id (ForcingDiagramOrder.product (3 : Fin 10) (1 : Fin 10) (0 : Fin 10) (2
    : Fin 10)))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (10 : Fin 13) (5 : Fin 13) (4 : Fin 13))) (.imp
    (ConstructionDirectedSystem.transition (9 : Fin 13) (11 : Fin 13) (12 : Fin 13) (5 : Fin 13) (4 : Fin
    13) (3 : Fin 13) (2 : Fin 13)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product (6 : Fin
    13) (5 : Fin 13) (3 : Fin 13) (1 : Fin 13))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (6 : Fin 13) (4 : Fin 13) (2 : Fin 13) (0 : Fin 13)))
    (Project.Formula.extensionalEq (.bound (1 : Fin 13)) (.bound (0 : Fin 13))))))))))))) (.conj (.imp
    (ConstructionDirectedSystem.injectiveTransitions (3 : Fin 7) (4 : Fin 7) (5 : Fin 7) (6 : Fin 7))
    (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
    (4 : Fin 11) (3 : Fin 11) (2 : Fin 11) (0 : Fin 11))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (4 : Fin 11) (3 : Fin 11) (1 : Fin 11) (0 : Fin 11)))
    (Project.Formula.extensionalEq (.bound (2 : Fin 11)) (.bound (1 : Fin 11)))))))))) (.conj (.forallE
    (.forallE (.imp (.mem (.bound (1 : Fin 9)) (.bound (3 : Fin 9))) (.imp (.mem (.bound (0 : Fin 9))
    (.bound (3 : Fin 9))) (.existsE (.existsE (.existsE (.conj (ConstructionDirectedSystem.atStage (8 :
    Fin 12) (10 : Fin 12) (2 : Fin 12) (1 : Fin 12)) (.conj (ConstructionDirectedSystem.atStage (8 : Fin
    12) (10 : Fin 12) (2 : Fin 12) (0 : Fin 12)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (5 : Fin 12) (2 : Fin 12) (1 : Fin 12) (4 : Fin 12)))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (5 : Fin 12) (2 : Fin 12) (0 : Fin 12) (3 : Fin
    12))))))))))))) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin 10)) (.bound (4 :
    Fin 10))) (.imp (.mem (.bound (1 : Fin 10)) (.bound (4 : Fin 10))) (.imp (.mem (.bound (0 : Fin 10))
    (.bound (4 : Fin 10))) (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionDirectedSystem.atStage (10 : Fin 14) (12 : Fin 14) (3 : Fin 14) (2 : Fin 14)) (.conj
    (ConstructionDirectedSystem.atStage (10 : Fin 14) (12 : Fin 14) (3 : Fin 14) (1 : Fin 14)) (.conj
    (ConstructionDirectedSystem.atStage (10 : Fin 14) (12 : Fin 14) (3 : Fin 14) (0 : Fin 14)) (.conj
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (7 : Fin 14) (3 : Fin 14) (2 : Fin 14) (6 : Fin
    14))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product (7 : Fin 14) (3 : Fin 14) (1 : Fin
    14) (5 : Fin 14))) (ProjectSyntax.encode id (ForcingDiagramOrder.product (7 : Fin 14) (3 : Fin 14) (0
    : Fin 14) (4 : Fin 14)))))))))))))))))) (.forallE (.forallE (.imp (.mem (.bound (1 : Fin 9)) (.bound
    (5 : Fin 9))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin 9) (1 : Fin 9) (0 :
    Fin 9))) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 10) (1 : Fin
    10) (4 : Fin 10))) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
    (2 : Fin 12) (1 : Fin 12) (0 : Fin 12))) (.conj (.mem (.bound (1 : Fin 12)) (.bound (3 : Fin 12)))
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (5 : Fin 12) (4 : Fin 12) (1 : Fin 12) (0 : Fin
    12))))))) (.imp (ConstructionDirectedSystem.injectiveTransitions (6 : Fin 10) (7 : Fin 10) (8 : Fin
    10) (9 : Fin 10)) (ProjectSyntax.encode id (Source.SetLanguage.injection (0 : Fin 10) (1 : Fin 10) (4
    : Fin 10)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,
      ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,
      ConstructionDirectedSystem.atStage_freeClosed,ConstructionDirectedSystem.transition_freeClosed,
      ConstructionDirectedSystem.injectiveTransitions_freeClosed,
      ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,
      ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,ConstructionDirectedLimitCarrier.equalityLaw_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),
    ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,
    ConstructionDirectedSystem.atStage_semantics hM,ConstructionDirectedSystem.transition_semantics hM,
    ConstructionDirectedSystem.injectiveTransitions_semantics hM,
    ConstructionDirectedLimitCarrier.representatives_semantics hM,ConstructionDirectedLimitCarrier.carrier_semantics hM,
    ConstructionDirectedLimitCarrier.projectionGraph_semantics hM,ConstructionDirectedLimitCarrier.equalityLaw_semantics hM]
  intro hE hT
  exact ConstructionDirectedLimitCarrier.exists_system hM (bound 0) (bound 1) (bound 2) (bound 3) hE hT

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionDirectedLimitCarrierSyntax
