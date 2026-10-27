/- Pinned DirectLimits.ConservativeLimit.of as actual MonoidHom,
LeftCancelMonoid:32 and IsConical:44. Pure forall6/exist6 native-ZF certificate:
SAME actual carrier/projection, actual multiplication/unit, ALL algebra laws,
conditional Conical and EVERY stage map as actual product/unit preserving graph.
No transition-injectivity premise; original nonempty directed index/stage monoids
and transition map_mul/map_one remain explicit inputs. Conservative/weights,
actual final weighted tower and final internal Con remain open. -/
import PPAC.Migration.ConstructionDirectedMonoid
import PPAC.Migration.ConstructionProbeLiftHomSyntax

namespace PPAC.Migration.ConstructionDirectedMonoidSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6
    (.imp (.existsE (.mem (.bound (0 : Fin 7)) (.bound (1 : Fin 7)))) (.imp
    (ConstructionDirectedSystem.indexLaws (0 : Fin 6) (1 : Fin 6)) (.imp
    (ConstructionDirectedSystem.transitionLaws (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6)) (.imp
    (ConstructionDirectedMonoidData.family (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)) (.imp
    (ConstructionDirectedMonoidData.homLaws (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6)
    (5 : Fin 6)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionDirectedLimitCarrier.representatives (6 : Fin 12) (8 : Fin 12) (5 : Fin 12)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 12) (5 : Fin 12) (4 : Fin 12))) (.conj
    (ConstructionDirectedLimitCarrier.carrier (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (9 : Fin 12) (5 :
    Fin 12) (4 : Fin 12)) (.conj (ConstructionDirectedLimitCarrier.projectionGraph (6 : Fin 12) (7 : Fin
    12) (8 : Fin 12) (9 : Fin 12) (5 : Fin 12) (3 : Fin 12)) (.conj
    (ConstructionDirectedLimitCarrier.equalityLaw (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (9 : Fin 12) (3
    : Fin 12)) (.conj (ConstructionProbeLetters.representatives (4 : Fin 12) (4 : Fin 12) (2 : Fin 12))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 12) (2 : Fin 12) (4 : Fin 12)))
    (.conj (ConstructionDirectedProduct.graph (6 : Fin 12) (8 : Fin 12) (10 : Fin 12) (3 : Fin 12) (1 :
    Fin 12)) (.conj (.mem (.bound (0 : Fin 12)) (.bound (4 : Fin 12))) (.conj
    (ConstructionDirectedMonoid.unitImage (6 : Fin 12) (8 : Fin 12) (11 : Fin 12) (3 : Fin 12) (0 : Fin
    12)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 12) (1 : Fin 12)
    (0 : Fin 12))) (.conj (.imp (ConstructionDirectedMonoidData.conicalFamily (6 : Fin 12) (8 : Fin 12)
    (10 : Fin 12) (11 : Fin 12)) (ProjectSyntax.encode id (ForcingDiagramPoset.conical (4 : Fin 12) (1 :
    Fin 12) (0 : Fin 12)))) (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin 16))
    (.bound (10 : Fin 16))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 16) (3 :
    Fin 16) (2 : Fin 16))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (14 : Fin 16) (3 : Fin
    16) (1 : Fin 16))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (15 : Fin 16) (3 : Fin 16)
    (0 : Fin 16))) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 17) (3 :
    Fin 17) (9 : Fin 17))) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge (2 : Fin 19) (1 : Fin 19) (0 : Fin 19))) (.conj (.mem (.bound (1 : Fin 19))
    (.bound (5 : Fin 19))) (ProjectSyntax.encode id (ForcingDiagramOrder.product (10 : Fin 19) (6 : Fin
    19) (1 : Fin 19) (0 : Fin 19))))))) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (2 : Fin
    17) (6 : Fin 17) (0 : Fin 17)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin 17)
    (1 : Fin 17) (5 : Fin 17))) (.imp (ConstructionDirectedSystem.injectiveTransitions (11 : Fin 17) (12
    : Fin 17) (13 : Fin 17) (14 : Fin 17)) (ProjectSyntax.encode id (Source.SetLanguage.injection (0 :
    Fin 17) (3 : Fin 17) (9 : Fin 17))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,
      ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedMonoidData.homLaws_freeClosed,
      ConstructionDirectedMonoidData.conicalFamily_freeClosed,ConstructionDirectedSystem.injectiveTransitions_freeClosed,
      ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,
      ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,ConstructionDirectedLimitCarrier.equalityLaw_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionDirectedProduct.graph_freeClosed,
      ConstructionDirectedMonoid.unitImage_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed]

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
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,
    ConstructionDirectedMonoidData.family_semantics hM,ConstructionDirectedMonoidData.homLaws_semantics hM,
    ConstructionDirectedMonoidData.conicalFamily_semantics hM,ConstructionDirectedSystem.injectiveTransitions_semantics hM,
    ConstructionDirectedLimitCarrier.representatives_semantics hM,ConstructionDirectedLimitCarrier.carrier_semantics hM,
    ConstructionDirectedLimitCarrier.projectionGraph_semantics hM,ConstructionDirectedLimitCarrier.equalityLaw_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ConstructionDirectedProduct.graph_semantics hM,
    ConstructionDirectedMonoid.unitImage_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM]
  intro hne hE hT hFam hHom
  exact ConstructionDirectedMonoid.exists_system hM (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) hne hE hT hFam hHom

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionDirectedMonoidSyntax
