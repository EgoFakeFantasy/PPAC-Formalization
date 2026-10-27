/- Original-kernel certificate for ALL INTERNAL Merger Word conditional joins.
Retains SAME prescribed copies, actual Word carrier/actions/product and monoid.
Original old monoid/joins/valid prescription remain parent inputs.
Weights, full MergerData and final Con remain unclaimed. -/
import PPAC.Migration.ConstructionMergerWordCones

namespace PPAC.Migration.ConstructionMergerWordConesSyntax
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
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (2 : Fin 7) (3 : Fin 7)) (.imp (Project.Formula.isOmega (.bound (0 : Fin 7))) (.imp (Project.Formula.isEmpty (.bound (6 : Fin
    7))) (.imp (.mem (.bound (6 : Fin 7)) (.bound (0 : Fin 7))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 7) (3 : Fin 7) (4 : Fin 7))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.conical (2 : Fin 7) (3 : Fin 7) (4 : Fin 7))) (.imp
    (ConstructionMergerRelations.prescription (1 : Fin 7) (2 : Fin 7) (5 : Fin 7)) (.imp
    (ConstructionMergerRelations.valid (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.conj
    (ConstructionProbeLetters.representatives (12 : Fin 18) (13 : Fin 18) (10 : Fin 18)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 18) (10 : Fin 18) (9 : Fin 18))) (.conj
    (ConstructionMergerCopies.copies (12 : Fin 18) (13 : Fin 18) (14 : Fin 18) (16 : Fin 18) (10 : Fin 18)
    (9 : Fin 18)) (.conj (ConstructionMergerCopies.projectionGraph (12 : Fin 18) (13 : Fin 18) (14 : Fin 18)
    (16 : Fin 18) (10 : Fin 18) (8 : Fin 18)) (.conj (ConstructionMergerCopies.equalityLaw (12 : Fin 18) (13
    : Fin 18) (14 : Fin 18) (16 : Fin 18) (8 : Fin 18)) (.conj (ConstructionProbeLetters.representatives (9
    : Fin 18) (13 : Fin 18) (7 : Fin 18)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 :
    Fin 18) (7 : Fin 18) (9 : Fin 18))) (.conj (ConstructionMergerAction.actionTable (13 : Fin 18) (14 : Fin
    18) (8 : Fin 18) (6 : Fin 18)) (.conj (ConstructionMergerAction.rightFreeAction (14 : Fin 18) (15 : Fin
    18) (9 : Fin 18) (6 : Fin 18)) (.conj (ConstructionMergerAction.copyLaw (13 : Fin 18) (14 : Fin 18) (8 :
    Fin 18) (6 : Fin 18)) (.conj (ConstructionProbeRaw.carrier (11 : Fin 18) (13 : Fin 18) (9 : Fin 18) (5 :
    Fin 18)) (.conj (ConstructionProbeLetters.representatives (5 : Fin 18) (13 : Fin 18) (4 : Fin 18))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (3 : Fin 18) (4 : Fin 18) (5 : Fin 18)))
    (.conj (ConstructionMergerWordAction.actionTable (11 : Fin 18) (13 : Fin 18) (9 : Fin 18) (17 : Fin 18)
    (14 : Fin 18) (6 : Fin 18) (3 : Fin 18)) (.conj (ConstructionMergerAction.rightFreeAction (14 : Fin 18)
    (15 : Fin 18) (5 : Fin 18) (3 : Fin 18)) (.conj (ConstructionProbeLetters.representatives (5 : Fin 18)
    (5 : Fin 18) (2 : Fin 18)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 18) (2 :
    Fin 18) (5 : Fin 18))) (ConstructionMergerWordProduct.laws (11 : Fin 18) (13 : Fin 18) (9 : Fin 18) (17
    : Fin 18) (3 : Fin 18) (1 : Fin 18))))))))))))))))))) (.conj (ConstructionProbeRaw.old (17 : Fin 18) (13
    : Fin 18) (15 : Fin 18) (0 : Fin 18)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (5 : Fin 18) (1 : Fin 18) (0 : Fin 18))) (.conj (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical (5 : Fin 18) (1 : Fin 18) (0 : Fin 18))) (.conj (ConstructionMergerCopyCones.hasConeJoins (13 : Fin 18) (9 : Fin 18) (6 : Fin 18)) (ConstructionProbeSharedIntersections.conditionalJoins (5 : Fin 18) (1 : Fin 18))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionMergerCopies.copies_freeClosed,
      ConstructionMergerCopies.projectionGraph_freeClosed,ConstructionMergerCopies.equalityLaw_freeClosed,
      ConstructionMergerAction.actionTable_freeClosed,ConstructionMergerAction.rightFreeAction_freeClosed,
      ConstructionMergerAction.copyLaw_freeClosed,ConstructionProbeRaw.carrier_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,ConstructionMergerWordProduct.laws_freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionMergerCopyCones.hasConeJoins_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeRaw.old_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeLetters.representatives_semantics hM,
    ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,ConstructionMergerAction.actionTable_semantics hM,
    ConstructionMergerAction.rightFreeAction_semantics hM,ConstructionMergerAction.copyLaw_semantics hM,
    ConstructionProbeRaw.carrier_semantics hM,ConstructionMergerWordAction.actionTable_semantics hM,ConstructionMergerWordProduct.laws_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionMergerCopyCones.hasConeJoins_semantics hM]
  intro hJoins hw hz hzw hm hc hP hValid
  exact ConstructionMergerWordCones.exists_system hM hw hz hzw hm hc hJoins hP hValid



theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerWordConesSyntax
