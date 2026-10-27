/- Pinned MergerWords.Word.act/product: actual full internal carrier and
both operation graphs are CONSTRUCTED from the original valid prescription.
Pure nativeZF original-kernel certificate retains exact old/snoc equations,
right-action unit/composition and injectivity in the old factor.
Word product associativity/cancellation/joins/weights are separate obligations. -/
import PPAC.Migration.ConstructionMergerWordProduct

namespace PPAC.Migration.ConstructionMergerWordProductSyntax
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
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 7))) (.imp (Project.Formula.isEmpty (.bound (6 : Fin
    7))) (.imp (.mem (.bound (6 : Fin 7)) (.bound (0 : Fin 7))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 7) (3 : Fin 7) (4 : Fin 7))) (.imp
    (ConstructionMergerRelations.prescription (1 : Fin 7) (2 : Fin 7) (5 : Fin 7)) (.imp
    (ConstructionMergerRelations.valid (1 : Fin 7) (2 : Fin 7) (3 : Fin 7) (5 : Fin 7)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeLetters.representatives (11 : Fin 17) (12 : Fin 17) (9 : Fin 17)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 17) (9 : Fin 17) (8 : Fin 17))) (.conj
    (ConstructionMergerCopies.copies (11 : Fin 17) (12 : Fin 17) (13 : Fin 17) (15 : Fin 17) (9 : Fin 17) (8
    : Fin 17)) (.conj (ConstructionMergerCopies.projectionGraph (11 : Fin 17) (12 : Fin 17) (13 : Fin 17)
    (15 : Fin 17) (9 : Fin 17) (7 : Fin 17)) (.conj (ConstructionMergerCopies.equalityLaw (11 : Fin 17) (12
    : Fin 17) (13 : Fin 17) (15 : Fin 17) (7 : Fin 17)) (.conj (ConstructionProbeLetters.representatives (8
    : Fin 17) (12 : Fin 17) (6 : Fin 17)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 :
    Fin 17) (6 : Fin 17) (8 : Fin 17))) (.conj (ConstructionMergerAction.actionTable (12 : Fin 17) (13 : Fin
    17) (7 : Fin 17) (5 : Fin 17)) (.conj (ConstructionMergerAction.rightFreeAction (13 : Fin 17) (14 : Fin
    17) (8 : Fin 17) (5 : Fin 17)) (.conj (ConstructionMergerAction.copyLaw (12 : Fin 17) (13 : Fin 17) (7 :
    Fin 17) (5 : Fin 17)) (.conj (ConstructionProbeRaw.carrier (10 : Fin 17) (12 : Fin 17) (8 : Fin 17) (4 :
    Fin 17)) (.conj (ConstructionProbeLetters.representatives (4 : Fin 17) (12 : Fin 17) (3 : Fin 17))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 17) (3 : Fin 17) (4 : Fin 17)))
    (.conj (ConstructionMergerWordAction.actionTable (10 : Fin 17) (12 : Fin 17) (8 : Fin 17) (16 : Fin 17)
    (13 : Fin 17) (5 : Fin 17) (2 : Fin 17)) (.conj (ConstructionMergerAction.rightFreeAction (13 : Fin 17)
    (14 : Fin 17) (4 : Fin 17) (2 : Fin 17)) (.conj (ConstructionProbeLetters.representatives (4 : Fin 17)
    (4 : Fin 17) (1 : Fin 17)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 17) (1 :
    Fin 17) (4 : Fin 17))) (ConstructionMergerWordProduct.laws (10 : Fin 17) (12 : Fin 17) (8 : Fin 17) (16
    : Fin 17) (2 : Fin 17) (0 : Fin 17)))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionMergerCopies.copies_freeClosed,
      ConstructionMergerCopies.projectionGraph_freeClosed,ConstructionMergerCopies.equalityLaw_freeClosed,
      ConstructionMergerAction.actionTable_freeClosed,ConstructionMergerAction.rightFreeAction_freeClosed,
      ConstructionMergerAction.copyLaw_freeClosed,ConstructionProbeRaw.carrier_freeClosed,
      ConstructionMergerWordAction.actionTable_freeClosed,ConstructionMergerWordProduct.laws_freeClosed]

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
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeLetters.representatives_semantics hM,
    ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,ConstructionMergerAction.actionTable_semantics hM,
    ConstructionMergerAction.rightFreeAction_semantics hM,ConstructionMergerAction.copyLaw_semantics hM,
    ConstructionProbeRaw.carrier_semantics hM,ConstructionMergerWordAction.actionTable_semantics hM,ConstructionMergerWordProduct.laws_semantics hM]
  exact ConstructionMergerWordProduct.exists_system hM


theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerWordProductSyntax
