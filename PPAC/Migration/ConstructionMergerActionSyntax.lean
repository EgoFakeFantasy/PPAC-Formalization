/- Pure nativeZF original-kernel certificate for actual prescribed Copies and
its right free action. The source relation itself is valid; no transitive closure,
supplied quotient or supplied action. Index n is an arbitrary internal set,
so in particular covers every internal/nonstandard finite source index set. -/
import PPAC.Migration.ConstructionMergerAction

namespace PPAC.Migration.ConstructionMergerActionSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 5
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 5) (2 : Fin 5) (3 : Fin
    5))) (.imp (ConstructionMergerRelations.prescription (0 : Fin 5) (1 : Fin 5) (4 : Fin 5)) (.imp
    (ConstructionMergerRelations.valid (0 : Fin 5) (1 : Fin 5) (2 : Fin 5) (4 : Fin 5)) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.conj (ConstructionProbeLetters.representatives (5 : Fin 10) (6 : Fin 10)
    (4 : Fin 10)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin 10) (4 : Fin 10) (3 :
    Fin 10))) (.conj (ConstructionMergerCopies.copies (5 : Fin 10) (6 : Fin 10) (7 : Fin 10) (9 : Fin 10) (4
    : Fin 10) (3 : Fin 10)) (.conj (ConstructionMergerCopies.projectionGraph (5 : Fin 10) (6 : Fin 10) (7 :
    Fin 10) (9 : Fin 10) (4 : Fin 10) (2 : Fin 10)) (.conj (ConstructionMergerCopies.equalityLaw (5 : Fin
    10) (6 : Fin 10) (7 : Fin 10) (9 : Fin 10) (2 : Fin 10)) (.conj
    (ConstructionProbeLetters.representatives (3 : Fin 10) (6 : Fin 10) (1 : Fin 10)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 10) (1 : Fin 10) (3 : Fin 10))) (.conj
    (ConstructionMergerAction.actionTable (6 : Fin 10) (7 : Fin 10) (2 : Fin 10) (0 : Fin 10)) (.conj
    (ConstructionMergerAction.rightFreeAction (7 : Fin 10) (8 : Fin 10) (3 : Fin 10) (0 : Fin 10))
    (ConstructionMergerAction.copyLaw (6 : Fin 10) (7 : Fin 10) (2 : Fin 10) (0 : Fin 10)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionMergerCopies.copies_freeClosed,
      ConstructionMergerCopies.projectionGraph_freeClosed,ConstructionMergerCopies.equalityLaw_freeClosed,
      ConstructionMergerAction.actionTable_freeClosed,ConstructionMergerAction.rightFreeAction_freeClosed,
      ConstructionMergerAction.copyLaw_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeLetters.representatives_semantics hM,
    ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,
    ConstructionMergerCopies.copies_semantics hM,ConstructionMergerCopies.projectionGraph_semantics hM,
    ConstructionMergerCopies.equalityLaw_semantics hM,ConstructionMergerAction.actionTable_semantics hM,
    ConstructionMergerAction.rightFreeAction_semantics hM,ConstructionMergerAction.copyLaw_semantics hM]
  exact ConstructionMergerAction.exists_system hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerActionSyntax
