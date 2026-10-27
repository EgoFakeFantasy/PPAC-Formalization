/- Pinned MonoidRounds.Request.map and Round.step schedule evaluation.
Actual UNIQUE mapped function graph on arbitrary internal J and VARYING
stage domains/base maps, with exact values and valid target Request data. -/
import PPAC.Migration.ConstructionRequestSchedule

namespace PPAC.Migration.ConstructionRequestScheduleSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRequestSchedule
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def scheduleSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 12 (.imp (Project.Formula.isEmpty (.bound (4 : Fin 12))) (.imp
    (Project.Formula.isOrdinalOne (.bound (5 : Fin 12))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 12) (2 : Fin 12) (3 : Fin 12))) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 12) (2 : Fin 12)) (.imp
    (ConstructionDirectedMonoidData.family (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (9 : Fin 12)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.functionOn (10 : Fin 12) (6 : Fin 12))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.functionOn (11 : Fin 12) (6 : Fin 12))) (.imp
    (ConstructionRequestSchedule.requests (11 : Fin 12) (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4
    : Fin 12) (5 : Fin 12)) (.imp (ConstructionRequestSchedule.baseMaps (6 : Fin 12) (7 : Fin 12) (8 : Fin 12)
    (9 : Fin 12) (10 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12)) (.existsE (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.functionOn (0 : Fin (12+1)) (6 : Fin 12).succ)) (.conj
    (ConstructionRequestSchedule.graph (0 : Fin 12).succ (1 : Fin 12).succ (2 : Fin 12).succ (3 : Fin 12).succ
    (4 : Fin 12).succ (5 : Fin 12).succ (6 : Fin 12).succ (7 : Fin 12).succ (8 : Fin 12).succ (9 : Fin
    12).succ (10 : Fin 12).succ (11 : Fin 12).succ (0 : Fin (12+1))) (.conj (.forallE (.forallE (.forallE
    (.forallE (.forallE (.imp (.mem (.bound (4 : Fin (12+6))) (.bound (6 : Fin
    12).succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (7 : Fin
    12).succ.succ.succ.succ.succ.succ (4 : Fin (12+6)) (3 : Fin (12+6)))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (8 : Fin 12).succ.succ.succ.succ.succ.succ (4 : Fin (12+6)) (2 : Fin (12+6))))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (9 : Fin 12).succ.succ.succ.succ.succ.succ (4 :
    Fin (12+6)) (1 : Fin (12+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
    (12+1)).succ.succ.succ.succ.succ (4 : Fin (12+6)) (0 : Fin (12+6)))) (ConstructionRequestSchedule.request
    (0 : Fin 12).succ.succ.succ.succ.succ.succ (3 : Fin (12+6)) (2 : Fin (12+6)) (1 : Fin (12+6)) (4 : Fin
    12).succ.succ.succ.succ.succ.succ (5 : Fin 12).succ.succ.succ.succ.succ.succ (0 : Fin (12+6)))))))))))))
    (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn (0 : Fin (12+2)) (6 : Fin
    12).succ.succ)) (.imp (ConstructionRequestSchedule.graph (0 : Fin 12).succ.succ (1 : Fin 12).succ.succ (2
    : Fin 12).succ.succ (3 : Fin 12).succ.succ (4 : Fin 12).succ.succ (5 : Fin 12).succ.succ (6 : Fin
    12).succ.succ (7 : Fin 12).succ.succ (8 : Fin 12).succ.succ (9 : Fin 12).succ.succ (10 : Fin 12).succ.succ
    (11 : Fin 12).succ.succ (0 : Fin (12+2))) (Project.Formula.extensionalEq (.bound (0 : Fin (12+2))) (.bound
    (0 : Fin (12+1)).succ)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isEmpty,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionDirectedMonoidData.family_freeClosed,
      ConstructionRequestSchedule.requests_freeClosed,ConstructionRequestSchedule.baseMaps_freeClosed,
      ConstructionRequestSchedule.graph_freeClosed,ConstructionRequestSchedule.request_freeClosed]

theorem schedule_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence scheduleSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) scheduleSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionDirectedMonoidData.family_semantics hM,ConstructionRequestSchedule.requests_semantics hM,
    ConstructionRequestSchedule.baseMaps_semantics hM,ConstructionRequestSchedule.graph_semantics hM,
    ConstructionRequestSchedule.request_semantics hM]
  exact fun hz hone hm hJoins hFam hOrigins hSchedule hReq hBase =>
    exists_schedule hM hz hone hm hJoins hFam hOrigins hSchedule hReq hBase

theorem schedule_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence scheduleSentence) := ModelTransfer.derives (fun _ hM => schedule_models hM)

end PPAC.Migration.ConstructionRequestScheduleSyntax
