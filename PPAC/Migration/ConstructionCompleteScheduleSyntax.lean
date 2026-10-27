/- Pinned MonoidRounds.Request.defaultProbe / CompleteRounds.Index/
schedule/place. Full internal Request carrier and ACTUAL exhaustive schedule/
placement graphs, arbitrary K. Ordering/ordinalization and cardinal bounds
are explicitly NOT asserted by this data-construction endpoint. -/
import PPAC.Migration.ConstructionCompleteSchedule

namespace PPAC.Migration.ConstructionCompleteScheduleSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCompleteSchedule
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def data {m : Nat} (Requests K A I top base Schedule Place : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbeLetters.representatives Requests K A) (.conj (ProjectSyntax.encode id
  (ForcingWithTopCarrier.carrier A I)) (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
  (.conj (.mem (.bound top) (.bound I)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo Schedule
  I Requests)) (.conj (ConstructionCompleteSchedule.graph I A base Schedule) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.injection Place A I)) (.conj (ConstructionCompleteSchedule.places A Place) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule top base)) (.conj (.forallE (.forallE (.imp
  (.mem (.bound (1 : Fin (m+2))) (.bound Requests.succ.succ)) (.imp (.mem (.bound (0 : Fin (m+2))) (.bound
  K.succ.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+3))) (.bound I.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product Place.succ.succ.succ (1 : Fin (m+2)).succ (0 : Fin
  (m+2)).succ (0 : Fin (m+3)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Schedule.succ.succ.succ (0 : Fin (m+3)) (1 : Fin (m+2)).succ)) (.neg (Project.Formula.extensionalEq
  (.bound (0 : Fin (m+3))) (.bound top.succ.succ.succ))))))))))) (.conj (.forallE (.imp (.mem (.bound (0 :
  Fin (m+1))) (.bound Requests.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+2))) (.bound I.succ.succ))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule.succ.succ (0 : Fin (m+2)) (0 : Fin
  (m+1)).succ)) (.neg (Project.Formula.extensionalEq (.bound (0 : Fin (m+2))) (.bound top.succ.succ))))))))
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  Place.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (0 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product Place.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)) (0 : Fin (m+4))))
  (Project.Formula.extensionalEq (.bound (2 : Fin (m+4))) (.bound (1 : Fin (m+4)))))))))) (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+1)) I.succ Requests.succ)) (.imp
  (ConstructionCompleteSchedule.graph I.succ A.succ base.succ (0 : Fin (m+1)))
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+1))) (.bound Schedule.succ)))))))))))))))))

theorem data_freeClosed {m : Nat} (Requests K A I top base Schedule Place : Fin m) :
    (data Requests K A I top base Schedule Place).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionCompleteSchedule.graph_freeClosed,ConstructionCompleteSchedule.places_freeClosed,Project.Formula.extensionalEq]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Requests K A I top base Schedule Place : Fin m) :
    Project.Formula.satisfies env (data Requests K A I top base Schedule Place) ↔ Data (env.bound Requests) (env.bound K) (env.bound A) (env.bound I) (env.bound top) (env.bound base) (env.bound Schedule) (env.bound Place) := by
  simp only [data,Data,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeLetters.representatives_semantics hM,ForcingWithTopCarrier.carrier_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionCompleteSchedule.graph_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionCompleteSchedule.places_semantics hM,ForcingDiagramOrder.product_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 8 (.imp (Project.Formula.isOmega (.bound (0 : Fin 8))) (.imp
    (Project.Formula.isEmpty (.bound (5 : Fin 8))) (.imp (.mem (.bound (5 : Fin 8)) (.bound (0 : Fin 8)))
    (.imp (Project.Formula.isOrdinalOne (.bound (6 : Fin 8))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 8) (2 : Fin 8) (3 : Fin 8))) (.imp (.mem (.bound (4 : Fin
    8)) (.bound (1 : Fin 8))) (.imp (.neg (Project.Formula.extensionalEq (.bound (4 : Fin 8)) (.bound (3 : Fin
    8)))) (.imp (.existsE (.mem (.bound (0 : Fin 9)) (.bound (7 : Fin 8).succ))) (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRequestCarrier.carrier (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
    (8+8))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin (8+8)) (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ)) (.conj
    (ConstructionRequestCarrier.constantNode (0 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (8+8))) (.conj (ConstructionProbePath.path (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    (8+8))) (.conj (ConstructionRequestSchedule.probeCode (5 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ
    (3 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (6
    : Fin (8+8)) (5 : Fin (8+8))) (.conj (.mem (.bound (5 : Fin (8+8))) (.bound (7 : Fin (8+8)))) (.conj (.neg
    (Project.Formula.extensionalEq (.bound (5 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ) (.bound (6 :
    Fin 8).succ.succ.succ.succ.succ.succ.succ.succ))) (.conj (data (7 : Fin (8+8)) (7 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (8+8)) (3 : Fin (8+8)) (2 : Fin (8+8)) (5 : Fin (8+8))
    (1 : Fin (8+8)) (0 : Fin (8+8))) (.conj (ConstructionRequestSchedule.requests (1 : Fin (8+8)) (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ) (.conj
    (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (8+14))) (.bound
    (7 : Fin (8+8)).succ.succ.succ.succ.succ.succ)) (.imp (ConstructionRequestSchedule.transport (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (8+14)) (4 : Fin (8+14))
    (3 : Fin (8+14)) (2 : Fin (8+14)) (1 : Fin (8+14)) (0 : Fin (8+14))) (ConstructionRequestCarrier.element
    (0 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (8+14)) (4 :
    Fin (8+14)) (3 : Fin (8+14)) (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (8+14)))))))))))
    (.forallE (.imp (ConstructionRequestCarrier.carrier (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ.succ
    (2 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ.succ
    (6 : Fin 8).succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (8+9))) (Project.Formula.extensionalEq
    (.bound (0 : Fin (8+9))) (.bound (7 : Fin (8+8)).succ)))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionRequestCarrier.carrier_freeClosed,ConstructionRequestCarrier.constantNode_freeClosed,
      ConstructionProbePath.path_freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,
      data_freeClosed,ConstructionRequestSchedule.requests_freeClosed,
      ConstructionRequestSchedule.transport_freeClosed,ConstructionRequestCarrier.element_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinalOne_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionRequestCarrier.carrier_semantics hM,ConstructionRequestCarrier.constantNode_semantics hM,
    ConstructionProbePath.path_semantics hM,ConstructionRequestSchedule.probeCode_semantics hM,
    data_semantics hM,ConstructionRequestSchedule.requests_semantics hM,
    ConstructionRequestSchedule.transport_semantics hM,ConstructionRequestCarrier.element_semantics hM]
  exact fun hw hz hzw hone hm hmark hne hK => exists_all hM hw hz hzw hone hm hmark hne hK

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionCompleteScheduleSyntax
