/- Full object sentence for the ACTUAL canonical ordinal schedule.
All previous exhaustive schedule/order fields retained; native ordinal
collapse/inverse/composition construct actual transported graphs and places. -/
import PPAC.Migration.ConstructionOrdinalSchedule

namespace PPAC.Migration.ConstructionOrdinalScheduleSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionOrdinalSchedule
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def data {m : Nat} (Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionScheduleOrderSyntax.orderedData Requests K A I top base Schedule Place r R ordinal)
  (.conj (Project.Formula.isWellOrderCollapseFunction PureKuratowskiProject.convention (.bound collapse)
  (.bound R) (.bound I) (.bound I)) (.conj (Project.Formula.isBijectionFromTo
  PureKuratowskiProject.convention (.bound collapse) (.bound I) (.bound ordinal)) (.conj
  (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound inverse) (.bound ordinal)
  (.bound I)) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
  inverse.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (ProjectSyntax.encode id (Source.SetLanguage.edge
  collapse.succ.succ (0 : Fin (m+2)) (1 : Fin (m+2))))))) (.conj (.forallE (.forallE (.forallE (.forallE
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge collapse.succ.succ.succ.succ (3 : Fin (m+4)) (1 :
  Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge collapse.succ.succ.succ.succ (2 : Fin
  (m+4)) (0 : Fin (m+4)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ.succ (3
  : Fin (m+4)) (2 : Fin (m+4)))) (.mem (.bound (1 : Fin (m+4))) (.bound (0 : Fin (m+4))))))))))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo ordSchedule ordinal Requests)) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap inverse Schedule ordSchedule) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.injection ordPlace A ordinal)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap Place
  collapse ordPlace) (.conj (.mem (.bound last) (.bound ordinal)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge collapse top last)) (.conj (Project.Formula.isOrdinal (.bound last)) (.conj
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound ordinal.succ)) (.disj (.mem (.bound (0 : Fin
  (m+1))) (.bound last.succ)) (Project.Formula.extensionalEq (.bound (0 : Fin (m+1))) (.bound last.succ)))))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge ordSchedule last base)) (.conj (.forallE
  (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound Requests.succ.succ)) (.imp (.mem (.bound (0 : Fin
  (m+2))) (.bound K.succ.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+3))) (.bound
  last.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product ordPlace.succ.succ.succ
  (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge
  ordSchedule.succ.succ.succ (0 : Fin (m+3)) (2 : Fin (m+3))))))))))) (.conj (.forallE (.forallE (.forallE
  (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product ordPlace.succ.succ.succ.succ (3 :
  Fin (m+4)) (2 : Fin (m+4)) (0 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  ordPlace.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)) (0 : Fin (m+4))))
  (Project.Formula.extensionalEq (.bound (2 : Fin (m+4))) (.bound (1 : Fin (m+4)))))))))) (.conj (.forallE
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge collapse.succ.succ.succ (2 :
  Fin (m+3)) (1 : Fin (m+3)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
  ordSchedule.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id
  (Source.SetLanguage.edge Schedule.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))))))) (.forallE
  (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  Place.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge collapse.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin (m+4))))
  (ProjectSyntax.encode id (ForcingDiagramOrder.product ordPlace.succ.succ.succ.succ (3 : Fin (m+4)) (2 :
  Fin (m+4)) (0 : Fin (m+4))))))))))))))))))))))))))))

theorem data_freeClosed {m : Nat} (Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last : Fin m) :
    (data Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionScheduleOrderSyntax.orderedData_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,Project.Formula.extensionalEq]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last : Fin m) :
    Project.Formula.satisfies env (data Requests K A I top base Schedule Place r R ordinal collapse inverse ordSchedule ordPlace last) ↔ Data hM (env.bound Requests) (env.bound K) (env.bound A) (env.bound I) (env.bound top) (env.bound base) (env.bound Schedule) (env.bound Place) (env.bound r) (env.bound R) (env.bound ordinal) (env.bound collapse) (env.bound inverse) (env.bound ordSchedule) (env.bound ordPlace) (env.bound last) := by
  simp only [data,Data,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionScheduleOrderSyntax.orderedData_semantics hM,Project.Formula.satisfies_isWellOrderCollapseFunction_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl


def fullSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8 (.imp (ConstructionDirectedCardinality.choice ) (.imp (Project.Formula.isOmega (.bound (0 : Fin 8))) (.imp
    (Project.Formula.isEmpty (.bound (5 : Fin 8))) (.imp (.mem (.bound (5 : Fin 8)) (.bound (0 : Fin 8)))
    (.imp (Project.Formula.isOrdinalOne (.bound (6 : Fin 8))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 8) (2 : Fin 8) (3 : Fin 8))) (.imp (.mem (.bound (4 :
    Fin 8)) (.bound (1 : Fin 8))) (.imp (.neg (Project.Formula.extensionalEq (.bound (4 : Fin 8)) (.bound
    (3 : Fin 8)))) (.imp (.existsE (.mem (.bound (0 : Fin (8+1))) (.bound (7 : Fin 8).succ))) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRequestCarrier.carrier (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (15 : Fin (8+16)))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin (8+16)) (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj
    (ConstructionRequestCarrier.constantNode (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin (8+16)))
    (.conj (ConstructionProbePath.path (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin (8+16)))
    (.conj (ConstructionRequestSchedule.probeCode (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin (8+16))
    (13 : Fin (8+16))) (.conj (.mem (.bound (13 : Fin (8+16))) (.bound (15 : Fin (8+16)))) (.conj (.neg
    (Project.Formula.extensionalEq (.bound (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.bound (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) (.conj (data (15
    : Fin (8+16)) (7 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (12 : Fin (8+16))
    (11 : Fin (8+16)) (10 : Fin (8+16)) (13 : Fin (8+16)) (9 : Fin (8+16)) (8 : Fin (8+16)) (7 : Fin
    (8+16)) (6 : Fin (8+16)) (5 : Fin (8+16)) (4 : Fin (8+16)) (3 : Fin (8+16)) (2 : Fin (8+16)) (1 : Fin
    (8+16)) (0 : Fin (8+16))) (.conj (ConstructionRequestSchedule.requests (2 : Fin (8+16)) (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (.forallE
    (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (8+22))) (.bound (15 :
    Fin (8+16)).succ.succ.succ.succ.succ.succ)) (.imp (ConstructionRequestSchedule.transport (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (5 : Fin (8+22)) (4 : Fin (8+22)) (3 : Fin (8+22)) (2 : Fin (8+22)) (1 : Fin (8+22)) (0 : Fin (8+22)))
    (ConstructionRequestCarrier.element (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (5 : Fin (8+22)) (4 : Fin (8+22)) (3 : Fin (8+22)) (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    (0 : Fin (8+22))))))))))) (.forallE (.imp (ConstructionRequestCarrier.carrier (0 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
    8).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin
    (8+17))) (Project.Formula.extensionalEq (.bound (0 : Fin (8+17))) (.bound (15 : Fin
    (8+16)).succ)))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedCardinality.choice_freeClosed,Project.Formula.extensionalEq,
      ConstructionRequestCarrier.carrier_freeClosed,ConstructionRequestCarrier.constantNode_freeClosed,
      ConstructionProbePath.path_freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,data_freeClosed,
      ConstructionRequestSchedule.requests_freeClosed,ConstructionRequestSchedule.transport_freeClosed,
      ConstructionRequestCarrier.element_freeClosed]

theorem full_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence fullSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) fullSentence]
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
    ConstructionDirectedCardinality.choice_semantics hM,
    ConstructionRequestCarrier.carrier_semantics hM,ConstructionRequestCarrier.constantNode_semantics hM,
    ConstructionProbePath.path_semantics hM,ConstructionRequestSchedule.probeCode_semantics hM,data_semantics hM,
    ConstructionRequestSchedule.requests_semantics hM,ConstructionRequestSchedule.transport_semantics hM,
    ConstructionRequestCarrier.element_semantics hM]
  exact fun hc hw hz hzw hone hm hmark hne hK => exists_all hM hc hw hz hzw hone hm hmark hne hK

theorem full_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence fullSentence) := ModelTransfer.derives (fun _ hM => full_models hM)

end PPAC.Migration.ConstructionOrdinalScheduleSyntax
