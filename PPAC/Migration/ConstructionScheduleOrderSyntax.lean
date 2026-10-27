/- Actual chosen INTERNAL wellorder/WithTop order/ordinal type of the pinned
CompleteRound exhaustive schedule. Explicit source Choice is an antecedent
inside nativeZF; it is NOT added to the final background theory. -/
import PPAC.Migration.ConstructionScheduleOrder

namespace PPAC.Migration.ConstructionScheduleOrderSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionScheduleOrder
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def orderedData {m : Nat} (Requests K A I top base Schedule Place r R ordinal : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionCompleteScheduleSyntax.data Requests K A I top base Schedule Place) (.conj
  (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound r) (.bound A)) (.conj
  (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound R) (.bound I)) (.conj
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ (1 : Fin (m+2)) (0
  : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound I.succ.succ)) (.conj (.mem (.bound (0 : Fin
  (m+2))) (.bound I.succ.succ)) (ConstructionScheduleOrder.lt r.succ.succ (1 : Fin (m+2)) (0 : Fin
  (m+2)))))))) (.conj (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound I.succ)) (.imp (.neg
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+1))) (.bound top.succ))) (ProjectSyntax.encode id
  (Source.SetLanguage.edge R.succ (0 : Fin (m+1)) top.succ))))) (.conj (.forallE (.neg (ProjectSyntax.encode
  id (Source.SetLanguage.edge R.succ top.succ (0 : Fin (m+1)))))) (.conj (.forallE (.forallE (.imp (.mem
  (.bound (1 : Fin (m+2))) (.bound Requests.succ.succ)) (.imp (.mem (.bound (0 : Fin (m+2))) (.bound
  K.succ.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+3))) (.bound I.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product Place.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))
  (0 : Fin (m+3)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Schedule.succ.succ.succ (0 :
  Fin (m+3)) (2 : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ (0 : Fin
  (m+3)) top.succ.succ.succ)))))))))) (.conj (Project.Formula.isWellOrderType
  PureKuratowskiProject.convention (.bound R) (.bound I) (.bound ordinal)) (.conj (Project.Formula.isOrdinal
  (.bound ordinal)) (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound I) (.bound
  ordinal)))))))))))

theorem orderedData_freeClosed {m : Nat} (Requests K A I top base Schedule Place r R ordinal : Fin m) :
    (orderedData Requests K A I top base Schedule Place r R ordinal).FreeClosed := by
  simp -implicitDefEqProofs [orderedData,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionCompleteScheduleSyntax.data_freeClosed,ConstructionScheduleOrder.lt_freeClosed,Project.Formula.extensionalEq]

theorem orderedData_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Requests K A I top base Schedule Place r R ordinal : Fin m) :
    Project.Formula.satisfies env (orderedData Requests K A I top base Schedule Place r R ordinal) ↔ OrderedData hM (env.bound Requests) (env.bound K) (env.bound A) (env.bound I) (env.bound top) (env.bound base) (env.bound Schedule) (env.bound Place) (env.bound r) (env.bound R) (env.bound ordinal) := by
  simp only [orderedData,OrderedData,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionCompleteScheduleSyntax.data_semantics hM,ConstructionScheduleOrder.lt_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_isWellOrderType_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl


def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3 (.imp (ConstructionDirectedCardinality.choice ) (.imp (.mem (.bound (2 : Fin 3)) (.bound (0 : Fin 3)))
    (.imp (.existsE (.mem (.bound (0 : Fin (3+1))) (.bound (1 : Fin 3).succ))) (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (orderedData (0 : Fin
    3).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin 3).succ.succ.succ.succ.succ.succ.succ.succ (7 :
    Fin (3+8)) (6 : Fin (3+8)) (5 : Fin (3+8)) (2 : Fin 3).succ.succ.succ.succ.succ.succ.succ.succ (4 :
    Fin (3+8)) (3 : Fin (3+8)) (2 : Fin (3+8)) (1 : Fin (3+8)) (0 : Fin (3+8))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionDirectedCardinality.choice_freeClosed,orderedData_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionDirectedCardinality.choice_semantics hM,orderedData_semantics hM]
  exact fun hc hb hK => exists_system hM hc hb hK

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionScheduleOrderSyntax
