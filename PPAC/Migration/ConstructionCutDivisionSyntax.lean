/- Pure-set certificates for general positive division and the actual /4
operation required by the pinned ProbeMargins interval expression. -/
import PPAC.Migration.ConstructionCutDivision

namespace PPAC.Migration.ConstructionCutDivisionSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCutDivision
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def graph {m : Nat} (w Q n R F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound R.succ.succ)) (value w.succ.succ Q.succ.succ
  n.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (w Q n R F : Fin m) : (graph w Q n R F).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q n R F : Fin m) :
    Project.Formula.satisfies env (graph w Q n R F) ↔
      Graph hM (env.bound w) (env.bound Q) (env.bound n) (env.bound R) (env.bound F) := by
  simp only
  [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl

def laws {m : Nat} (F : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin
  (m+2)) (0 : Fin (m+2)))) (.iff (.existsE (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+3))))) (.existsE
  (.mem (.bound (0 : Fin (m+3))) (.bound (2 : Fin (m+3))))))))) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin
  (m+4)))) (.conj (.iff (Project.Formula.subset (.bound (1 : Fin (m+4))) (.bound (0 : Fin (m+4))))
  (Project.Formula.subset (.bound (3 : Fin (m+4))) (.bound (2 : Fin (m+4))))) (.iff (.conj
  (Project.Formula.subset (.bound (1 : Fin (m+4))) (.bound (0 : Fin (m+4)))) (.neg (Project.Formula.subset
  (.bound (0 : Fin (m+4))) (.bound (1 : Fin (m+4)))))) (.conj (Project.Formula.subset (.bound (3 : Fin (m+4)))
  (.bound (2 : Fin (m+4)))) (.neg (Project.Formula.subset (.bound (2 : Fin (m+4))) (.bound (3 : Fin
  (m+4)))))))))))))))

theorem laws_freeClosed {m : Nat} (F : Fin m) : (laws F).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (F : Fin m) :
    Project.Formula.satisfies env (laws F) ↔
      Laws (env.bound F) := by
  simp only
  [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 4))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 4)
    (1 : Fin 4)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 4) (1 : Fin 4) (2 : Fin 4)) (.imp (.mem
    (.bound (3 : Fin 4)) (.bound (0 : Fin 4))) (.imp (.existsE (.mem (.bound (0 : Fin 5)) (.bound (4 : Fin
    5)))) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 5) (3 : Fin 5) (3 :
    Fin 5))) (.conj (graph (1 : Fin 5) (2 : Fin 5) (4 : Fin 5) (3 : Fin 5) (0 : Fin 5)) (laws (0 : Fin
    5))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,graph_freeClosed,laws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    graph_semantics hM,laws_semantics hM]
  intro hw hQ hR hn hnp
  exact exists_graph hM hw hQ hn hnp hR

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

def quarterSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 3))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 3)
    (1 : Fin 3)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBaseWeights.digits (5 : Fin 8) (4 : Fin 8) (3
    : Fin 8) (2 : Fin 8)) (.conj (Project.Formula.isSuccessor (.bound (1 : Fin 8)) (.bound (2 : Fin 8)))
    (.conj (.mem (.bound (1 : Fin 8)) (.bound (5 : Fin 8))) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 8) (7 : Fin 8) (7 : Fin 8))) (.conj (graph (5 : Fin 8) (6 : Fin 8) (1
    : Fin 8) (7 : Fin 8) (0 : Fin 8)) (laws (0 : Fin 8)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionBaseWeights.digits_freeClosed,graph_freeClosed,laws_freeClosed]

theorem quarter_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence quarterSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) quarterSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionBaseWeights.digits_semantics,
    Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    graph_semantics hM,laws_semantics hM]
  intro hw hQ hR
  exact exists_quarter hM hw hQ hR

theorem quarter_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence quarterSentence) := ModelTransfer.derives (fun _ hM => quarter_models hM)

end PPAC.Migration.ConstructionCutDivisionSyntax
