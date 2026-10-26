/- Original-kernel certificate connecting actual quarter and addition graphs. -/
import PPAC.Migration.ConstructionCutQuarterSum
import PPAC.Migration.ConstructionCutArithmeticSyntax

namespace PPAC.Migration.ConstructionCutQuarterSumSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCutQuarterSum
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def linkLaws {m : Nat} (R G F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (.existsE (.conj (.mem (.bound (0 : Fin (m+3))) (.bound R.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ (1 : Fin (m+3)) (1 : Fin (m+3)) (0 :
  Fin (m+3)))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ (0 : Fin (m+3))
  (0 : Fin (m+3)) (2 : Fin (m+3)))) (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product G.succ.succ.succ.succ.succ (3 : Fin (m+5)) (3 : Fin (m+5)) (1 : Fin (m+5))))
  (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ.succ.succ (1 : Fin (m+5)) (1 :
  Fin (m+5)) (0 : Fin (m+5)))) (Project.Formula.extensionalEq (.bound (0 : Fin (m+5))) (.bound (4 : Fin
  (m+5)))))))))))))))

theorem linkLaws_freeClosed {m : Nat} (R G F : Fin m) : (linkLaws R G F).FreeClosed := by
  simp -implicitDefEqProofs [linkLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem linkLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R G F : Fin m) :
    Project.Formula.satisfies env (linkLaws R G F) ↔ LinkLaws (env.bound R) (env.bound G) (env.bound F) := by
  simp only [linkLaws,LinkLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 3))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 3)
    (1 : Fin 3)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeLetters.representatives (9 : Fin 10) (9 : Fin 10) (6 : Fin 10)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 10) (6 : Fin 10) (9 : Fin 10))) (.conj
    (ConstructionCutArithmeticSyntax.graph (7 : Fin 10) (8 : Fin 10) (9 : Fin 10) (5 : Fin 10)) (.conj
    (ConstructionCutArithmeticSyntax.laws (9 : Fin 10) (5 : Fin 10)) (.conj (ConstructionBaseWeights.digits (7
    : Fin 10) (4 : Fin 10) (3 : Fin 10) (2 : Fin 10)) (.conj (Project.Formula.isSuccessor (.bound (1 : Fin
    10)) (.bound (2 : Fin 10))) (.conj (.mem (.bound (1 : Fin 10)) (.bound (7 : Fin 10))) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 10) (9 : Fin 10) (9 : Fin 10))) (.conj
    (ConstructionCutDivisionSyntax.graph (7 : Fin 10) (8 : Fin 10) (1 : Fin 10) (9 : Fin 10) (0 : Fin 10))
    (.conj (ConstructionCutDivisionSyntax.laws (0 : Fin 10)) (linkLaws (9 : Fin 10) (5 : Fin 10) (0 : Fin
    10))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionCutArithmeticSyntax.graph_freeClosed,
      ConstructionCutArithmeticSyntax.laws_freeClosed,ConstructionBaseWeights.digits_freeClosed,
      ConstructionCutDivisionSyntax.graph_freeClosed,ConstructionCutDivisionSyntax.laws_freeClosed,linkLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeLetters.representatives_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionCutArithmeticSyntax.graph_semantics hM,ConstructionCutArithmeticSyntax.laws_semantics hM,
    ConstructionBaseWeights.digits_semantics,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_mem_iff,
    ConstructionCutDivisionSyntax.graph_semantics hM,ConstructionCutDivisionSyntax.laws_semantics hM,linkLaws_semantics hM]
  intro hw hQ hR
  exact exists_link hM hw hQ hR

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionCutQuarterSumSyntax
