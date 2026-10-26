/- Pure native-ZF original-kernel certificate for the actual product graph
and literal minimum used by pinned ProbeMargins.rawHeight/rawCost. -/
import PPAC.Migration.ConstructionCutProduct
import PPAC.Migration.ConstructionCutMinimum

namespace PPAC.Migration.ConstructionWordArithmeticSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def graph {m : Nat} (w Q R G : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ (2
: Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)))) (.conj (.mem (.bound (2 : Fin (m+3))) (.bound
R.succ.succ.succ)) (.conj (.mem (.bound (1 : Fin (m+3))) (.bound R.succ.succ.succ))
(ConstructionCutProduct.value w.succ.succ.succ Q.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin
(m+3)))))))))

theorem graph_freeClosed {m : Nat} (w Q R G : Fin m) : (graph w Q R G).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ConstructionCutProduct.value_freeClosed,ProjectSyntax.freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R G : Fin m) :
    Project.Formula.satisfies env (graph w Q R G) ↔ ConstructionCutProduct.Graph hM (env.bound w) (env.bound Q) (env.bound R) (env.bound G) := by
  simp only
    [graph,ConstructionCutProduct.Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M :=
    M),ConstructionCutProduct.value_semantics hM]
  rfl

def laws {m : Nat} (R G : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
G.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id
(ForcingDiagramOrder.product G.succ.succ.succ (1 : Fin (m+3)) (2 : Fin (m+3)) (0 : Fin (m+3)))))))) (.conj
(.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
(ForcingDiagramOrder.product G.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)) (3 : Fin (m+6))))
(.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (1
: Fin (m+6)) (0 : Fin (m+6)))) (.imp (Project.Formula.subset (.bound (5 : Fin (m+6))) (.bound (2 : Fin
(m+6)))) (.imp (Project.Formula.subset (.bound (4 : Fin (m+6))) (.bound (1 : Fin (m+6))))
(Project.Formula.subset (.bound (3 : Fin (m+6))) (.bound (0 : Fin (m+6)))))))))))))) (.conj (.forallE
(.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound R.succ.succ)) (.imp (.mem (.bound (0 : Fin (m+2)))
(.bound R.succ.succ)) (.imp (.forallE (.neg (.mem (.bound (0 : Fin (m+3))) (.bound (2 : Fin (m+3)))))) (.conj
(ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)) (1 : Fin
(m+2)))) (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ (0 : Fin (m+2)) (1 : Fin (m+2)) (1
: Fin (m+2)))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
G.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3)))) (.imp (.existsE (.mem (.bound (0 : Fin
(m+4))) (.bound (3 : Fin (m+4))))) (.imp (.existsE (.mem (.bound (0 : Fin (m+4))) (.bound (2 : Fin (m+4)))))
(.existsE (.mem (.bound (0 : Fin (m+4))) (.bound (1 : Fin (m+4))))))))))))))

theorem laws_freeClosed {m : Nat} (R G : Fin m) : (laws R G).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R G : Fin m) :
    Project.Formula.satisfies env (laws R G) ↔ ConstructionCutProduct.Laws (env.bound R) (env.bound G) := by
  simp only
    [laws,ConstructionCutProduct.Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def totalMinimum {m : Nat} (R : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound R.succ.succ)) (.imp (.mem (.bound (0 : Fin
(m+2))) (.bound R.succ.succ)) (.existsE (.conj (.mem (.bound (0 : Fin (m+3))) (.bound R.succ.succ.succ))
(.conj (ConstructionCutMinimum.value (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3))) (.conj
(Project.Formula.subset (.bound (0 : Fin (m+3))) (.bound (2 : Fin (m+3)))) (.conj (Project.Formula.subset
(.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+3)))) (.conj (.disj (Project.Formula.extensionalEq (.bound (0 :
Fin (m+3))) (.bound (2 : Fin (m+3)))) (Project.Formula.extensionalEq (.bound (0 : Fin (m+3))) (.bound (1 : Fin
(m+3))))) (.conj (.imp (.existsE (.mem (.bound (0 : Fin (m+4))) (.bound (3 : Fin (m+4))))) (.imp (.existsE
(.mem (.bound (0 : Fin (m+4))) (.bound (2 : Fin (m+4))))) (.existsE (.mem (.bound (0 : Fin (m+4))) (.bound (1
: Fin (m+4))))))) (.forallE (.imp (ConstructionCutMinimum.value (3 : Fin (m+4)) (2 : Fin (m+4)) (0 : Fin
(m+4))) (Project.Formula.extensionalEq (.bound (0 : Fin (m+4))) (.bound (1 : Fin (m+4)))))))))))))))))

theorem totalMinimum_freeClosed {m : Nat} (R : Fin m) : (totalMinimum R).FreeClosed := by
  simp -implicitDefEqProofs [totalMinimum,Definitional.Formula.FreeClosed,ConstructionCutMinimum.value_freeClosed]

theorem totalMinimum_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Fin m) :
    Project.Formula.satisfies env (totalMinimum R) ↔ ConstructionCutMinimum.Total (env.bound R) := by
  simp only
    [totalMinimum,ConstructionCutMinimum.Total,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_extensionalEq_iff_eq
    (ModelTransfer.extensionality hM),Project.Term.eval_bound,ConstructionCutMinimum.value_semantics]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 3))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 3) (1 :
Fin 3)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)) (.existsE (.existsE (.conj
(ConstructionProbeLetters.representatives (4 : Fin 5) (4 : Fin 5) (1 : Fin 5)) (.conj (ProjectSyntax.encode id
(Source.SetLanguage.mapsTo (0 : Fin 5) (1 : Fin 5) (4 : Fin 5))) (.conj (graph (2 : Fin 5) (3 : Fin 5) (4 :
Fin 5) (0 : Fin 5)) (.conj (laws (4 : Fin 5) (0 : Fin 5)) (totalMinimum (4 : Fin 5)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,graph_freeClosed,laws_freeClosed,totalMinimum_freeClosed]

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
    graph_semantics hM,laws_semantics hM,totalMinimum_semantics hM]
  intro hw hQ hR
  obtain ⟨I,G,hI,hG,hGraph⟩ := ConstructionCutProduct.exists_graph hM hw hQ hR
  exact ⟨I,G,hI,hG,hGraph,ConstructionCutProduct.graph_laws hM hw hQ hR hGraph,
    ConstructionCutMinimum.total hM hw hQ hR⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionWordArithmeticSyntax
