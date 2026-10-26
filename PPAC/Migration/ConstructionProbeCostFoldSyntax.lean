/- Original-kernel certificate for the SAME Word carrier's actual gateCap
and unique cost graph, with exact rawCost recurrence and 0 < cost <= 1. -/
import PPAC.Migration.ConstructionProbeCostFold

namespace PPAC.Migration.ConstructionProbeCostFoldSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def laws {m : Nat} (w D S zero W Q C V Cap LC : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ D.succ.succ.succ (2 :
Fin (m+3)) (1 : Fin (m+3))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge LC.succ.succ.succ (1 : Fin
(m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ.succ (2 : Fin (m+3)) (0 :
Fin (m+3))))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.cons w.succ.succ.succ.succ
D.succ.succ.succ.succ S.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (1 : Fin (m+4))) (.imp (.mem (.bound
(1 : Fin (m+4))) (.bound W.succ.succ.succ.succ)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
LC.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin (m+4)))) (.existsE (.conj (ProjectSyntax.encode id
(Source.SetLanguage.edge LC.succ.succ.succ.succ.succ (3 : Fin (m+5)) (0 : Fin (m+5))))
(ConstructionProbeCostOperation.update w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ
Cap.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ (2 : Fin (m+5)) (4 : Fin (m+5)) (0 : Fin (m+5)) (1 : Fin
(m+5)))))))))))))

theorem laws_freeClosed {m : Nat} (w D S zero W Q C V Cap LC : Fin m) : (laws w D S zero W Q C V Cap LC).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed,ConstructionProbeCostOperation.update_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero W Q C V Cap LC : Fin m) :
    Project.Formula.satisfies env (laws w D S zero W Q C V Cap LC) ↔ ConstructionProbeCostFold.Laws hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound W) (env.bound Q) (env.bound C) (env.bound V) (env.bound Cap) (env.bound LC) := by
  simp only
    [laws,ConstructionProbeCostFold.Laws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeRaw.old_semantics
    hM,ConstructionProbeRaw.cons_semantics hM,ConstructionProbeCostOperation.update_semantics hM]
  rfl

def positive {m : Nat} (V : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge V.succ.succ (1 : Fin (m+2)) (0 : Fin
(m+2)))) (.existsE (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+3))))))))

theorem positive_freeClosed {m : Nat} (V : Fin m) : (positive V).FreeClosed := by
  simp -implicitDefEqProofs [positive,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem positive_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V : Fin m) :
    Project.Formula.satisfies env (positive V) ↔ ∀ s d, PureKuratowski.PairMember M s d (env.bound V) → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d := by
  simp only
    [positive,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 16
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 16))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 16)))
(.imp (.mem (.bound (3 : Fin 16)) (.bound (0 : Fin 16))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 16)
(8 : Fin 16)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 16) (8 : Fin 16) (9 : Fin 16)) (.imp
(ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 16) (4 : Fin 16) (13 : Fin 16))) (.imp
(ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 16) (4 : Fin 16) (13 : Fin 16))) (.imp
(ConstructionProbeWord.wordCarrier (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6 : Fin 16)
(7 : Fin 16)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 16) (1 : Fin 16) (7 : Fin
16))) (.imp (ConstructionProbeOldEmbeddingSyntax.oldGraph (3 : Fin 16) (1 : Fin 16) (10 : Fin 16)) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 16) (1 : Fin 16) (9 : Fin 16))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 16) (2 : Fin 16) (9 : Fin 16))) (.imp (.mem
(.bound (14 : Fin 16)) (.bound (9 : Fin 16))) (.imp (.existsE (.mem (.bound (0 : Fin 17)) (.bound (15 : Fin
17)))) (.imp (ConstructionProbeGateCap.bounds (14 : Fin 16) (11 : Fin 16)) (.imp (positive (12 : Fin 16))
(.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 18) (9 : Fin 18) (11 :
Fin 18))) (.conj (ConstructionProbeGateCap.graph (3 : Fin 18) (9 : Fin 18) (6 : Fin 18) (17 : Fin 18) (12 : Fin
18) (13 : Fin 18) (16 : Fin 18) (1 : Fin 18)) (.conj (ConstructionProbeGateCap.bounds (16 : Fin 18) (1 : Fin
18)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 18) (9 : Fin 18) (11 : Fin 18))) (.conj
(laws (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (9 : Fin 18) (10 : Fin 18) (13 : Fin 18) (14 : Fin 18)
(1 : Fin 18) (0 : Fin 18)) (.conj (ConstructionProbeGateCap.bounds (16 : Fin 18) (0 : Fin 18)) (.forallE (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 19) (10 : Fin 19) (12 : Fin 19))) (.imp (laws (3 :
Fin 19) (4 : Fin 19) (5 : Fin 19) (6 : Fin 19) (10 : Fin 19) (11 : Fin 19) (14 : Fin 19) (15 : Fin 19) (2 : Fin
19) (0 : Fin 19)) (Project.Formula.extensionalEq (.bound (0 : Fin 19)) (.bound (1 : Fin
19))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,
      ConstructionProbeGateCap.graph_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,laws_freeClosed,positive_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeGateCap.graph_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,
    laws_semantics hM,positive_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact ConstructionProbeCostFold.exists_bounded_cost hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeCostFoldSyntax
