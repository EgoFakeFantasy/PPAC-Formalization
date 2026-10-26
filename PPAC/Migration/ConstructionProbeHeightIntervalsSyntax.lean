/- Pure native-ZF certificate for the actual source heightIntervals graphs. -/
import PPAC.Migration.ConstructionProbeHeightIntervalGraphs

namespace PPAC.Migration.ConstructionProbeHeightIntervalsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeHeightIntervalGraphs
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def graph {m : Nat} (i : Fin 3) (w Q four D mul S K E H C F G : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge G.succ.succ (1 : Fin (m+2))
  (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound S.succ.succ))
  (ConstructionProbeHeightIntervalGraphs.selected i w.succ.succ Q.succ.succ four.succ.succ D.succ.succ
  mul.succ.succ K.succ.succ E.succ.succ H.succ.succ C.succ.succ F.succ.succ (1 : Fin (m+2)) (0 : Fin
  (m+2)))))))

theorem graph_freeClosed {m : Nat} (i : Fin 3) (w Q four D mul S K E H C F G : Fin m) : (graph i w Q four D mul S K E H C F G).FreeClosed := by
  simp -implicitDefEqProofs
  [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeHeightIntervalGraphs.selected_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (i : Fin 3) (w Q four D mul S K E H C F G : Fin m) :
    Project.Formula.satisfies env (graph i w Q four D mul S K E H C F G) ↔
  Graph i hM (env.bound w) (env.bound Q) (env.bound four) (env.bound D) (env.bound mul) (env.bound S)
  (env.bound K) (env.bound E) (env.bound H) (env.bound C) (env.bound F) (env.bound G) := by
  simp only
  [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality
  hM),KuratowskiZF.source_edge,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,ConstructionProbeHeightIntervalGraphs.selected_semantics
  hM,Project.Term.eval_bound]
  rfl

def laws {m : Nat} (w Q four D mul S A K E H C F O L B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge L.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge B.succ.succ.succ.succ (3 : Fin (m+4)) (0 : Fin
  (m+4)))) (ConstructionProbeIntervalChoices.valid w.succ.succ.succ.succ Q.succ.succ.succ.succ
  four.succ.succ.succ.succ D.succ.succ.succ.succ mul.succ.succ.succ.succ S.succ.succ.succ.succ
  A.succ.succ.succ.succ K.succ.succ.succ.succ E.succ.succ.succ.succ H.succ.succ.succ.succ
  C.succ.succ.succ.succ F.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (1 : Fin (m+4)) (0 : Fin
  (m+4))))))))))

theorem laws_freeClosed {m : Nat} (w Q four D mul S A K E H C F O L B : Fin m) : (laws w Q four D mul S A K E H C F O L B).FreeClosed := by
  simp -implicitDefEqProofs
  [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeIntervalChoices.valid_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q four D mul S A K E H C F O L B : Fin m) :
    Project.Formula.satisfies env (laws w Q four D mul S A K E H C F O L B) ↔
  Laws hM (env.bound w) (env.bound Q) (env.bound four) (env.bound D) (env.bound mul) (env.bound S)
  (env.bound A) (env.bound K) (env.bound E) (env.bound H) (env.bound C) (env.bound F) (env.bound O)
  (env.bound L) (env.bound B) := by
  simp only
  [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality
  hM),KuratowskiZF.source_edge,ConstructionProbeIntervalChoices.valid_semantics hM]
  rfl

def insideBounds {m : Nat} (w Q D mul S A H C F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)))) (.imp (.mem
  (.bound (3 : Fin (m+6))) (.bound D.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (2 : Fin (m+6)))
  (.bound D.succ.succ.succ.succ.succ.succ)) (.imp (ConstructionProbeAlphabet.inCone
  S.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (5 : Fin (m+6))) (.imp
  (ConstructionProbeAlphabet.inCone S.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ (2 :
  Fin (m+6)) (5 : Fin (m+6))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (3 : Fin (m+6)))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ (3 : Fin (m+6))
  (1 : Fin (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  C.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (0 : Fin (m+6)))) (.existsE (.conj
  (ConstructionRealCuts.cut w.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ (0 :
  Fin (m+7))) (.conj (ConstructionCutDifference.value w.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+7)) (5 : Fin (m+7)) (0 : Fin (m+7))) (.conj
  (ConstructionCutAddition.sumCut w.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+7)) (0 : Fin (m+7)) (5 : Fin (m+7)))
  (Project.Formula.subset (.bound (1 : Fin (m+7))) (.bound (0 : Fin (m+7))))))))))))))))))))))

theorem insideBounds_freeClosed {m : Nat} (w Q D mul S A H C F : Fin m) : (insideBounds w Q D mul S A H C F).FreeClosed := by
  simp -implicitDefEqProofs
  [insideBounds,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.inCone_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionCutDifference.value_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem insideBounds_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D mul S A H C F : Fin m) :
    Project.Formula.satisfies env (insideBounds w Q D mul S A H C F) ↔
  InsideBounds hM (env.bound w) (env.bound Q) (env.bound D) (env.bound mul) (env.bound S) (env.bound A)
  (env.bound H) (env.bound C) (env.bound F) := by
  simp only
  [insideBounds,InsideBounds,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality
  hM),KuratowskiZF.source_edge,Project.Formula.satisfies_mem_iff,ConstructionProbeAlphabet.inCone_semantics
  hM,Project.Formula.satisfies_neg_iff,ConstructionBaseMonoid.divides_semantics (M :=
  M),Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionRealCuts.cut_semantics
  hM,ConstructionCutDifference.value_semantics hM,ConstructionCutAddition.sumCut_semantics
  hM,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 18
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 18))) (.imp (ConstructionFractionOrder.carrier (0 :
    Fin 18) (1 : Fin 18)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 18) (1 : Fin 18) (2 : Fin 18))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (3 : Fin 18) (4 : Fin 18) (5 :
    Fin 18))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (3 : Fin 18) (4 : Fin 18) (5 :
    Fin 18))) (.imp (.mem (.bound (6 : Fin 18)) (.bound (3 : Fin 18))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (6 : Fin 18)) (.bound (5 : Fin 18)))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 18) (7 : Fin 18) (3 : Fin 18))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 18) (7 : Fin 18) (3 : Fin 18))) (.imp
    (ConstructionProbeAlphabet.exitGraph (4 : Fin 18) (9 : Fin 18) (6 : Fin 18) (10 : Fin 18)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 18) (3 : Fin 18) (2 : Fin 18))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 18) (3 : Fin 18) (2 : Fin 18))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 18) (7 : Fin 18) (2 : Fin 18))) (.imp
    (ConstructionProbeLetterFloorSyntax.floorLaws (3 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (11
    : Fin 18) (13 : Fin 18)) (.imp (ConstructionProbeCostBoundsSyntax.costBounds (0 : Fin 18) (1 : Fin 18)
    (3 : Fin 18) (4 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (11 : Fin 18) (12 : Fin 18) (13 : Fin
    18)) (.imp (ConstructionProbeIntervalsSyntax.uniformMargins (0 : Fin 18) (1 : Fin 18) (3 : Fin 18) (4
    : Fin 18) (11 : Fin 18) (12 : Fin 18)) (.imp (ConstructionBaseWeights.digits (0 : Fin 18) (14 : Fin
    18) (15 : Fin 18) (16 : Fin 18)) (.imp (Project.Formula.isSuccessor (.bound (17 : Fin 18)) (.bound (16
    : Fin 18))) (.imp (.mem (.bound (17 : Fin 18)) (.bound (0 : Fin 18))) (.existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (2 : Fin (18+3)) (7 : Fin
    18).succ.succ.succ (2 : Fin 18).succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (1 : Fin (18+3)) (7 : Fin 18).succ.succ.succ (2 : Fin 18).succ.succ.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (18+3)) (7 : Fin
    18).succ.succ.succ (2 : Fin 18).succ.succ.succ)) (.conj (graph (0 : Fin 3) (0 : Fin 18).succ.succ.succ
    (1 : Fin 18).succ.succ.succ (17 : Fin 18).succ.succ.succ (3 : Fin 18).succ.succ.succ (4 : Fin
    18).succ.succ.succ (7 : Fin 18).succ.succ.succ (9 : Fin 18).succ.succ.succ (10 : Fin
    18).succ.succ.succ (11 : Fin 18).succ.succ.succ (12 : Fin 18).succ.succ.succ (13 : Fin
    18).succ.succ.succ (2 : Fin (18+3))) (.conj (graph (1 : Fin 3) (0 : Fin 18).succ.succ.succ (1 : Fin
    18).succ.succ.succ (17 : Fin 18).succ.succ.succ (3 : Fin 18).succ.succ.succ (4 : Fin
    18).succ.succ.succ (7 : Fin 18).succ.succ.succ (9 : Fin 18).succ.succ.succ (10 : Fin
    18).succ.succ.succ (11 : Fin 18).succ.succ.succ (12 : Fin 18).succ.succ.succ (13 : Fin
    18).succ.succ.succ (1 : Fin (18+3))) (.conj (graph (2 : Fin 3) (0 : Fin 18).succ.succ.succ (1 : Fin
    18).succ.succ.succ (17 : Fin 18).succ.succ.succ (3 : Fin 18).succ.succ.succ (4 : Fin
    18).succ.succ.succ (7 : Fin 18).succ.succ.succ (9 : Fin 18).succ.succ.succ (10 : Fin
    18).succ.succ.succ (11 : Fin 18).succ.succ.succ (12 : Fin 18).succ.succ.succ (13 : Fin
    18).succ.succ.succ (0 : Fin (18+3))) (.conj (laws (0 : Fin 18).succ.succ.succ (1 : Fin
    18).succ.succ.succ (17 : Fin 18).succ.succ.succ (3 : Fin 18).succ.succ.succ (4 : Fin
    18).succ.succ.succ (7 : Fin 18).succ.succ.succ (8 : Fin 18).succ.succ.succ (9 : Fin 18).succ.succ.succ
    (10 : Fin 18).succ.succ.succ (11 : Fin 18).succ.succ.succ (12 : Fin 18).succ.succ.succ (13 : Fin
    18).succ.succ.succ (2 : Fin (18+3)) (1 : Fin (18+3)) (0 : Fin (18+3))) (insideBounds (0 : Fin
    18).succ.succ.succ (1 : Fin 18).succ.succ.succ (3 : Fin 18).succ.succ.succ (4 : Fin 18).succ.succ.succ
    (7 : Fin 18).succ.succ.succ (8 : Fin 18).succ.succ.succ (11 : Fin 18).succ.succ.succ (12 : Fin
    18).succ.succ.succ (13 : Fin 18).succ.succ.succ))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs
    [Definitional.Formula.FreeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.exitGraph_freeClosed,ConstructionProbeLetterFloorSyntax.floorLaws_freeClosed,ConstructionProbeCostBoundsSyntax.costBounds_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,ConstructionBaseWeights.digits_freeClosed,graph_freeClosed,laws_freeClosed,insideBounds_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only
  [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,ConstructionFractionOrder.carrier_semantics
  hM,ConstructionRealCuts.cutCarrier_semantics hM,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality
  hM),ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq
  (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M :=
  M),ConstructionProbeAlphabet.exitGraph_semantics
  hM,ConstructionProbeLetterFloorSyntax.floorLaws_semantics
  hM,ConstructionProbeCostBoundsSyntax.costBounds_semantics
  hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics
  hM,ConstructionBaseWeights.digits_semantics,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,graph_semantics
  hM,laws_semantics hM,insideBounds_semantics hM,Project.Term.eval_bound]
  exact exists_heightIntervals hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeHeightIntervalsSyntax
