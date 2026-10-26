/- Pure-set certificate for the pinned probe inside/outside cost estimates. -/
import PPAC.Migration.ConstructionProbeCostBounds

namespace PPAC.Migration.ConstructionProbeCostBoundsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeCostBounds ConstructionRealCuts ConstructionCutAddition
open ConstructionProbeAlphabet (inCone inCone_freeClosed inCone_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def pointBound {m : Nat} (w D mul H C : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2 : Fin (m+6)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (1 : Fin
  (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+6)) (0 : Fin (m+6)))) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)))) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (4 : Fin (m+6)))) (.imp (.neg (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+6)) (5 : Fin (m+6))))) (addBound w.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (0 : Fin (m+6)) (1 : Fin
  (m+6)))))))))))))))

theorem pointBound_freeClosed {m : Nat} (w D mul H C : Fin m) : (pointBound w D mul H C).FreeClosed := by
  simp -implicitDefEqProofs [pointBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,addBound_freeClosed]

theorem pointBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul H C : Fin m) :
    Project.Formula.satisfies env (pointBound w D mul H C) ↔
      PointBound hM (env.bound w) (env.bound D) (env.bound mul) (env.bound H) (env.bound C) := by
  simp only
  [pointBound,PointBound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M :=
  M),addBound_semantics hM]
  rfl

def boundedAdd {m : Nat} (w Q a b upper : Fin m) : Project.Formula 1 m :=
  (.conj (addBound w a b upper) (.existsE (.conj (cut w.succ Q.succ (0 : Fin (m+1))) (.conj (sumCut w.succ
  Q.succ a.succ b.succ (0 : Fin (m+1))) (Project.Formula.subset (.bound (0 : Fin (m+1))) (.bound
  upper.succ))))))

theorem boundedAdd_freeClosed {m : Nat} (w Q a b upper : Fin m) : (boundedAdd w Q a b upper).FreeClosed := by
  simp -implicitDefEqProofs [boundedAdd,Definitional.Formula.FreeClosed,addBound_freeClosed,cut_freeClosed,sumCut_freeClosed]

theorem boundedAdd_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q a b upper : Fin m) :
    Project.Formula.satisfies env (boundedAdd w Q a b upper) ↔
      BoundedAdd hM (env.bound w) (env.bound Q) (env.bound a) (env.bound b) (env.bound upper) := by
  simp only
  [boundedAdd,BoundedAdd,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,addBound_semantics
  hM,cut_semantics hM,sumCut_semantics hM]
  rfl

def costBounds {m : Nat} (w Q D mul S A K H C F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (2 : Fin (m+6))) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (inCone S.succ.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (5 : Fin (m+6))) (.imp (inCone
  S.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (5 : Fin (m+6))) (.imp (.neg
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (3 : Fin (m+6))))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (1 : Fin (m+6)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (0 : Fin
  (m+6)))) (boundedAdd w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ (1 : Fin (m+6)) (0 :
  Fin (m+6)) (4 : Fin (m+6)))))))))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge K.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6)))) (.imp (.mem
  (.bound (2 : Fin (m+6))) (.bound D.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ (2 : Fin
  (m+6)) (3 : Fin (m+6)))) (.imp (.neg (inCone S.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ
  (2 : Fin (m+6)) (5 : Fin (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) (1 : Fin (m+6)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge C.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (0 : Fin (m+6)))) (boundedAdd
  w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (0 : Fin (m+6)) (1 : Fin
  (m+6)))))))))))))))))

theorem costBounds_freeClosed {m : Nat} (w Q D mul S A K H C F : Fin m) : (costBounds w Q D mul S A K H C F).FreeClosed := by
  simp -implicitDefEqProofs [costBounds,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,boundedAdd_freeClosed,inCone_freeClosed]

theorem costBounds_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D mul S A K H C F : Fin m) :
    Project.Formula.satisfies env (costBounds w Q D mul S A K H C F) ↔
      CostBounds hM (env.bound w) (env.bound Q) (env.bound D) (env.bound mul) (env.bound S) (env.bound A) (env.bound K) (env.bound H) (env.bound C) (env.bound F) := by
  simp only
  [costBounds,CostBounds,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics
  (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M :=
  M),inCone_semantics hM,boundedAdd_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 17
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 17))) (.imp (ConstructionFractionOrder.carrier (0 : Fin
    17) (1 : Fin 17)) (.imp (cutCarrier (0 : Fin 17) (1 : Fin 17) (2 : Fin 17)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (3 : Fin 17) (4 : Fin 17) (5 : Fin 17))) (.imp
    (ConstructionProbeLetters.representatives (3 : Fin 17) (6 : Fin 17) (7 : Fin 17)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 17) (7 : Fin 17) (6 : Fin 17))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 17) (6 : Fin 17) (3 : Fin 17))) (.imp
    (ConstructionProbeTarget.targetLaws (4 : Fin 17) (10 : Fin 17) (11 : Fin 17) (8 : Fin 17) (9 : Fin 17))
    (.imp (ConstructionProbeLetterFloorSyntax.heightOrder (3 : Fin 17) (4 : Fin 17) (2 : Fin 17) (12 : Fin
    17)) (.imp (pointBound (0 : Fin 17) (3 : Fin 17) (4 : Fin 17) (12 : Fin 17) (13 : Fin 17)) (.imp
    (ConstructionProbeCones.coneLaws (0 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (14 : Fin 17) (15 :
    Fin 17) (16 : Fin 17) (6 : Fin 17) (10 : Fin 17) (8 : Fin 17)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (13 : Fin 17) (3 : Fin 17) (2 : Fin 17))) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (3 : Fin 17) (4 : Fin 17)) (.imp
    (ConstructionProbeAction.actionLaws (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (8 : Fin 17)) (.existsE (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 18) (7 : Fin 18) (3 : Fin 18))) (.conj
    (ConstructionProbeLetterFloorSyntax.graph (4 : Fin 18) (7 : Fin 18) (9 : Fin 18) (13 : Fin 18) (0 : Fin
    18)) (.conj (ConstructionProbeLetterFloorSyntax.floorLaws (4 : Fin 18) (7 : Fin 18) (9 : Fin 18) (10 : Fin
    18) (13 : Fin 18) (0 : Fin 18)) (costBounds (1 : Fin 18) (2 : Fin 18) (4 : Fin 18) (5 : Fin 18) (7 : Fin
    18) (9 : Fin 18) (10 : Fin 18) (13 : Fin 18) (14 : Fin 18) (0 : Fin 18))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,cutCarrier_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionProbeTarget.targetLaws_freeClosed,
      ConstructionProbeLetterFloorSyntax.heightOrder_freeClosed,pointBound_freeClosed,
      ConstructionProbeCones.coneLaws_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeAction.actionLaws_freeClosed,ConstructionProbeLetterFloorSyntax.graph_freeClosed,
      ConstructionProbeLetterFloorSyntax.floorLaws_freeClosed,costBounds_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,cutCarrier_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeTarget.targetLaws_semantics hM,
    ConstructionProbeLetterFloorSyntax.heightOrder_semantics hM,pointBound_semantics hM,
    ConstructionProbeCones.coneLaws_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeAction.actionLaws_semantics hM,ConstructionProbeLetterFloorSyntax.graph_semantics hM,
    ConstructionProbeLetterFloorSyntax.floorLaws_semantics hM,costBounds_semantics hM]
  intro hw hQ hR hm hI hA hK hTarget hH hPoint hCones hC hJ hAction
  exact exists_cost_bounds hm hI hA hK hTarget hH hPoint hCones hw hQ hR hC hJ hAction

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeCostBoundsSyntax
