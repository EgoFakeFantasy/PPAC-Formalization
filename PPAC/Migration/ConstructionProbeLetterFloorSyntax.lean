/- Pure membership/equality certificate for the pinned letter-floor graph. -/
import PPAC.Migration.ConstructionProbeLetterFloor

namespace PPAC.Migration.ConstructionProbeLetterFloorSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeLetterFloor ConstructionRealCuts
open ConstructionProbeAlphabet (inCone inCone_freeClosed inCone_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def heightOrder {m : Nat} (D mul R H : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo H D R)) (.conj (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.existsE
  (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+3)))))))) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin
  (m+4)))) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ
  mul.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)))) (Project.Formula.subset (.bound (1 : Fin (m+4)))
  (.bound (0 : Fin (m+4)))))))))))))

theorem heightOrder_freeClosed {m : Nat} (D mul R H : Fin m) : (heightOrder D mul R H).FreeClosed := by
  simp -implicitDefEqProofs [heightOrder,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem heightOrder_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul R H : Fin m) :
    Project.Formula.satisfies env (heightOrder D mul R H) ↔
      HeightOrder (env.bound D) (env.bound mul) (env.bound R) (env.bound H) := by
  simp only [heightOrder,HeightOrder,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def graph {m : Nat} (D S A H F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0
  : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound S.succ.succ)) (floor D.succ.succ S.succ.succ
  A.succ.succ H.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (D S A H F : Fin m) : (graph D S A H F).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,floor_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S A H F : Fin m) :
    Project.Formula.satisfies env (graph D S A H F) ↔
      Graph (env.bound D) (env.bound S) (env.bound A) (env.bound H) (env.bound F) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    floor_semantics hM]
  rfl

def floorLaws {m : Nat} (D S A K H F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin (m+2)) (0
  : Fin (m+2)))) (.conj (.existsE (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin (m+3))))) (.conj (.forallE
  (.forallE (.imp (.mem (.bound (1 : Fin (m+4))) (.bound D.succ.succ.succ.succ)) (.imp (inCone
  S.succ.succ.succ.succ A.succ.succ.succ.succ (1 : Fin (m+4)) (3 : Fin (m+4))) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge H.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin (m+4))))
  (Project.Formula.subset (.bound (0 : Fin (m+4))) (.bound (2 : Fin (m+4))))))))) (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin
  (m+4)))) (Project.Formula.subset (.bound (2 : Fin (m+4))) (.bound (0 : Fin (m+4)))))))))))))

theorem floorLaws_freeClosed {m : Nat} (D S A K H F : Fin m) : (floorLaws D S A K H F).FreeClosed := by
  simp -implicitDefEqProofs [floorLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,inCone_freeClosed]

theorem floorLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S A K H F : Fin m) :
    Project.Formula.satisfies env (floorLaws D S A K H F) ↔
      FloorLaws (env.bound D) (env.bound S) (env.bound A) (env.bound K) (env.bound H) (env.bound F) := by
  simp only [floorLaws,FloorLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    inCone_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (cutCarrier (0 : Fin 13) (1 : Fin 13) (2 : Fin 13)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (3 : Fin 13) (4 : Fin 13) (5 : Fin 13))) (.imp
    (ConstructionProbeLetters.representatives (3 : Fin 13) (6 : Fin 13) (7 : Fin 13)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (8 : Fin 13) (7 : Fin 13) (6 : Fin 13))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 13) (6 : Fin 13) (3 : Fin 13))) (.imp
    (ConstructionProbeTarget.targetLaws (4 : Fin 13) (10 : Fin 13) (11 : Fin 13) (8 : Fin 13) (9 : Fin 13))
    (.imp (heightOrder (3 : Fin 13) (4 : Fin 13) (2 : Fin 13) (12 : Fin 13)) (.imp
    (ConstructionProbeAction.actionLaws (4 : Fin 13) (5 : Fin 13) (6 : Fin 13) (8 : Fin 13)) (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 14) (7 : Fin 14) (3 : Fin 14)))
    (.conj (graph (4 : Fin 14) (7 : Fin 14) (9 : Fin 14) (13 : Fin 14) (0 : Fin 14)) (floorLaws (4 : Fin 14)
    (7 : Fin 14) (9 : Fin 14) (10 : Fin 14) (13 : Fin 14) (0 : Fin 14)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      cutCarrier_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbeTarget.targetLaws_freeClosed,heightOrder_freeClosed,
      ConstructionProbeAction.actionLaws_freeClosed,graph_freeClosed,floorLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    cutCarrier_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeTarget.targetLaws_semantics hM,heightOrder_semantics hM,
    ConstructionProbeAction.actionLaws_semantics hM,graph_semantics hM,floorLaws_semantics hM]
  intro hR hm hI hA hK hTarget hH hAction
  exact exists_floor_graph hm hI hA hK hTarget hH hR hAction

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeLetterFloorSyntax
