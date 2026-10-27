/- Pinned ConservativeExtensions.OverlapPrescription.map/valid_map_iff
consumed by MonoidRounds.MergerData.map. Pure native-ZF producer quantifies
all internal indices, starts, target elements and exact mapped graphs. -/
import PPAC.Migration.ConstructionMergerPrescriptionMap

namespace PPAC.Migration.ConstructionMergerPrescriptionMapSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerPrescriptionMap
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def graph {m : Nat} (P f PN : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound PN.succ)) (ConstructionMergerPrescriptionMap.entry
  P.succ f.succ (0 : Fin (m+1)))))

theorem graph_freeClosed {m : Nat} (P f PN : Fin m) :
    (graph P f PN).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ConstructionMergerPrescriptionMap.entry_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P f PN : Fin m) :
    Project.Formula.satisfies env (graph P f PN) ↔ Graph (env.bound P) (env.bound f) (env.bound PN) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionMergerPrescriptionMap.entry_semantics hM]
  rfl


def mapped {m : Nat} (P f PN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.iff (ConstructionMergerRelations.start PN.succ.succ.succ.succ (3 :
  Fin (m+4)) (2 : Fin (m+4)) (1 : Fin (m+4)) (0 : Fin (m+4))) (.existsE (.existsE (.conj
  (ConstructionMergerRelations.start P.succ.succ.succ.succ.succ.succ (3 : Fin (m+4)).succ.succ (2 : Fin
  (m+4)).succ.succ (1 : Fin (m+6)) (0 : Fin (m+6))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ (1 : Fin (m+6)) (1 : Fin (m+4)).succ.succ)) (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (0 : Fin (m+6)) (0 : Fin
  (m+4)).succ.succ)))))))))))

theorem mapped_freeClosed {m : Nat} (P f PN : Fin m) :
    (mapped P f PN).FreeClosed := by
  simp -implicitDefEqProofs [mapped,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionMergerRelations.start_freeClosed]

theorem mapped_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P f PN : Fin m) :
    Project.Formula.satisfies env (mapped P f PN) ↔ Mapped (env.bound P) (env.bound f) (env.bound PN) := by
  simp only [mapped,Mapped,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionMergerRelations.start_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 9 (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin
    9) (2 : Fin 9) (3 : Fin 9))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (6 : Fin
    9) (7 : Fin 9) (8 : Fin 9))) (.imp (ConstructionMergerRelations.prescription (0 : Fin 9) (1 : Fin 9) (4 :
    Fin 9)) (.imp (ConstructionProbeConservativeSyntax.conservative (1 : Fin 9) (6 : Fin 9) (2 : Fin 9) (7 :
    Fin 9) (5 : Fin 9)) (.imp (ConstructionProbeLiftHomSyntax.preservesProducts (2 : Fin 9) (7 : Fin 9) (5 :
    Fin 9)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 9) (2 : Fin 9)) (.existsE
    (.conj (graph (4 : Fin 9).succ (5 : Fin 9).succ (0 : Fin 10)) (.conj (mapped (4 : Fin 9).succ (5 : Fin
    9).succ (0 : Fin 10)) (.conj (ConstructionMergerRelations.prescription (0 : Fin 9).succ (6 : Fin 9).succ
    (0 : Fin 10)) (.conj (.iff (ConstructionMergerRelations.valid (0 : Fin 9).succ (6 : Fin 9).succ (7 : Fin
    9).succ (0 : Fin 10)) (ConstructionMergerRelations.valid (0 : Fin 9).succ (1 : Fin 9).succ (2 : Fin
    9).succ (4 : Fin 9).succ)) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 9).succ.succ.succ.succ.succ.succ.succ (3 : Fin
    (9+7)) (1 : Fin (9+7)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin
    9).succ.succ.succ.succ.succ.succ.succ (2 : Fin (9+7)) (0 : Fin (9+7)))) (.iff
    (ConstructionMergerRelations.rel (0 : Fin 9).succ.succ.succ.succ.succ.succ.succ (6 : Fin
    9).succ.succ.succ.succ.succ.succ.succ (7 : Fin 9).succ.succ.succ.succ.succ.succ.succ (0 : Fin
    10).succ.succ.succ.succ.succ.succ (5 : Fin (9+7)) (1 : Fin (9+7)) (4 : Fin (9+7)) (0 : Fin (9+7)))
    (ConstructionMergerRelations.rel (0 : Fin 9).succ.succ.succ.succ.succ.succ.succ (1 : Fin
    9).succ.succ.succ.succ.succ.succ.succ (2 : Fin 9).succ.succ.succ.succ.succ.succ.succ (4 : Fin
    9).succ.succ.succ.succ.succ.succ.succ (5 : Fin (9+7)) (3 : Fin (9+7)) (4 : Fin (9+7)) (2 : Fin
    (9+7)))))))))))) (.forallE (.imp (graph (4 : Fin 9).succ.succ (5 : Fin 9).succ.succ (0 : Fin (9+2)))
    (Project.Formula.extensionalEq (.bound (0 : Fin (9+2))) (.bound (0 : Fin 10).succ)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      graph_freeClosed,mapped_freeClosed,ConstructionMergerRelations.valid_freeClosed,
      ConstructionMergerRelations.rel_freeClosed,Project.Formula.extensionalEq]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionMergerRelations.prescription_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    graph_semantics hM,mapped_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionMergerRelations.rel_semantics hM]
  intro hm hmN hP hCons hPres hJoins
  exact ConstructionMergerPrescriptionMap.exists_system hM hm hmN hP hCons hPres hJoins

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionMergerPrescriptionMapSyntax
