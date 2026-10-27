/- Pinned MonoidRounds.Request.map:43, both actual source constructors.
Native-ZF object theorem, arbitrary internal omega paths and finite n.
No host-level sum or profile conclusion substitutes for the mapped data. -/
import PPAC.Migration.ConstructionRequestMaps

namespace PPAC.Migration.ConstructionRequestMapsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRequestMaps
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def mapsRequests {m : Nat} (w D mul e zero N mulN eN f : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+3))) (.bound D.succ.succ.succ)) (.imp
  (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+3))) (.bound e.succ.succ.succ))) (.imp
  (ConstructionProbePath.path w.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  zero.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))) (.existsE (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ (2 : Fin
  (m+3)).succ.succ.succ (2 : Fin (m+6)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ (1 : Fin (m+3)).succ.succ.succ (1 : Fin (m+6)))) (.conj (.mem (.bound (1 :
  Fin (m+6))) (.bound N.succ.succ.succ.succ.succ.succ)) (.conj (.neg (Project.Formula.extensionalEq (.bound
  (1 : Fin (m+6))) (.bound eN.succ.succ.succ.succ.succ.succ))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo (0 : Fin (m+6)) w.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap (0 : Fin
  (m+3)).succ.succ.succ f.succ.succ.succ.succ.succ.succ (0 : Fin (m+6))) (.conj (ConstructionProbePath.path
  w.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ
  eN.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (0 : Fin (m+6)))
  (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+3)).succ.succ.succ.succ.succ.succ (2 : Fin
  (m+9)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+3)).succ.succ.succ.succ.succ.succ (1 : Fin
  (m+9)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+9))
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ConstructionProbeMappedPathSyntax.nodeMap (0 : Fin (m+3)).succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+9))) (.conj (Project.Formula.extensionalEq
  (.bound (2 : Fin (m+9))) (.bound (2 : Fin (m+6)).succ.succ.succ)) (.conj (Project.Formula.extensionalEq
  (.bound (1 : Fin (m+9))) (.bound (1 : Fin (m+6)).succ.succ.succ)) (Project.Formula.extensionalEq (.bound
  (0 : Fin (m+9))) (.bound (0 : Fin (m+6)).succ.succ.succ))))))))))))))))))))))))))) (.forallE (.forallE
  (.imp (.mem (.bound (1 : Fin (m+2))) (.bound w.succ.succ)) (.imp (.existsE (.mem (.bound (0 : Fin (m+3)))
  (.bound (1 : Fin (m+2)).succ))) (.imp (ConstructionMergerRelations.prescription (1 : Fin (m+2))
  D.succ.succ (0 : Fin (m+2))) (.imp (ConstructionMergerRelations.valid (1 : Fin (m+2)) D.succ.succ
  mul.succ.succ (0 : Fin (m+2))) (.existsE (.conj (ConstructionMergerPrescriptionMapSyntax.graph (0 : Fin
  (m+2)).succ f.succ.succ.succ (0 : Fin (m+3))) (.conj (ConstructionMergerPrescriptionMapSyntax.mapped (0 :
  Fin (m+2)).succ f.succ.succ.succ (0 : Fin (m+3))) (.conj (.mem (.bound (1 : Fin (m+2)).succ) (.bound
  w.succ.succ.succ)) (.conj (.existsE (.mem (.bound (0 : Fin (m+4))) (.bound (1 : Fin (m+2)).succ.succ)))
  (.conj (ConstructionMergerRelations.prescription (1 : Fin (m+2)).succ N.succ.succ.succ (0 : Fin (m+3)))
  (.conj (ConstructionMergerRelations.valid (1 : Fin (m+2)).succ N.succ.succ.succ mulN.succ.succ.succ (0 :
  Fin (m+3))) (.forallE (.imp (ConstructionMergerPrescriptionMapSyntax.graph (0 : Fin (m+2)).succ.succ
  f.succ.succ.succ.succ (0 : Fin (m+4))) (Project.Formula.extensionalEq (.bound (0 : Fin (m+4))) (.bound (0
  : Fin (m+3)).succ))))))))))))))))))

theorem mapsRequests_freeClosed {m : Nat} (w D mul e zero N mulN eN f : Fin m) :
    (mapsRequests w D mul e zero N mulN eN f).FreeClosed := by
  simp -implicitDefEqProofs [mapsRequests,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionProbePath.path_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,ConstructionMergerPrescriptionMapSyntax.mapped_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed]

theorem mapsRequests_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e zero N mulN eN f : Fin m) :
    Project.Formula.satisfies env (mapsRequests w D mul e zero N mulN eN f) ↔ MapsRequests (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound zero) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound f) := by
  simp only [mapsRequests,MapsRequests,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbePath.path_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,ConstructionMergerPrescriptionMapSyntax.mapped_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM]
  rfl


def mapsSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 9 (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin
    9) (2 : Fin 9) (3 : Fin 9))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (5 : Fin
    9) (6 : Fin 9) (7 : Fin 9))) (.imp (ConstructionProbeConservativeSyntax.conservative (1 : Fin 9) (5 : Fin
    9) (2 : Fin 9) (6 : Fin 9) (8 : Fin 9)) (.imp (ConstructionProbeLiftHomSyntax.preservesProducts (2 : Fin
    9) (6 : Fin 9) (8 : Fin 9)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (8 : Fin 9) (3 : Fin
    9) (7 : Fin 9))) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 9) (2 : Fin 9))
    (mapsRequests (0 : Fin 9) (1 : Fin 9) (2 : Fin 9) (3 : Fin 9) (4 : Fin 9) (5 : Fin 9) (6 : Fin 9) (7 : Fin
    9) (8 : Fin 9)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,mapsRequests_freeClosed]

theorem maps_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence mapsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) mapsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,mapsRequests_semantics hM]
  exact fun hm hmN hCons hPres hOne hJoins => maps_requests hM hm hmN hCons hPres hOne hJoins

theorem maps_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence mapsSentence) := ModelTransfer.derives (fun _ hM => maps_models hM)

end PPAC.Migration.ConstructionRequestMapsSyntax
