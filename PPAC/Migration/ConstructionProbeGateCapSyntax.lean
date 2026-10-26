/- Original-kernel certificate for pinned OldMinimum/gateCap, retaining
its exact minimum-cost/default-one alternatives and non-strict cost bound. -/
import PPAC.Migration.ConstructionProbeGateCap

namespace PPAC.Migration.ConstructionProbeGateCapSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeGateCap
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 9
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (0 : Fin 9) (2 : Fin 9) (3 : Fin 9))) (.imp
(ProjectSyntax.encode id (ForcingDiagramPoset.conical (0 : Fin 9) (2 : Fin 9) (3 : Fin 9))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 9) (0 : Fin 9) (1 : Fin 9))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 9) (0 : Fin 9) (8 : Fin 9))) (.imp (.mem (.bound (7
: Fin 9)) (.bound (8 : Fin 9))) (.imp (.existsE (.mem (.bound (0 : Fin 10)) (.bound (8 : Fin 10)))) (.imp
(bounds (7 : Fin 9) (6 : Fin 9)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin
10) (2 : Fin 10) (9 : Fin 10))) (.conj (graph (1 : Fin 10) (2 : Fin 10) (3 : Fin 10) (5 : Fin 10) (6 : Fin 10)
(7 : Fin 10) (8 : Fin 10) (0 : Fin 10)) (.conj (bounds (8 : Fin 10) (0 : Fin 10)) (.conj (.forallE (.forallE
(.forallE (.imp (.mem (.bound (2 : Fin 13)) (.bound (5 : Fin 13))) (.imp (oldMinimum (4 : Fin 13) (5 : Fin 13)
(6 : Fin 13) (8 : Fin 13) (9 : Fin 13) (2 : Fin 13) (1 : Fin 13)) (.imp (ProjectSyntax.encode id
(Source.SetLanguage.edge (10 : Fin 13) (1 : Fin 13) (0 : Fin 13))) (ProjectSyntax.encode id
(Source.SetLanguage.edge (3 : Fin 13) (2 : Fin 13) (0 : Fin 13))))))))) (.conj (.forallE (.imp (.mem (.bound (0
: Fin 11)) (.bound (3 : Fin 11))) (.imp (.neg (.existsE (oldMinimum (3 : Fin 12) (4 : Fin 12) (5 : Fin 12) (7 :
Fin 12) (8 : Fin 12) (1 : Fin 12) (0 : Fin 12)))) (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin 11)
(0 : Fin 11) (9 : Fin 11)))))) (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 11)
(3 : Fin 11) (10 : Fin 11))) (.imp (graph (2 : Fin 11) (3 : Fin 11) (4 : Fin 11) (6 : Fin 11) (7 : Fin 11) (8 :
Fin 11) (9 : Fin 11) (0 : Fin 11)) (Project.Formula.extensionalEq (.bound (0 : Fin 11)) (.bound (1 : Fin
11)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      graph_freeClosed,bounds_freeClosed,oldMinimum_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics,ForcingDiagramPoset.conical_semantics,
    ForcingSupportSize.mapsTo_semantics (M := M),Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,graph_semantics hM,bounds_semantics hM,oldMinimum_semantics hM]
  exact exists_cap hM

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeGateCapSyntax
