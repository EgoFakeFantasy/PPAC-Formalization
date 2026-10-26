/- Native object derivation of the source adjacent-to-all transition lemma. -/
import PPAC.Migration.ConstructionProbePresentationTransitions

namespace PPAC.Migration.ConstructionProbePresentationTransitionsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePath ConstructionProbePresentationTransitions
open ConstructionProbeLiftHomSyntax
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def adjacent {m : Nat} (w factor f p mulN : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound w.succ.succ))
    (.imp (.mem (.bound 0) (.bound w.succ.succ))
      (.imp (Project.Formula.isSuccessor (.bound 0) (.bound 1))
        (transport factor.succ.succ f.succ.succ p.succ.succ mulN.succ.succ 1 0)))))

theorem adjacent_freeClosed {m : Nat} (w factor f p mulN : Fin m) : (adjacent w factor f p mulN).FreeClosed := by
  simp -implicitDefEqProofs [adjacent,Definitional.Formula.FreeClosed,transport_freeClosed]

theorem adjacent_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w factor f p mulN : Fin m) :
    Project.Formula.satisfies env (adjacent w factor f p mulN) ↔
      Adjacent (env.bound w) (env.bound factor) (env.bound f) (env.bound p) (env.bound mulN) := by
  simp only [adjacent,Adjacent,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,
    transport_semantics hM]
  rfl

def allTransitions {m : Nat} (w factor f p mulN : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound w.succ)) (stage w.succ factor.succ f.succ p.succ mulN.succ 0))

theorem allTransitions_freeClosed {m : Nat} (w factor f p mulN : Fin m) : (allTransitions w factor f p mulN).FreeClosed := by
  simp -implicitDefEqProofs [allTransitions,Definitional.Formula.FreeClosed,stage_freeClosed]

theorem allTransitions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w factor f p mulN : Fin m) :
    Project.Formula.satisfies env (allTransitions w factor f p mulN) ↔
      (∀ j, (Project.FirstOrderSemantics.reduct M).mem j (env.bound w) →
        Stage (env.bound w) (env.bound factor) (env.bound f) (env.bound p) (env.bound mulN) j) := by
  simp only [allTransitions,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,stage_semantics hM]
  rfl

def transitionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 13) 2 3)) (.imp (path (0 : Fin 13) 1 2 3 4 5 6) (.imp
    (factorTable (0 : Fin 13) 1 2 6 7) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 13) 1
    8)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 13) 0 8)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (11 : Fin 13) 3 9)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.unit (8 : Fin 13) 10 9)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.associative (8 : Fin 13) 10)) (.imp (preservesProducts (2 : Fin 13) 10 11) (.imp
    (adjacent (0 : Fin 13) 7 11 12 10) (allTransitions (0 : Fin 13) 7 11 12 10))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,path_freeClosed,
      factorTable_freeClosed,preservesProducts_freeClosed,adjacent_freeClosed,allTransitions_freeClosed]

theorem transition_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence transitionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) transitionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),path_semantics hM,factorTable_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge,
    ForcingDiagramPoset.unit_semantics (M := M),ForcingDiagramPoset.associative_semantics (M := M),
    preservesProducts_semantics hM,adjacent_semantics hM,allTransitions_semantics hM]
  intro hw hm hPath hFactor hf hp hOne hUnit hAssoc hPres hAdj
  exact transitions_from_adjacent hM hw hm hPath hFactor hf hp hOne hUnit hAssoc hPres hAdj

theorem transition_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence transitionSentence) := ModelTransfer.derives (fun _ hM => transition_models hM)

end PPAC.Migration.ConstructionProbePresentationTransitionsSyntax
