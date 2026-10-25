/- Source CohenForcing.Condition uses countable graphs with values in Bool.
Instantiate the accepted carrier/action construction at internal omega and
von Neumann two, directly consuming native omega/one/successor constructors. -/
import PPAC.Migration.ForcingProductFamily
import YesMetaZFC.SetTheory.Ord.Natural
import YesMetaZFC.SetTheory.Ord.Arithmetic.Semantics

namespace PPAC.Migration.ForcingProductParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Existing ordinal-one and successor predicates define exactly von Neumann two. -/
def two {m : Nat} (B : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (Project.Formula.isOrdinalOne (.bound 0))
    (Project.Formula.isSuccessor (.bound B.succ) (.bound 0)))

theorem two_freeClosed {m : Nat} (B : Fin m) : (two B).FreeClosed := by
  simp -implicitDefEqProofs [two, Definitional.Formula.FreeClosed]

theorem two_semantics {m : Nat} (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (B : Fin m) :
    Project.Formula.satisfies env (two B) ↔ ∃ one, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf (env.bound B) one := by
  simp only [two, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOrdinalOne_iff, Project.Formula.satisfies_isSuccessor_iff,
    Project.Term.eval_bound]
  rfl

/-- Parameters in the encoded source body are D,I,K,B,omega. -/
def parameters : Fin 5 → Fin 5 := Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Source.SetLanguage.args2 0 1)))

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 3 (.existsE (.conj (Project.Formula.isOmega (.bound 0))
    (.existsE (.conj (two (0 : Fin 5)) (ProjectSyntax.encode parameters ForcingProductFamily.constructionBody)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, two_freeClosed, ProjectSyntax.freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff, two_semantics,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), Project.Term.eval_bound]
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨w, hw⟩ := SetTheory.ZF.exists_omega hZF
  obtain ⟨one, hone⟩ := SetTheory.KP.exists_ordinalOne (SetTheory.ZF.modelsKP hZF)
  obtain ⟨B, hB⟩ := SetTheory.KP.exists_successor (SetTheory.ZF.modelsKP hZF) one
  refine ⟨w, hw, B, ⟨one, hone, hB⟩, ?_⟩
  exact (GodelDefOutput.close_semantics _ _).mp
    ((Translation.realizes_sentence M _).mp (ForcingProductFamily.construction_models hM)) _

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ForcingProductParameters
