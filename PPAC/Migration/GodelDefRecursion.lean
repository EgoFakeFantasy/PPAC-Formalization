/- Internal zero/successor/limit recursion for the pinned original Godel Def
output formula. Consumes the existing native three-branch recursion theorem;
no new recursion kernel, external ordinal recursion or Choice axiom. -/
import PPAC.Migration.GodelDefOutput
import PPAC.Migration.ProjectSyntax
import YesMetaZFC.SetTheory.Ord.Arithmetic.Recursion

namespace PPAC.Migration.GodelDefRecursion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Bridge the already existing encoders; both satisfaction relations are reused. -/
theorem encode_semantics {N : SetTheory.Structure.{u}} (hExt : SetTheory.Extensional N)
    {n m : Nat} (p : Source.Formula n) (r : Fin n → Fin m) (env : SetTheory.Env N m) :
    Project.Formula.satisfies env (ProjectSyntax.encode r p) ↔
      Source.Formula.Realize N.mem (fun i => env.bound (r i)) p := by
  induction p generalizing m with
  | bot => simp only [ProjectSyntax.encode, Project.Formula.satisfies_falsum_iff, Source.Formula.Realize]
  | mem => simp only [ProjectSyntax.encode, Project.Formula.satisfies_mem_iff, Project.Term.eval_bound, Source.Formula.Realize]
  | equal => exact Project.Formula.satisfies_extensionalEq_iff_eq hExt _ _ _
  | imp p q hp hq =>
      simp only [ProjectSyntax.encode, Project.Formula.satisfies_imp_iff,
        Source.Formula.Realize, hp, hq]
  | conj p q hp hq =>
      simp only [ProjectSyntax.encode, Project.Formula.satisfies_conj_iff,
        Source.Formula.Realize, hp, hq]
  | disj p q hp hq =>
      simp only [ProjectSyntax.encode, Project.Formula.satisfies_disj_iff,
        Source.Formula.Realize, hp, hq]
  | all p hp =>
      simp only [ProjectSyntax.encode, Project.Formula.satisfies_forall_iff, Source.Formula.Realize]
      apply forall_congr'
      intro x
      have he : (fun i => (env.push x).bound (ProjectSyntax.lift r i)) =
          Fin.lastCases x (fun i => env.bound (r i)) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp only [ProjectSyntax.lift, SetTheory.Env.push, Fin.lastCases_last,
            Fin.lastCases_castSucc, Fin.cases_zero, Fin.cases_succ]
      simpa only [he] using hp (ProjectSyntax.lift r) (env.push x)
  | ex p hp =>
      simp only [ProjectSyntax.encode, Project.Formula.satisfies_exists_iff, Source.Formula.Realize]
      apply exists_congr
      intro x
      have he : (fun i => (env.push x).bound (ProjectSyntax.lift r i)) =
          Fin.lastCases x (fun i => env.bound (r i)) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp only [ProjectSyntax.lift, SetTheory.Env.push, Fin.lastCases_last,
            Fin.lastCases_castSucc, Fin.cases_zero, Fin.cases_succ]
      simpa only [he] using hp (ProjectSyntax.lift r) (env.push x)

/-- Original `(previous,fixed13,output)` to Source `(fixed13,previous,output)`. -/
def successorIndex : Fin 15 → Fin 15 :=
  Fin.lastCases (Fin.last 14)
    (fun i => Fin.cases (13 : Fin 15) (fun j : Fin 13 => j.castSucc.castSucc) i)

def successor : Project.BinarySchema 13 :=
  ProjectSyntax.binary (GodelDefOutput.output.rename successorIndex)

theorem successor_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (previous output : M.Carrier .set) :
    successor.denote env previous output ↔
      Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
        (Fin.lastCases output (Fin.cases previous (fun i : Fin 13 => env.bound i.rev)))
        GodelDefOutput.output := by
  unfold successor ProjectSyntax.binary ProjectSyntax.formula Project.BinarySchema.denote
  rw [encode_semantics (ModelTransfer.extensionality hM), DefinableMinimaChoice.realize_rename]
  have he : (fun i => ((env.push previous).push output).bound (successorIndex i).rev) =
      Fin.lastCases output (Fin.cases previous (fun i : Fin 13 => env.bound i.rev)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · simp only [successorIndex, Fin.lastCases_castSucc, Fin.cases_succ, Fin.rev_castSucc,
          SetTheory.Env.push, Fin.cases_succ]
  rw [he]

theorem successor_total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (previous : M.Carrier .set) :
    ∃ output, successor.denote env previous output ∧
      ∀ other, successor.denote env previous other → other = output := by
  obtain ⟨output, hOutput, hUnique⟩ := GodelDefOutput.exists_unique hM
    (Fin.cases previous (fun i : Fin 13 => env.bound i.rev))
  exact ⟨output, (successor_semantics hM env previous output).mpr hOutput,
    fun other hOther => hUnique other ((successor_semantics hM env previous other).mp hOther)⟩

/-- The existing native three-way recursion syntax, with this exact Def successor. -/
def operator : Project.BinarySchema 13 where
  body := .disj
    (.conj (Project.Formula.isZeroLengthSequence PureKuratowskiProject.convention (.bound 1))
      (Project.Formula.isEmpty (.bound 0)))
    (.disj (.existsE
      (.conj (Project.Formula.isSuccessorLengthSequenceWithLast
          PureKuratowskiProject.convention (.bound 2) Project.Term.newest)
        (Project.Formula.related successor (Definitional.TermVector.boundParameters 13 3)
          Project.Term.newest (.bound 1))))
      (Project.Formula.isLimitLengthSequenceWithUnion PureKuratowskiProject.convention (.bound 1) (.bound 0)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem operator_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (sequence output : M.Carrier .set) :
    operator.denote env sequence output ↔
      (Project.FirstOrderSemantics.reduct M).IsZeroSuccessorLimitStep
        (KuratowskiZF.interpretation hM)
        (fun initial => ∀ value, ¬ (Project.FirstOrderSemantics.reduct M).mem value initial)
        (successor.denote env) sequence output := by
  simp only [operator, Project.BinarySchema.denote, SetTheory.Structure.IsZeroSuccessorLimitStep,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isZeroLengthSequence_iff (KuratowskiZF.interpretation hM)
      (ModelTransfer.extensionality hM), Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isSuccessorLengthSequenceWithLast_iff (KuratowskiZF.interpretation hM)
      (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isLimitLengthSequenceWithUnion_iff (KuratowskiZF.interpretation hM)
      (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_related_iff, Definitional.TermVector.evalEnv_boundParameters_three,
    Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push,
    Project.Term.eval_bound_two_push, Definitional.Term.eval_newest]

/-- Both actual branch premises are discharged: empty exists uniquely and Def is total single-valued. -/
theorem operator_total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnTransfiniteSequences
      (KuratowskiZF.interpretation hM) (operator.denote env) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨empty, hEmpty⟩ := SetTheory.KP.exists_empty (SetTheory.ZF.modelsKP hZF)
  have hInitial : ∃ output, (∀ value, ¬ (Project.FirstOrderSemantics.reduct M).mem value output) ∧
      ∀ other, (∀ value, ¬ (Project.FirstOrderSemantics.reduct M).mem value other) → other = output := by
    refine ⟨empty, hEmpty, ?_⟩
    intro other hOther
    exact (ModelTransfer.extensionality hM).eq_of_same_members other empty
      (fun value => ⟨fun h => False.elim (hOther value h), fun h => False.elim (hEmpty value h)⟩)
  have hStep := SetTheory.ZF.zeroSuccessorLimitStep_isClassFunctionOnTransfiniteSequences
    hZF (KuratowskiZF.interpretation hM) _ (successor.denote env) hInitial (successor_total_unique hM env)
  intro sequence hSequence
  obtain ⟨output, hOutput, hUnique⟩ := hStep sequence hSequence
  exact ⟨output, (operator_semantics hM env sequence output).mpr hOutput,
    fun other hOther => hUnique other ((operator_semantics hM env sequence other).mp hOther)⟩

/-- Set-coded histories in the existing internal recursion, not host ordinal recursion. -/
def hierarchy : Project.BinarySchema 13 :=
  operator.transfiniteRecursion PureKuratowskiProject.convention

/-- The output relation contains an internal set-coded history and the actual three-way final step. -/
theorem hierarchy_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13)
    (index value : M.Carrier .set) :
    hierarchy.denote env index value ↔
      ∃ sequence,
        (Project.FirstOrderSemantics.reduct M).IsRecursiveSequence
          (KuratowskiZF.interpretation hM) (operator.denote env) sequence index ∧
        (Project.FirstOrderSemantics.reduct M).IsZeroSuccessorLimitStep
          (KuratowskiZF.interpretation hM)
          (fun initial => ∀ element, ¬ (Project.FirstOrderSemantics.reduct M).mem element initial)
          (successor.denote env) sequence value := by
  rw [hierarchy, Project.Formula.denote_transfiniteRecursion_iff
    (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)]
  change (∃ sequence, _ ∧ operator.denote env sequence value) ↔ _
  exact exists_congr (fun sequence => and_congr_right (fun _ => operator_semantics hM env sequence value))

theorem hierarchy_total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnOrdinals (hierarchy.denote env) :=
  SetTheory.ZF.transfiniteRecursion_isClassFunctionOnOrdinals
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    env operator (operator_total_unique hM env)

/-- For every fixed parameter tuple, all internal ordinals have unique hierarchy values. -/
def hierarchySentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (Project.Formula.isClassFunctionOnOrdinals hierarchy (Definitional.TermVector.boundParameters 13 0))
  freeClosed := by simp

theorem hierarchy_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence hierarchySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) hierarchySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  rw [Project.Formula.satisfies_isClassFunctionOnOrdinals_iff (ModelTransfer.extensionality hM),
    Definitional.TermVector.evalEnv_boundParameters_zero]
  exact hierarchy_total_unique hM ⟨bound, free⟩

theorem hierarchy_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence hierarchySentence) :=
  ModelTransfer.derives (fun _ hM => hierarchy_models hM)

end PPAC.Migration.GodelDefRecursion
