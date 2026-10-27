/- Pinned ConstructionIteration / Round.underFunctor: ONE actual pure
binary history operator, total/unique on ALL internal histories. Valid
in-range histories execute the real source case; all other histories take
one explicit zero default. Instantiate the existing native ordinal
recursor with THIS operator, not a supplied arbitrary function/sequence. -/
import PPAC.Migration.ConstructionTowerIterationCases

namespace PPAC.Migration.ConstructionTowerIteration
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerValidity (Valid)
open ConstructionTowerIterationCases (Context Case)
open ConstructionTowerHistoryClosure (Continues)
open ForcingConditionGraphs (FunctionOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u lengthBound Schedule S J output : M.Carrier .set}

def Good (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C lengthBound S J : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOrdinal J ∧
  (Project.FirstOrderSemantics.reduct M).mem J lengthBound ∧
  Valid hM w Q R top D mul e mark H C J S

def Operation (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one lengthBound Schedule S output : M.Carrier .set) : Prop :=
  (∃ J, Good hM w Q R top D mul e mark H C lengthBound S J ∧
    Case hM w Q R top D mul e mark H C zero one Schedule J S output) ∨
  (¬ (∃ J, Good hM w Q R top D mul e mark H C lengthBound S J)) ∧ output = zero

/-- Exact domain equality of the SAME actual set-function graph. -/
theorem length_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J K S : M.Carrier .set} (hJ : FunctionOn J S) (hK : FunctionOn K S) : J = K := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro i
  constructor
  · intro hi
    obtain ⟨v,hv,_⟩ := hJ.2 i hi
    exact ForcingConditionGraphs.function_input hK hv
  · intro hi
    obtain ⟨v,hv,_⟩ := hK.2 i hi
    exact ForcingConditionGraphs.function_input hJ hv

theorem total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (S : M.Carrier .set) :
    ∃ output, Operation hM w Q R top D mul e mark H C zero one lengthBound Schedule S output ∧
      ∀ other, Operation hM w Q R top D mul e mark H C zero one lengthBound Schedule S other → other = output := by
  classical
  by_cases hGood : ∃ J, Good hM w Q R top D mul e mark H C lengthBound S J
  · obtain ⟨J,hJ,hBound,hV⟩ := hGood
    obtain ⟨out,hCase⟩ := ConstructionTowerIterationCases.case_exists hM hOrder hCtx hJ hBound hV
    refine ⟨out,Or.inl ⟨J,⟨hJ,hBound,hV⟩,hCase⟩,?_⟩
    intro other hOther
    rcases hOther with ⟨K,hK,hCase'⟩ | ⟨hn,_⟩
    · have ek := length_unique hM hK.2.2.1.1 hV.1.1
      subst K
      exact ConstructionTowerIterationCases.case_unique hM hOrder hCtx hJ hV hCase' hCase
    · exact False.elim (hn ⟨J,hJ,hBound,hV⟩)
  · refine ⟨zero,Or.inr ⟨hGood,rfl⟩,?_⟩
    intro other hOther
    rcases hOther with ⟨J,hJ,_⟩ | ⟨_,he⟩
    · exact False.elim (hGood ⟨J,hJ⟩)
    · exact he

theorem valid_step (hM : FirstOrder.Theory.Models M nativeZF)
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    (hGood : Good hM w Q R top D mul e mark H C lengthBound S J)
    (hOp : Operation hM w Q R top D mul e mark H C zero one lengthBound Schedule S output) :
    Case hM w Q R top D mul e mark H C zero one Schedule J S output ∧
    Continues hM w Q R top D mul e mark H C J S output := by
  rcases hOp with ⟨K,hK,hCase⟩ | ⟨hn,_⟩
  · have ek := length_unique hM hK.2.2.1.1 hGood.2.2.1.1
    subst K
    exact ⟨hCase,ConstructionTowerIterationCases.case_continues hM hCtx hGood.1 hGood.2.2 hCase⟩
  · exact False.elim (hn ⟨J,hGood⟩)


def good {m : Nat} (w Q R top D mul e mark H C lengthBound S J : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isOrdinal (.bound J)) (.conj (.mem (.bound J) (.bound lengthBound))
  (ConstructionTowerValidity.valid w Q R top D mul e mark H C J S)))

theorem good_freeClosed {m : Nat} (w Q R top D mul e mark H C lengthBound S J : Fin m) :
    (good w Q R top D mul e mark H C lengthBound S J).FreeClosed := by
  simp -implicitDefEqProofs [good,Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionTowerValidity.valid_freeClosed]

theorem good_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C lengthBound S J : Fin m) :
    Project.Formula.satisfies env (good w Q R top D mul e mark H C lengthBound S J) ↔ Good hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound lengthBound) (env.bound S) (env.bound J) := by
  simp only [good,Good,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionTowerValidity.valid_semantics hM]


def operation {m : Nat} (w Q R top D mul e mark H C zero one lengthBound Schedule S output : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.conj (good w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ
  lengthBound.succ S.succ (0 : Fin (m+1))) (ConstructionTowerIterationCases.caseValue w.succ Q.succ R.succ
  top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ Schedule.succ (0 : Fin (m+1))
  S.succ output.succ))) (.conj (.neg (.existsE (good w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ
  mark.succ H.succ C.succ lengthBound.succ S.succ (0 : Fin (m+1))))) (Project.Formula.extensionalEq (.bound
  output) (.bound zero))))

theorem operation_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one lengthBound Schedule S output : Fin m) :
    (operation w Q R top D mul e mark H C zero one lengthBound Schedule S output).FreeClosed := by
  simp -implicitDefEqProofs [operation,Definitional.Formula.FreeClosed,good_freeClosed,ConstructionTowerIterationCases.caseValue_freeClosed,Project.Formula.extensionalEq]

theorem operation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one lengthBound Schedule S output : Fin m) :
    Project.Formula.satisfies env (operation w Q R top D mul e mark H C zero one lengthBound Schedule S output) ↔ Operation hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound lengthBound) (env.bound Schedule) (env.bound S) (env.bound output) := by
  simp only [operation,Operation,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,good_semantics hM,ConstructionTowerIterationCases.caseValue_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def operatorSchema : Project.BinarySchema 14 where
  body := operation 2 3 4 5 6 7 8 9 10 11 12 13 14 15 1 0
  freeClosed := operation_freeClosed ..

def operatorEnv (w Q R top D mul e mark H C zero one lengthBound Schedule : M.Carrier .set) :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 14 where
  bound := Fin.cases w ( Fin.cases Q ( Fin.cases R ( Fin.cases top ( Fin.cases D ( Fin.cases mul ( Fin.cases e ( Fin.cases mark ( Fin.cases H ( Fin.cases C ( Fin.cases zero ( Fin.cases one ( Fin.cases lengthBound (fun _ => Schedule)))))))))))))
  free := fun _ => zero

theorem schema_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one lengthBound Schedule S output : M.Carrier .set) :
    operatorSchema.denote (operatorEnv w Q R top D mul e mark H C zero one lengthBound Schedule) S output ↔
      Operation hM w Q R top D mul e mark H C zero one lengthBound Schedule S output :=
  operation_semantics hM (((operatorEnv w Q R top D mul e mark H C zero one lengthBound Schedule).push S).push output)
    2 3 4 5 6 7 8 9 10 11 12 13 14 15 1 0

theorem class_function (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnTransfiniteSequences
      (KuratowskiZF.interpretation hM)
      (operatorSchema.denote (operatorEnv w Q R top D mul e mark H C zero one lengthBound Schedule)) := by
  intro history _
  obtain ⟨out,hOp,hUnique⟩ := total_unique hM hOrder hCtx history
  exact ⟨out,(schema_semantics hM w Q R top D mul e mark H C zero one lengthBound Schedule history out).mpr hOp,
    fun other hOther => hUnique other ((schema_semantics hM w Q R top D mul e mark H C zero one lengthBound Schedule history other).mp hOther)⟩

def Recursive (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one lengthBound Schedule length history : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsRecursiveSequence (KuratowskiZF.interpretation hM)
    (Operation hM w Q R top D mul e mark H C zero one lengthBound Schedule) history length

theorem recursive_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u lengthBound Schedule)
    {length : M.Carrier .set} (hLength : (Project.FirstOrderSemantics.reduct M).IsOrdinal length) :
    ∃ history, Recursive hM w Q R top D mul e mark H C zero one lengthBound Schedule length history := by
  obtain ⟨history,hSequence,hRecursion⟩ := ZF.recursiveSequence_exists
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (operatorEnv w Q R top D mul e mark H C zero one lengthBound Schedule) operatorSchema (class_function hM hOrder hCtx) hLength
  refine ⟨history,hSequence,?_⟩
  intro index hi value hv
  obtain ⟨restriction,hr,hop⟩ := hRecursion index hi value hv
  exact ⟨restriction,hr,(schema_semantics hM w Q R top D mul e mark H C zero one lengthBound Schedule restriction value).mp hop⟩


def recursive {m : Nat} (w Q R top D mul e mark H C zero one lengthBound Schedule length history : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isSequenceOfLength PureKuratowskiProject.convention (.bound history) (.bound
  length)) (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound length.succ)) (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge history.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (.existsE (.conj (Project.Formula.isRestriction PureKuratowskiProject.convention (.bound (0 : Fin (m+3)))
  (.bound history.succ.succ.succ) (.bound (2 : Fin (m+3)))) (operation w.succ.succ.succ Q.succ.succ.succ
  R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  lengthBound.succ.succ.succ Schedule.succ.succ.succ (0 : Fin (m+3)) (1 : Fin (m+3))))))))))

theorem recursive_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one lengthBound Schedule length history : Fin m) :
    (recursive w Q R top D mul e mark H C zero one lengthBound Schedule length history).FreeClosed := by
  simp -implicitDefEqProofs [recursive,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSequenceOfLength_freeClosed,Project.Formula.isRestriction_freeClosed,operation_freeClosed]

theorem recursive_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one lengthBound Schedule length history : Fin m) :
    Project.Formula.satisfies env (recursive w Q R top D mul e mark H C zero one lengthBound Schedule length history) ↔ Recursive hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound lengthBound) (env.bound Schedule) (env.bound length) (env.bound history) := by
  simp only [recursive,Recursive,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isSequenceOfLength_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isRestriction_iff (KuratowskiZF.interpretation hM),operation_semantics hM,Structure.IsRecursiveSequence,Structure.ObeysRecursion]
  rfl


def totalSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 16 (.imp (ConstructionTowerIterationCases.context (0 : Fin 16) (1 : Fin 16)
    (2 : Fin 16) (3 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6 : Fin 16) (7 : Fin 16) (8 : Fin 16) (9 : Fin 16)
    (10 : Fin 16) (11 : Fin 16) (12 : Fin 16) (13 : Fin 16) (14 : Fin 16)) (.existsE (.conj (operation (0 :
    Fin 16).succ (1 : Fin 16).succ (2 : Fin 16).succ (3 : Fin 16).succ (4 : Fin 16).succ (5 : Fin 16).succ
    (6 : Fin 16).succ (7 : Fin 16).succ (8 : Fin 16).succ (9 : Fin 16).succ (10 : Fin 16).succ (11 : Fin
    16).succ (13 : Fin 16).succ (14 : Fin 16).succ (15 : Fin 16).succ (0 : Fin 17)) (.forallE (.imp
    (operation (0 : Fin 16).succ.succ (1 : Fin 16).succ.succ (2 : Fin 16).succ.succ (3 : Fin 16).succ.succ
    (4 : Fin 16).succ.succ (5 : Fin 16).succ.succ (6 : Fin 16).succ.succ (7 : Fin 16).succ.succ (8 : Fin
    16).succ.succ (9 : Fin 16).succ.succ (10 : Fin 16).succ.succ (11 : Fin 16).succ.succ (13 : Fin
    16).succ.succ (14 : Fin 16).succ.succ (15 : Fin 16).succ.succ (0 : Fin 18))
    (Project.Formula.extensionalEq (.bound (0 : Fin 18)) (.bound (1 : Fin 18)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerIterationCases.context_freeClosed,operation_freeClosed,Project.Formula.extensionalEq]

theorem total_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence totalSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) totalSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,operation_semantics hM]
  exact fun hCtx => total_unique hM hOrder hCtx (bound 15)

theorem total_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative totalSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM totalSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) totalSentence).mp
    (total_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

def stepSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 18 (.imp (ConstructionTowerIterationCases.context (0 : Fin 18) (1 : Fin 18)
    (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18)
    (10 : Fin 18) (11 : Fin 18) (12 : Fin 18) (13 : Fin 18) (14 : Fin 18)) (.imp (good (0 : Fin 18) (1 : Fin
    18) (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin
    18) (13 : Fin 18) (15 : Fin 18) (16 : Fin 18)) (.imp (operation (0 : Fin 18) (1 : Fin 18) (2 : Fin 18)
    (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (10 : Fin 18)
    (11 : Fin 18) (13 : Fin 18) (14 : Fin 18) (15 : Fin 18) (17 : Fin 18)) (.conj
    (ConstructionTowerIterationCases.caseValue (0 : Fin 18) (1 : Fin 18) (2 : Fin 18) (3 : Fin 18) (4 : Fin
    18) (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (10 : Fin 18) (11 : Fin 18) (14 :
    Fin 18) (16 : Fin 18) (15 : Fin 18) (17 : Fin 18)) (ConstructionTowerHistoryClosure.continues (0 : Fin
    18) (1 : Fin 18) (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 : Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin
    18) (9 : Fin 18) (16 : Fin 18) (15 : Fin 18) (17 : Fin 18)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerIterationCases.context_freeClosed,good_freeClosed,operation_freeClosed,ConstructionTowerIterationCases.caseValue_freeClosed,ConstructionTowerHistoryClosure.continues_freeClosed]

theorem step_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence stepSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) stepSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    ConstructionTowerIterationCases.context_semantics hM,good_semantics hM,operation_semantics hM,
    ConstructionTowerIterationCases.caseValue_semantics hM,ConstructionTowerHistoryClosure.continues_semantics hM]
  exact fun hCtx hGood hOp => valid_step hM hCtx hGood hOp

theorem step_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence stepSentence) := ModelTransfer.derives (fun _ hM => step_models hM)

def recursionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 16 (.imp (ConstructionTowerIterationCases.context (0 : Fin 16) (1 : Fin 16)
    (2 : Fin 16) (3 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6 : Fin 16) (7 : Fin 16) (8 : Fin 16) (9 : Fin 16)
    (10 : Fin 16) (11 : Fin 16) (12 : Fin 16) (13 : Fin 16) (14 : Fin 16)) (.imp (Project.Formula.isOrdinal
    (.bound (15 : Fin 16))) (.existsE (recursive (0 : Fin 16).succ (1 : Fin 16).succ (2 : Fin 16).succ (3 :
    Fin 16).succ (4 : Fin 16).succ (5 : Fin 16).succ (6 : Fin 16).succ (7 : Fin 16).succ (8 : Fin 16).succ
    (9 : Fin 16).succ (10 : Fin 16).succ (11 : Fin 16).succ (13 : Fin 16).succ (14 : Fin 16).succ (15 : Fin
    16).succ (0 : Fin 17))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerIterationCases.context_freeClosed,Project.Formula.isOrdinal,recursive_freeClosed]

theorem recursion_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence recursionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) recursionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,recursive_semantics hM]
  exact fun hCtx hLength => recursive_exists hM hOrder hCtx hLength

theorem recursion_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative recursionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM recursionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) recursionSentence).mp
    (recursion_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionTowerIteration
