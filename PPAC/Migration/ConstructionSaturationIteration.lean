/- Pinned CompleteRounds.Saturation.tower / ConstructionIteration.
The actual outer history operator, with the EXISTING initial/limit and the
trace-bearing complete-round successor. It is total and unique on ALL
internal set histories. Instantiate the original native ordinal recursor;
no host well-foundedness and no arbitrary supplied step/tower. -/
import PPAC.Migration.ConstructionSaturationIterationCases

namespace PPAC.Migration.ConstructionSaturationIteration
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSaturationIterationCases (Context Case)
open ConstructionTowerValidity (Valid)
open ConstructionTowerCardinality (AllSmall)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C zero one u K mu lengthBound S J output length history : M.Carrier .set}

def Good (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C mu lengthBound S J : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsOrdinal J ∧
  (Project.FirstOrderSemantics.reduct M).mem J lengthBound ∧
  Valid hM w Q R top D mul e mark H C J S ∧ AllSmall J S mu

def Operation (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu lengthBound S output : M.Carrier .set) : Prop :=
  (∃ J, Good hM w Q R top D mul e mark H C mu lengthBound S J ∧
    Case hM w Q R top D mul e mark H C zero one K mu J S output) ∨
  (¬ (∃ J, Good hM w Q R top D mul e mark H C mu lengthBound S J)) ∧ output = zero

theorem total_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    (S : M.Carrier .set) :
    ∃ output, Operation hM w Q R top D mul e mark H C zero one K mu lengthBound S output ∧
      ∀ other, Operation hM w Q R top D mul e mark H C zero one K mu lengthBound S other → other = output := by
  classical
  by_cases hGood : ∃ J, Good hM w Q R top D mul e mark H C mu lengthBound S J
  · obtain ⟨J,hJ,hBound,hV,hSmall⟩ := hGood
    obtain ⟨out,hCase⟩ := ConstructionSaturationIterationCases.case_exists hM hOrder hChoice hCtx hJ hV hSmall
    refine ⟨out,Or.inl ⟨J,⟨hJ,hBound,hV,hSmall⟩,hCase⟩,?_⟩
    intro other hOther
    rcases hOther with ⟨L,hL,hCase'⟩ | ⟨hn,_⟩
    · have hLV := hL.2.2.1
      have eq := ConstructionTowerIteration.length_unique hM hLV.1.1 hV.1.1
      subst L
      have hCtxCopy := hCtx
      obtain ⟨_,_,_,_,_,_,_,hz,_⟩ := hCtxCopy
      exact ConstructionSaturationIterationCases.case_unique hM hOrder hJ hz hV hCase' hCase
    · exact False.elim (hn ⟨J,hJ,hBound,hV,hSmall⟩)
  · refine ⟨zero,Or.inr ⟨hGood,rfl⟩,?_⟩
    intro other hOther
    rcases hOther with ⟨J,hJ,_⟩ | ⟨_,he⟩
    · exact False.elim (hGood ⟨J,hJ⟩)
    · exact he

theorem valid_step (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    (hGood : Good hM w Q R top D mul e mark H C mu lengthBound S J)
    (hOp : Operation hM w Q R top D mul e mark H C zero one K mu lengthBound S output) :
    Case hM w Q R top D mul e mark H C zero one K mu J S output ∧
      ∃ next S', ConstructionTowerAppend.Append J S output next S' ∧
        Valid hM w Q R top D mul e mark H C next S' ∧ AllSmall next S' mu := by
  rcases hOp with ⟨L,hL,hCase⟩ | ⟨hn,_⟩
  · have hLV := hL.2.2.1
    have hJV := hGood.2.2.1
    have eq := ConstructionTowerIteration.length_unique hM hLV.1.1 hJV.1.1
    subst L
    exact ⟨hCase,ConstructionSaturationIterationCases.case_continues hM hOrder hChoice hCtx
      hGood.1 hGood.2.1 hGood.2.2.1 hGood.2.2.2 hCase⟩
  · exact False.elim (hn ⟨J,hGood⟩)

def good {m : Nat} (w Q R top D mul e mark H C mu lengthBound S J : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isOrdinal (.bound J)) (.conj (.mem (.bound J) (.bound lengthBound)) (.conj
  (ConstructionTowerValidity.valid w Q R top D mul e mark H C J S) (ConstructionTowerCardinality.allSmall J
  S mu))))

theorem good_freeClosed {m : Nat} (w Q R top D mul e mark H C mu lengthBound S J : Fin m) :
    (good w Q R top D mul e mark H C mu lengthBound S J).FreeClosed := by
  simp -implicitDefEqProofs [good,Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerCardinality.allSmall_freeClosed]

theorem good_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C mu lengthBound S J : Fin m) :
    Project.Formula.satisfies env (good w Q R top D mul e mark H C mu lengthBound S J) ↔ Good hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound mu) (env.bound lengthBound) (env.bound S) (env.bound J) := by
  simp only [good,Good,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM]


def operation {m : Nat} (w Q R top D mul e mark H C zero one K mu lengthBound S output : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.conj (good w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ
  mu.succ lengthBound.succ S.succ (0 : Fin (m+1))) (ConstructionSaturationIterationCases.caseValue w.succ
  Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ K.succ mu.succ (0
  : Fin (m+1)) S.succ output.succ))) (.conj (.neg (.existsE (good w.succ Q.succ R.succ top.succ D.succ
  mul.succ e.succ mark.succ H.succ C.succ mu.succ lengthBound.succ S.succ (0 : Fin (m+1)))))
  (Project.Formula.extensionalEq (.bound output) (.bound zero))))

theorem operation_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu lengthBound S output : Fin m) :
    (operation w Q R top D mul e mark H C zero one K mu lengthBound S output).FreeClosed := by
  simp -implicitDefEqProofs [operation,Definitional.Formula.FreeClosed,good_freeClosed,ConstructionSaturationIterationCases.caseValue_freeClosed,Project.Formula.extensionalEq]

theorem operation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu lengthBound S output : Fin m) :
    Project.Formula.satisfies env (operation w Q R top D mul e mark H C zero one K mu lengthBound S output) ↔ Operation hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound lengthBound) (env.bound S) (env.bound output) := by
  simp only [operation,Operation,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_disj_iff,good_semantics hM,ConstructionSaturationIterationCases.caseValue_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def operatorSchema : Project.BinarySchema 15 where
  body := operation 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 1 0
  freeClosed := operation_freeClosed ..

def operatorEnv (w Q R top D mul e mark H C zero one K mu lengthBound : M.Carrier .set) :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 15 where
  bound := fun i => match i.val with
    | 0 => w
    | 1 => Q
    | 2 => R
    | 3 => top
    | 4 => D
    | 5 => mul
    | 6 => e
    | 7 => mark
    | 8 => H
    | 9 => C
    | 10 => zero
    | 11 => one
    | 12 => K
    | 13 => mu
    | _ => lengthBound
  free := fun _ => zero


theorem schema_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu lengthBound S output : M.Carrier .set) :
    operatorSchema.denote (operatorEnv w Q R top D mul e mark H C zero one K mu lengthBound) S output ↔
      Operation hM w Q R top D mul e mark H C zero one K mu lengthBound S output :=
  operation_semantics hM (((operatorEnv w Q R top D mul e mark H C zero one K mu lengthBound).push S).push output)
    2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 1 0

theorem class_function (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound) :
    (Project.FirstOrderSemantics.reduct M).IsClassFunctionOnTransfiniteSequences
      (KuratowskiZF.interpretation hM)
      (operatorSchema.denote (operatorEnv w Q R top D mul e mark H C zero one K mu lengthBound)) := by
  intro history _
  obtain ⟨out,hOp,hUnique⟩ := total_unique hM hOrder hChoice hCtx history
  exact ⟨out,(schema_semantics hM w Q R top D mul e mark H C zero one K mu lengthBound history out).mpr hOp,
    fun other hOther => hUnique other ((schema_semantics hM w Q R top D mul e mark H C zero one K mu lengthBound history other).mp hOther)⟩

def Recursive (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu lengthBound length history : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).IsRecursiveSequence (KuratowskiZF.interpretation hM)
    (Operation hM w Q R top D mul e mark H C zero one K mu lengthBound) history length

theorem recursive_exists (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (hCtx : Context hM w Q R top D mul e mark H C zero one u K mu lengthBound)
    {length : M.Carrier .set} (hLength : (Project.FirstOrderSemantics.reduct M).IsOrdinal length) :
    ∃ history, Recursive hM w Q R top D mul e mark H C zero one K mu lengthBound length history := by
  obtain ⟨history,hSequence,hRecursion⟩ := ZF.recursiveSequence_exists
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (operatorEnv w Q R top D mul e mark H C zero one K mu lengthBound) operatorSchema (class_function hM hOrder hChoice hCtx) hLength
  refine ⟨history,hSequence,?_⟩
  intro index hi value hv
  obtain ⟨restriction,hr,hop⟩ := hRecursion index hi value hv
  exact ⟨restriction,hr,(schema_semantics hM w Q R top D mul e mark H C zero one K mu lengthBound restriction value).mp hop⟩



def recursive {m : Nat} (w Q R top D mul e mark H C zero one K mu lengthBound length history : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.isSequenceOfLength PureKuratowskiProject.convention (.bound history) (.bound
  length)) (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound length.succ)) (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge history.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (.existsE (.conj (Project.Formula.isRestriction PureKuratowskiProject.convention (.bound (0 : Fin (m+3)))
  (.bound history.succ.succ.succ) (.bound (2 : Fin (m+3)))) (operation w.succ.succ.succ Q.succ.succ.succ
  R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ lengthBound.succ.succ.succ (0 : Fin (m+3)) (1 : Fin (m+3))))))))))

theorem recursive_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu lengthBound length history : Fin m) :
    (recursive w Q R top D mul e mark H C zero one K mu lengthBound length history).FreeClosed := by
  simp -implicitDefEqProofs [recursive,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSequenceOfLength_freeClosed,Project.Formula.isRestriction_freeClosed,operation_freeClosed]

theorem recursive_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu lengthBound length history : Fin m) :
    Project.Formula.satisfies env (recursive w Q R top D mul e mark H C zero one K mu lengthBound length history) ↔ Recursive hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound lengthBound) (env.bound length) (env.bound history) := by
  simp only [recursive,Recursive,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_isSequenceOfLength_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_isRestriction_iff (KuratowskiZF.interpretation hM),operation_semantics hM,Structure.IsRecursiveSequence,Structure.ObeysRecursion]
  rfl



def totalSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 17 (.imp (ConstructionSaturationIterationCases.context (0 : Fin 17) (1 : Fin
    17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin
    17) (10 : Fin 17) (11 : Fin 17) (12 : Fin 17) (13 : Fin 17) (14 : Fin 17) (15 : Fin 17)) (.existsE
    (.conj (operation (0 : Fin 17).succ (1 : Fin 17).succ (2 : Fin 17).succ (3 : Fin 17).succ (4 : Fin
    17).succ (5 : Fin 17).succ (6 : Fin 17).succ (7 : Fin 17).succ (8 : Fin 17).succ (9 : Fin 17).succ (10 :
    Fin 17).succ (11 : Fin 17).succ (13 : Fin 17).succ (14 : Fin 17).succ (15 : Fin 17).succ (16 : Fin
    17).succ (0 : Fin 18)) (.forallE (.imp (operation (0 : Fin 17).succ.succ (1 : Fin 17).succ.succ (2 : Fin
    17).succ.succ (3 : Fin 17).succ.succ (4 : Fin 17).succ.succ (5 : Fin 17).succ.succ (6 : Fin
    17).succ.succ (7 : Fin 17).succ.succ (8 : Fin 17).succ.succ (9 : Fin 17).succ.succ (10 : Fin
    17).succ.succ (11 : Fin 17).succ.succ (13 : Fin 17).succ.succ (14 : Fin 17).succ.succ (15 : Fin
    17).succ.succ (16 : Fin 17).succ.succ (0 : Fin 19)) (Project.Formula.extensionalEq (.bound (0 : Fin 19))
    (.bound (1 : Fin 19)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,operation_freeClosed,Project.Formula.extensionalEq]

theorem total_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence totalSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) totalSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    ConstructionSaturationIterationCases.context_semantics hM,operation_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  exact fun hCtx => total_unique hM hOrder hChoice hCtx (bound 16)

theorem total_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative totalSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM totalSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) totalSentence).mp
    (total_models hL (ConstructionRoundSelection.l_order hM) hChoice)



end PPAC.Migration.ConstructionSaturationIteration
