/- Object-language history, evaluation and exact pinned Raw.eval equations.
The native recursive-sequence schema is reused without adding a proof kernel. -/
import PPAC.Migration.ConstructionProbeEvaluation

namespace PPAC.Migration.ConstructionProbeEvaluationSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeEvaluation ConstructionProbeRaw
open ConstructionProbeRawAction (OldAct)
open ConstructionProbeLetterAction (LetterAct)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeWord (WordCarrier)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def history {m : Nat} (w D S zero mul A b W E f x input H n : Fin m) : Project.Formula 1 m :=
  Project.Formula.isRecursiveSequenceIn PureKuratowskiProject.convention
    (stepSchema w D S zero mul A b W E f x input)
    (Definitional.TermVector.boundParameters m 0) (.bound H) (.bound n) (.bound W)

theorem history_freeClosed {m : Nat} (w D S zero mul A b W E f x input H n : Fin m) :
    (history w D S zero mul A b W E f x input H n).FreeClosed := by
  apply Project.Formula.isRecursiveSequenceIn_freeClosed
  all_goals simp

theorem history_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D S zero mul A b W E f x input H n : Fin m) :
    Project.Formula.satisfies env (history w D S zero mul A b W E f x input H n) ↔
      History hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E)
        (env.bound f) (env.bound x) (env.bound input) (env.bound H) (env.bound n) := by
  rw [history,Project.Formula.satisfies_isRecursiveSequenceIn_iff
    (KuratowskiZF.interpretation hM) (ModelTransfer.project_models_iff.mp hM).1,
    Definitional.TermVector.evalEnv_boundParameters_zero]
  have he : (stepSchema w D S zero mul A b W E f x input).denote env =
      Step (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound f) (env.bound x) (env.bound input) := by
    funext H y
    exact propext (stepSchema_semantics hM env w D S zero mul A b W E f x input H y)
  rw [he]
  rfl

def eval {m : Nat} (w D S zero mul A b W E q input y : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound input) (.bound W)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (.mem (.bound 4) (.bound w.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 3) (.bound
    w.succ.succ.succ.succ.succ)) (.conj (Project.Formula.isSuccessor (.bound 3) (.bound 4)) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 4 S.succ.succ.succ.succ.succ)) (.conj
    (.mem (.bound 1) (.bound D.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
    (PairSyntax.ordered q.succ.succ.succ.succ.succ 2 1)) (.conj (history w.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ
    W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ 2 1 input.succ.succ.succ.succ.succ 0 3)
    (ProjectSyntax.encode id (Source.SetLanguage.edge 0 4 y.succ.succ.succ.succ.succ)))))))))))))))

theorem eval_freeClosed {m : Nat} (w D S zero mul A b W E q input y : Fin m) :
    (eval w D S zero mul A b W E q input y).FreeClosed := by
  simp -implicitDefEqProofs [eval,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    history_freeClosed,Project.Formula.isSuccessor,Project.Formula.extensionalEq_freeClosed_iff]

theorem eval_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (w D S zero mul A b W E q input y : Fin m) :
    Project.Formula.satisfies env (eval w D S zero mul A b W E q input y) ↔
      Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) (env.bound input) (env.bound y) := by
  simp only [eval,Eval,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_code,KuratowskiZF.source_edge,
    history_semantics hM]
  rfl

def EvalLaws (hM : FirstOrder.Theory.Models M nativeZF)
    (w D S zero mul A b W E : M.Carrier .set) : Prop :=
  (∀ q input, Raw w D S q → (Project.FirstOrderSemantics.reduct M).mem input W →
    ∃ y, Eval hM w D S zero mul A b W E q input y) ∧
  (∀ q input y, Eval hM w D S zero mul A b W E q input y →
    (Project.FirstOrderSemantics.reduct M).mem y W) ∧
  (∀ q input y z, Eval hM w D S zero mul A b W E q input y →
    Eval hM w D S zero mul A b W E q input z → y = z) ∧
  (∀ x q input y, Old zero D x q → (Project.FirstOrderSemantics.reduct M).mem input W →
    (Eval hM w D S zero mul A b W E q input y ↔ OldAct w D S zero mul A x input y)) ∧
  (∀ s t q input y, Cons w D S s t q →
    (Eval hM w D S zero mul A b W E q input y ↔
      ∃ v, Eval hM w D S zero mul A b W E t input v ∧ LetterAct w D S zero mul A b W E s v y))

theorem eval_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D) :
    EvalLaws hM w D S zero mul A b W E := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun q input hq hi => eval_total hM hw hz hzw hm hAlpha hW hb hq hi
  · exact fun q input y hy => eval_word hM hy
  · exact fun q input y z hy hzv => eval_unique hM hw hz hzw hm hAlpha hW hb hy hzv
  · exact fun x q input y hq hi => eval_old_iff hM hw hz hzw hm hAlpha hW hb hq hi
  · exact fun s t q input y hq => eval_cons_iff hM hw hz hzw hm hAlpha hW hb hq

def evalLaws {m : Nat} (w D S zero mul A b W E : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (raw w.succ.succ D.succ.succ S.succ.succ 1) (.imp (.mem (.bound
    0) (.bound W.succ.succ)) (.existsE (eval w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ
    zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ W.succ.succ.succ
    E.succ.succ.succ 2 1 0)))))) (.conj (.forallE (.forallE (.forallE (.imp (eval w.succ.succ.succ
    D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ
    b.succ.succ.succ W.succ.succ.succ E.succ.succ.succ 2 1 0) (.mem (.bound 0) (.bound
    W.succ.succ.succ)))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (eval
    w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ zero.succ.succ.succ.succ
    mul.succ.succ.succ.succ A.succ.succ.succ.succ b.succ.succ.succ.succ W.succ.succ.succ.succ
    E.succ.succ.succ.succ 3 2 1) (.imp (eval w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ
    b.succ.succ.succ.succ W.succ.succ.succ.succ E.succ.succ.succ.succ 3 2 0)
    (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))) (.conj (.forallE (.forallE (.forallE
    (.forallE (.imp (old zero.succ.succ.succ.succ D.succ.succ.succ.succ 3 2) (.imp (.mem (.bound 1)
    (.bound W.succ.succ.succ.succ)) (.iff (eval w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ
    b.succ.succ.succ.succ W.succ.succ.succ.succ E.succ.succ.succ.succ 2 1 0)
    (ConstructionProbeRawActionSyntax.oldAct w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ 3 1
    0)))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (cons
    w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ 4 3 2) (.iff
    (eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ
    b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ 2 1 0)
    (.existsE (.conj (eval w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ
    b.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ
    4 2 0) (ConstructionProbeLetterAction.letterAct w.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
    A.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ
    E.succ.succ.succ.succ.succ.succ 5 0 1))))))))))))))

theorem evalLaws_freeClosed {m : Nat} (w D S zero mul A b W E : Fin m) :
    (evalLaws w D S zero mul A b W E).FreeClosed := by
  simp -implicitDefEqProofs [evalLaws,Definitional.Formula.FreeClosed,eval_freeClosed,raw_freeClosed,
    old_freeClosed,cons_freeClosed,ConstructionProbeRawActionSyntax.oldAct_freeClosed,
    ConstructionProbeLetterAction.letterAct_freeClosed,Project.Formula.extensionalEq_freeClosed_iff]

theorem evalLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E : Fin m) :
    Project.Formula.satisfies env (evalLaws w D S zero mul A b W E) ↔
      EvalLaws hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound W) (env.bound E) := by
  simp only [evalLaws,EvalLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    eval_semantics hM,raw_semantics hM,old_semantics hM,cons_semantics hM,
    ConstructionProbeRawActionSyntax.oldAct_semantics hM,ConstructionProbeLetterAction.letterAct_semantics hM]
  rfl

def lawsSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isEmpty (.bound 3))
        (.imp (.mem (.bound 3) (.bound 0))
          (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 11) 4 9))
            (.imp (ConstructionProbeAlphabet.alphabet (1 : Fin 11) 4 9 2 10 5 8)
              (.imp (ConstructionProbeWord.wordCarrier (0 : Fin 11) 1 2 4 5 6 7)
                (.imp (.mem (.bound 6) (.bound 1)) (evalLaws (0 : Fin 11) 1 2 3 4 5 6 7 8))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
    ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,
    ConstructionProbeWord.wordCarrier_freeClosed,evalLaws_freeClosed]

theorem laws_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence lawsSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) lawsSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,evalLaws_semantics hM]
  exact fun hw hz hzw hm hAlpha hW hb => eval_laws hM hw hz hzw hm hAlpha hW hb

theorem laws_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence lawsSentence) := ModelTransfer.derives (fun _ hM => laws_models hM)

end PPAC.Migration.ConstructionProbeEvaluationSyntax
