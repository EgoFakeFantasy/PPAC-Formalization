/- Pinned ProbeWords.Word: the actual internal set of reduced Raw words.
The source subtype is realized by native Separation, with no choice operation. -/
import PPAC.Migration.ConstructionProbeRawActionSyntax
import PPAC.Migration.ConstructionProbeReduced

namespace PPAC.Migration.ConstructionProbeWord
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeReduced
open ConstructionProbeRawActionSyntax (oldAct oldAct_freeClosed oldAct_semantics
  headDiv headDiv_freeClosed headDiv_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def WordCarrier (w D S mul A b W : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q W ↔ Reduced w D S mul A b q

theorem exists_word_carrier (hM : FirstOrder.Theory.Models M nativeZF) {w : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (D S mul A b : M.Carrier .set) :
    ∃ W, WordCarrier w D S mul A b W := by
  obtain ⟨R,hR⟩ := ConstructionProbeRaw.exists_carrier hM hw D S
  let schema : Project.UnarySchema 6 := {
    body := reduced 1 2 3 4 5 6 0
    freeClosed := reduced_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases mul (Fin.cases A (fun _ => b))))),
      free := fun _ => w }
  obtain ⟨W,hW⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env R
  refine ⟨W,fun q => (hW q).trans ?_⟩
  have he : schema.denote env q ↔ Reduced w D S mul A b q :=
    reduced_semantics hM (env.push q) 1 2 3 4 5 6 0
  exact ⟨fun h => he.mp h.2,
    fun h => ⟨(hR q).mpr (reduced_raw h),he.mpr h⟩⟩

theorem word_raw {w D S mul A b W q : M.Carrier .set}
    (hW : WordCarrier w D S mul A b W)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) : Raw w D S q :=
  reduced_raw ((hW q).mp hq)

/-- Source Word.headDiv_iff: the Raw preimage is reduced because oldAct
preserves and reflects reducedness. No choice function is extracted. -/
theorem headDiv_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W a q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    HeadDiv w D S zero mul A a q ↔ ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r W ∧ OldAct w D S zero mul A a r q := by
  constructor
  · intro h
    obtain ⟨r,_,hr⟩ := (ConstructionProbeRawAction.headDiv_iff hM hw hz hzw ha).mp h
    exact ⟨r,(hW r).mpr ((reduced_oldAct hM hw hz hzw hr).mp ((hW q).mp hq)),hr⟩
  · rintro ⟨r,hr,hact⟩
    exact (ConstructionProbeRawAction.headDiv_iff hM hw hz hzw ha).mpr ⟨r,word_raw hW hr,hact⟩

def WordLaws (w D S zero mul A b W : M.Carrier .set) : Prop :=
  (∀ x q, Old zero D x q → (Project.FirstOrderSemantics.reduct M).mem q W) ∧
  (∀ s t q, Cons w D S s t q →
    ((Project.FirstOrderSemantics.reduct M).mem q W ↔
      (Project.FirstOrderSemantics.reduct M).mem t W ∧ ¬ HeadDiv w D S zero mul A b t)) ∧
  (∀ a q r, OldAct w D S zero mul A a q r →
    ((Project.FirstOrderSemantics.reduct M).mem r W ↔ (Project.FirstOrderSemantics.reduct M).mem q W)) ∧
  (∀ a q, (Project.FirstOrderSemantics.reduct M).mem a D →
    (Project.FirstOrderSemantics.reduct M).mem q W →
    (HeadDiv w D S zero mul A a q ↔ ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r W ∧ OldAct w D S zero mul A a r q))

theorem word_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) : WordLaws w D S zero mul A b W := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x q hq
    exact (hW q).mpr (reduced_old hM hz hzw hq)
  · intro s t q hq
    exact (hW q).trans ((reduced_cons hM hw hz hzw hq).trans (and_congr (hW t).symm Iff.rfl))
  · intro a q r hact
    exact (hW r).trans ((reduced_oldAct hM hw hz hzw hact).trans (hW q).symm)
  · intro a q ha hq
    exact headDiv_iff hM hw hz hzw hW ha hq

def wordCarrier {m : Nat} (w D S mul A b W : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound W.succ)) (reduced w.succ D.succ S.succ mul.succ A.succ b.succ
    0)))

def wordLaws {m : Nat} (w D S zero mul A b W : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (old zero.succ.succ D.succ.succ 1 0) (.mem (.bound 0) (.bound
    W.succ.succ))))) (.conj (.forallE (.forallE (.forallE (.imp (cons w.succ.succ.succ D.succ.succ.succ
    S.succ.succ.succ 2 1 0) (.iff (.mem (.bound 0) (.bound W.succ.succ.succ)) (.conj (.mem (.bound 1)
    (.bound W.succ.succ.succ)) (.neg (headDiv w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ
    zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ 1)))))))) (.conj (.forallE
    (.forallE (.forallE (.imp (oldAct w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ
    mul.succ.succ.succ A.succ.succ.succ 2 1 0) (.iff (.mem (.bound 0) (.bound W.succ.succ.succ)) (.mem
    (.bound 1) (.bound W.succ.succ.succ))))))) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound
    D.succ.succ)) (.imp (.mem (.bound 0) (.bound W.succ.succ)) (.iff (headDiv w.succ.succ D.succ.succ
    S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ 1 0) (.existsE (.conj (.mem (.bound 0) (.bound
    W.succ.succ.succ)) (oldAct w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ
    mul.succ.succ.succ A.succ.succ.succ 2 0 1)))))))))))

theorem wordCarrier_freeClosed {m : Nat} (w D S mul A b W : Fin m) :
    (wordCarrier w D S mul A b W).FreeClosed := by
  simp -implicitDefEqProofs [wordCarrier,Definitional.Formula.FreeClosed,reduced_freeClosed]

theorem wordLaws_freeClosed {m : Nat} (w D S zero mul A b W : Fin m) :
    (wordLaws w D S zero mul A b W).FreeClosed := by
  simp -implicitDefEqProofs [wordLaws,Definitional.Formula.FreeClosed,
    old_freeClosed,cons_freeClosed,oldAct_freeClosed,headDiv_freeClosed]

theorem wordCarrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S mul A b W : Fin m) :
    Project.Formula.satisfies env (wordCarrier w D S mul A b W) ↔
      WordCarrier (env.bound w) (env.bound D) (env.bound S) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound W) := by
  simp only [wordCarrier,WordCarrier,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,reduced_semantics hM]
  rfl

theorem wordLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W : Fin m) :
    Project.Formula.satisfies env (wordLaws w D S zero mul A b W) ↔
      WordLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound W) := by
  simp only [wordLaws,WordLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    old_semantics hM,cons_semantics hM,oldAct_semantics hM,headDiv_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isEmpty (.bound 3))
        (.imp (.mem (.bound 3) (.bound 0))
          (.existsE (.conj (wordCarrier (1 : Fin 8) 2 3 5 6 7 0)
            (wordLaws (1 : Fin 8) 2 3 4 5 6 7 0))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    Project.Formula.isEmpty,wordCarrier_freeClosed,wordLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    wordCarrier_semantics hM,wordLaws_semantics hM]
  intro hw hz hzw
  obtain ⟨W,hW⟩ := exists_word_carrier hM hw (bound 1) (bound 2) (bound 4) (bound 5) (bound 6)
  exact ⟨W,hW,word_laws hM hw hz hzw hW⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeWord
