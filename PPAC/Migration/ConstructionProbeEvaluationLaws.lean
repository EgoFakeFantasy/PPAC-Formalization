/- Pinned Raw.eval_oldAct/eval_injective and Word.eval_letterAct.
The source Raw induction is interpreted by the existing definable omega induction. -/
import PPAC.Migration.ConstructionProbeEvaluationSyntax

namespace PPAC.Migration.ConstructionProbeEvaluationLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeEvaluation
open ConstructionProbeLetterAction (LetterAct)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeWord (WordCarrier word_raw)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingDiagramOrder (Product)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source constructor induction only needs the current internal length predicate. -/
def lengthSchema {m : Nat} (p : Project.UnarySchema m) : Project.UnarySchema (m+2) where
  body := .forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 3 4))
      (.imp (.mem (.bound 1) (.bound 5))
        (.imp (ProjectSyntax.encode id (PairSyntax.ordered 0 2 1))
          (p.body.rename (Fin.cases 0 (fun i => i.succ.succ.succ.succ.succ.succ))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem lengthSchema_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p : Project.UnarySchema m)
    (D S n : M.Carrier .set) :
    (lengthSchema p).denote ((env.push D).push S) n ↔
      ∀ f x q, MapsTo n S f → (Project.FirstOrderSemantics.reduct M).mem x D →
        PureKuratowski.Code M q f x → p.denote env q := by
  simp only [lengthSchema,Project.UnarySchema.denote,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_rename,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_code]
  have he (f x q : M.Carrier .set) :
      ((((((env.push D).push S).push n).push f).push x).push q).reindex
        (Fin.cases 0 (fun i => i.succ.succ.succ.succ.succ.succ)) = env.push q := by
    dsimp only [SetTheory.Env.reindex,SetTheory.Env.push]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [he]
  rfl

/-- Adapt the source inductive Raw eliminator; every property is a pure formula. -/
theorem raw_induction (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p : Project.UnarySchema m)
    {w D S zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hOld : ∀ x q, Old zero D x q → p.denote env q)
    (hCons : ∀ s t q, Cons w D S s t q → p.denote env t → p.denote env q) :
    ∀ q, Raw w D S q → p.denote env q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let property : (Project.FirstOrderSemantics.reduct M).Domain → Prop := fun n =>
    ∀ f x q, MapsTo n S f → (Project.FirstOrderSemantics.reduct M).mem x D →
      PureKuratowski.Code M q f x → p.denote env q
  have hAll : ∀ n, (Project.FirstOrderSemantics.reduct M).mem n w → property n := by
    apply hw.induction property
    · obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF (lengthSchema p) ((env.push D).push S) w
      exact ⟨B,fun n => (hB n).trans (and_congr_right (fun _ => lengthSchema_semantics hM env p D S n))⟩
    · intro z hz' f x q hf hx hq
      have he : z = zero := (ModelTransfer.extensionality hM).eq_of_same_members z zero
        (fun i => ⟨fun hi => (hz' i hi).elim,fun hi => (hz i hi).elim⟩)
      subst z
      have he : f = zero := SetTheory.Structure.IsFiniteSequenceOfLength.empty_sequence_unique hZF.1
        ⟨hzw,native_sequence hM (hw.members_areOrdinals hZF zero hzw) hf⟩
        ⟨hzw,SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz⟩ hz hz
      subst f
      exact hOld x q ⟨hx,hq⟩
    · intro n hn ih k hkn f x q hf hx hq
      have hk : (Project.FirstOrderSemantics.reduct M).mem k w := by
        obtain ⟨k',hk'n,hk'⟩ := hw.1.2 n hn
        exact (SetTheory.Structure.SuccessorOf.eq hZF.1 hkn hk'n).symm ▸ hk'
      obtain ⟨j,g,s,hd⟩ := SetTheory.Structure.IsFiniteSequenceLastDecomposition.exists_of_nonempty hZF
        (KuratowskiZF.interpretation hM) hw
        ⟨hk,native_sequence hM (hw.members_areOrdinals hZF k hk) hf⟩ ⟨n,hkn.predecessor_mem⟩
      have he := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1
        (hw.members_areOrdinals hZF n hn) hkn hd.length_successor
      subst j
      have hg : MapsTo n S g := maps_of_sequence hM hd.prefix_sequence.2
        (fun i y hy => hf.2 i y ((hd.prefix_restriction.2 i y).mp hy).2)
      obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM g x
      exact hCons s t q ⟨n,k,g,f,x,hn,hk,hkn,hg,hf,hx,hf.2 n s hd.last_value,ht,hq,
        decomposition_append hM hf hd⟩ (ih g x t hg hx ht)
  rintro q ⟨f,x,⟨n,hn,hf⟩,hx,hq⟩
  exact hAll n hn f x q hf hx hq

/-- Source Raw.eval_oldAct, by its two constructor cases. -/
theorem eval_oldAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I a q r input v y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (ha : OldAct w D S zero mul A a q r)
    (hv : Eval hM w D S zero mul A b W E q input v)
    (hy : OldAct w D S zero mul A a v y) : Eval hM w D S zero mul A b W E r input y := by
  rcases ha.2 with ⟨x,z,hq,hax,hr⟩ | ⟨s,t,z,hq,has,hr⟩
  · apply (eval_old_iff hM hw hz hzw hm hAlpha hW hb hr hv.1).mpr
    exact oldAct_mul hM hw hz hm hAlpha.2.2.1 hax (eval_old_forward hM hw hz hq hv) hy
  · obtain ⟨u,hu,hletter⟩ := eval_cons_forward hM hw hq hv
    apply (eval_cons_iff hM hw hz hzw hm hAlpha hW hb hr).mpr
    exact ⟨u,hu,ConstructionProbeLetterAction.oldAct_letterAct hM hw hz hm hAlpha has hletter hy⟩


def injective {m : Nat} (w D S zero mul A b W E q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE
    (.imp (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ W.succ.succ.succ E.succ.succ.succ q.succ.succ.succ 2 0)
      (.imp (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ W.succ.succ.succ E.succ.succ.succ q.succ.succ.succ 1 0)
        (Project.Formula.extensionalEq (.bound 2) (.bound 1))))))

theorem injective_freeClosed {m : Nat} (w D S zero mul A b W E q : Fin m) :
    (injective w D S zero mul A b W E q).FreeClosed := by
  simp -implicitDefEqProofs [injective,Definitional.Formula.FreeClosed,
    ConstructionProbeEvaluationSyntax.eval_freeClosed,Project.Formula.extensionalEq_freeClosed_iff]

theorem injective_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E q : Fin m) :
    Project.Formula.satisfies env (injective w D S zero mul A b W E q) ↔
      ∀ input other y, Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) input y →
        Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) other y → input = other := by
  simp only [injective,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    Project.Term.eval_bound,ConstructionProbeEvaluationSyntax.eval_semantics hM]
  rfl

/-- Source Raw.eval_injective; the induction predicate is explicitly separable. -/
theorem eval_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I q input other y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hinput : Eval hM w D S zero mul A b W E q input y)
    (hother : Eval hM w D S zero mul A b W E q other y) : input = other := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul
      (Fin.cases A (Fin.cases b (Fin.cases W (fun _ => E))))))))
    free := fun _ => w }
  let p : Project.UnarySchema 9 := {
    body := injective 1 2 3 4 5 6 7 8 9 0
    freeClosed := injective_freeClosed _ _ _ _ _ _ _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ∀ input other y, Eval hM w D S zero mul A b W E q input y →
        Eval hM w D S zero mul A b W E q other y → input = other :=
    injective_semantics hM (env.push q) 1 2 3 4 5 6 7 8 9 0
  have hAll := raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro input other y hi ho
    exact oldAct_injective hM hw hz hm hAlpha.2.2.1
      (eval_old_forward hM hw hz hOld hi) (eval_old_forward hM hw hz hOld ho)) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro input other y hi ho
    obtain ⟨v,hv,hs⟩ := eval_cons_forward hM hw hCons hi
    obtain ⟨v',hv',hs'⟩ := eval_cons_forward hM hw hCons ho
    have heq := ConstructionProbeLetterAction.letterAct_injective hM hw hz hzw hm hAlpha hs hs'
    subst v'
    exact (he t).mp ih input other v hv hv')
  exact (he q).mp (hAll q (eval_raw hM hinput)) input other y hinput hother

/-- Source Word.eval_letterAct, keeping its head-divisibility split. -/
theorem eval_letterAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I s q r input v y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (ha : LetterAct w D S zero mul A b W E s q r)
    (hv : Eval hM w D S zero mul A b W E q input v)
    (hy : LetterAct w D S zero mul A b W E s v y) : Eval hM w D S zero mul A b W E r input y := by
  rcases ha.2.2 with ⟨_,u,z,hu,hzE,hur⟩ | ⟨_,hCons⟩
  · obtain ⟨t,ht⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (word_raw hW hu.2.1) hv.1
    obtain ⟨v',hv'⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hb (word_raw hW (eval_word hM ht))
    have he := eval_unique hM hw hz hzw hm hAlpha hW hb
      (eval_oldAct hM hw hz hzw hm hAlpha hW hb hu.2.2 ht hv') hv
    subst v'
    have hzy := (ConstructionProbeLetterAction.letterAct_oldAct_b hM hw hz hzw hm hAlpha hW ha.1
      (eval_word hM ht) hv' hzE).mp hy
    exact eval_oldAct hM hw hz hzw hm hAlpha hW hb hur ht hzy
  · exact (eval_cons_iff hM hw hz hzw hm hAlpha hW hb hCons).mpr ⟨v,hv,hy⟩

end PPAC.Migration.ConstructionProbeEvaluationLaws
