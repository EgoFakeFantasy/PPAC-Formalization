/- Source Word.mul_assoc/mul_one and the actual LeftCancelMonoid instance. -/
import PPAC.Migration.ConstructionProbeEvaluationLaws

namespace PPAC.Migration.ConstructionProbeWordMonoid
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeEvaluation ConstructionProbeEvaluationLaws
open ConstructionProbeLetterAction (LetterAct)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeLetters (Representatives exists_representatives)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def associative {m : Nat} (w D S zero mul A b W E q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 4 2)
      (.imp (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ 4 3 1)
        (.imp (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ 2 3 0)
          (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 1 0))))))))

theorem associative_freeClosed {m : Nat} (w D S zero mul A b W E q : Fin m) :
    (associative w D S zero mul A b W E q).FreeClosed := by
  simp -implicitDefEqProofs [associative,Definitional.Formula.FreeClosed,ConstructionProbeEvaluationSyntax.eval_freeClosed]

theorem associative_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E q : Fin m) :
    Project.Formula.satisfies env (associative w D S zero mul A b W E q) ↔
      ∀ v input a c y, Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) v a →
        Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) v input c → Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) a input y →
          Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) c y := by
  simp only [associative,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ConstructionProbeEvaluationSyntax.eval_semantics hM]
  rfl

/-- Same old/cons induction as the pinned Word.mul_assoc proof. -/
theorem eval_assoc (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I q v input a c y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hqa : Eval hM w D S zero mul A b W E q v a)
    (hvc : Eval hM w D S zero mul A b W E v input c)
    (hay : Eval hM w D S zero mul A b W E a input y) :
    Eval hM w D S zero mul A b W E q c y := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul
      (Fin.cases A (Fin.cases b (Fin.cases W (fun _ => E))))))))
    free := fun _ => w }
  let p : Project.UnarySchema 9 := {
    body := associative 1 2 3 4 5 6 7 8 9 0
    freeClosed := associative_freeClosed _ _ _ _ _ _ _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ∀ v input a c y, Eval hM w D S zero mul A b W E q v a →
        Eval hM w D S zero mul A b W E v input c → Eval hM w D S zero mul A b W E a input y →
          Eval hM w D S zero mul A b W E q c y :=
    associative_semantics hM (env.push q) 1 2 3 4 5 6 7 8 9 0
  have hAll := raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro v input a c y hqa hvc hay
    have hxa := eval_old_forward hM hw hz hOld hqa
    obtain ⟨z,hzact⟩ := oldAct_total hM hw hz hzw hm hAlpha.1 hAlpha.2.1 hOld.1
      (word_raw hW (eval_word hM hvc))
    have heq := eval_unique hM hw hz hzw hm hAlpha hW hb
      (eval_oldAct hM hw hz hzw hm hAlpha hW hb hxa hvc hzact) hay
    subst z
    exact (eval_old_iff hM hw hz hzw hm hAlpha hW hb hOld (eval_word hM hvc)).mpr hzact) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro v input a c y hqa hvc hay
    obtain ⟨a0,ha0,hsa⟩ := eval_cons_forward hM hw hCons hqa
    obtain ⟨d,hd⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (word_raw hW (eval_word hM ha0)) hvc.1
    have htc := (he t).mp ih v input a0 c d ha0 hvc hd
    obtain ⟨z,hzletter⟩ := ConstructionProbeLetterAction.letterAct_total hM hw hz hzw hm hAlpha hW hb
      (cons_letter hCons) (eval_word hM hd)
    have heq := eval_unique hM hw hz hzw hm hAlpha hW hb
      (eval_letterAct hM hw hz hzw hm hAlpha hW hb hsa hd hzletter) hay
    subst z
    exact (eval_cons_iff hM hw hz hzw hm hAlpha hW hb hCons).mpr ⟨d,htc,hzletter⟩)
  exact (he q).mp (hAll q (eval_raw hM hqa)) v input a c y hqa hvc hay

def rightUnit {m : Nat} (w D S zero mul A b W E unit q : Fin m) : Project.Formula 1 m :=
  .imp (.mem (.bound q) (.bound W)) (ConstructionProbeEvaluationSyntax.eval w D S zero mul A b W E q unit q)

theorem rightUnit_freeClosed {m : Nat} (w D S zero mul A b W E unit q : Fin m) :
    (rightUnit w D S zero mul A b W E unit q).FreeClosed := by
  simp -implicitDefEqProofs [rightUnit,Definitional.Formula.FreeClosed,ConstructionProbeEvaluationSyntax.eval_freeClosed]

theorem rightUnit_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E unit q : Fin m) :
    Project.Formula.satisfies env (rightUnit w D S zero mul A b W E unit q) ↔
      ((Project.FirstOrderSemantics.reduct M).mem (env.bound q) (env.bound W) →
        Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) (env.bound unit) (env.bound q)) := by
  simp only [rightUnit,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,ConstructionProbeEvaluationSyntax.eval_semantics hM]

/-- Same reduced-cons step as the pinned Word.mul_one proof. -/
theorem eval_one (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I unit q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    Eval hM w D S zero mul A b W E q unit q := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 10 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul
      (Fin.cases A (Fin.cases b (Fin.cases W (Fin.cases E (fun _ => unit)))))))))
    free := fun _ => w }
  let p : Project.UnarySchema 10 := {
    body := rightUnit 1 2 3 4 5 6 7 8 9 10 0
    freeClosed := rightUnit_freeClosed _ _ _ _ _ _ _ _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ((Project.FirstOrderSemantics.reduct M).mem q W → Eval hM w D S zero mul A b W E q unit q) :=
    rightUnit_semantics hM (env.push q) 1 2 3 4 5 6 7 8 9 10 0
  have hUnitW := (hW unit).mpr (ConstructionProbeReduced.reduced_old hM hz hzw hUnit)
  have hAll := raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro _
    apply (eval_old_iff hM hw hz hzw hm hAlpha hW hb hOld hUnitW).mpr
    exact (oldAct_old_iff hz hUnit).mpr ⟨hOld.1,x,((hm.1.2 x hOld.1 x).2).mpr rfl,hOld⟩) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro hq
    obtain ⟨ht,hnot⟩ := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp ((hW q).mp hq)
    have htW := (hW t).mpr ht
    exact (eval_cons_iff hM hw hz hzw hm hAlpha hW hb hCons).mpr
      ⟨t,(he t).mp ih htW,⟨cons_letter hCons,htW,Or.inr ⟨hnot,hCons⟩⟩⟩)
  exact (he q).mp (hAll q (word_raw hW hq)) hq


def multiplicationPair {m : Nat} (w D S zero mul A b W E pair y : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered pair.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound W.succ.succ))
      (ConstructionProbeEvaluationSyntax.eval w.succ.succ D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ b.succ.succ W.succ.succ E.succ.succ 1 0 y.succ.succ))))

theorem multiplicationPair_freeClosed {m : Nat} (w D S zero mul A b W E pair y : Fin m) :
    (multiplicationPair w D S zero mul A b W E pair y).FreeClosed := by
  simp -implicitDefEqProofs [multiplicationPair,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeEvaluationSyntax.eval_freeClosed]

theorem multiplicationPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E pair y : Fin m) :
    Project.Formula.satisfies env (multiplicationPair w D S zero mul A b W E pair y) ↔
      ∃ q input, PureKuratowski.Code M (env.bound pair) q input ∧
        (Project.FirstOrderSemantics.reduct M).mem q (env.bound W) ∧
          Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) q input (env.bound y) := by
  simp only [multiplicationPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    ConstructionProbeEvaluationSyntax.eval_semantics hM]
  rfl

def MultiplicationGraph (hM : FirstOrder.Theory.Models M nativeZF)
    (w D S zero mul A b W E G : M.Carrier .set) : Prop := ∀ q input y,
  Product G q input y ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
    Eval hM w D S zero mul A b W E q input y

theorem exists_multiplication (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D) :
    ∃ J G, Representatives W W J ∧ MapsTo J W G ∧ MultiplicationGraph hM w D S zero mul A b W E G := by
  obtain ⟨J,hJ⟩ := exists_representatives hM W W
  let schema : Project.BinarySchema 9 := {
    body := multiplicationPair 2 3 4 5 6 7 8 9 10 1 0
    freeClosed := multiplicationPair_freeClosed _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul
      (Fin.cases A (Fin.cases b (Fin.cases W (fun _ => E))))))))
    free := fun _ => w }
  have he (pair y : M.Carrier .set) : schema.denote env pair y ↔
      ∃ q input, PureKuratowski.Code M pair q input ∧ (Project.FirstOrderSemantics.reduct M).mem q W ∧
        Eval hM w D S zero mul A b W E q input y :=
    multiplicationPair_semantics hM ((env.push pair).push y) 2 3 4 5 6 7 8 9 10 1 0
  obtain ⟨G,hG,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := W) (by
      intro pair hp
      obtain ⟨q,input,hq,hi,hcode⟩ := (hJ pair).mp hp
      obtain ⟨y,hy⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (word_raw hW hq) hi
      exact ⟨y,(he pair y).mpr ⟨q,input,hcode,hq,hy⟩⟩) (by
      intro pair _ y z hy hzv
      obtain ⟨q,input,hcode,_,hy⟩ := (he pair y).mp hy
      obtain ⟨q',input',hcode',_,hzv⟩ := (he pair z).mp hzv
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact eval_unique hM hw hz hzw hm hAlpha hW hb hy hzv) (by
      intro pair y _ hy
      obtain ⟨q,input,_,_,hy⟩ := (he pair y).mp hy
      exact eval_word hM hy)
  refine ⟨J,G,hJ,(ForcingSupportSize.native_mapsTo hM J W G).mpr hG,fun q input y => ?_⟩
  constructor
  · rintro ⟨pair,hcode,hpy⟩
    obtain ⟨_,hval⟩ := (hgraph pair y).mp hpy
    obtain ⟨q',input',hcode',hq,hy⟩ := (he pair y).mp hval
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨hq,hy⟩
  · rintro ⟨hq,hy⟩
    obtain ⟨pair,hcode⟩ := KuratowskiZF.exists_code hM q input
    exact ⟨pair,hcode,(hgraph pair y).mpr
      ⟨(hJ pair).mpr ⟨q,input,hq,hy.1,hcode⟩,(he pair y).mpr ⟨q,input,hcode,hq,hy⟩⟩⟩

/-- Actual multiplication graph satisfies the source LeftCancelMonoid contract. -/
theorem monoid_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I unit G : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G) :
    LeftCancelMonoid W G unit := by
  have hUnitW := (hW unit).mpr (ConstructionProbeReduced.reduced_old hM hz hzw hUnit)
  refine ⟨⟨hUnitW,?_⟩,?_,?_⟩
  · intro x hx y
    constructor
    · constructor
      · intro hy
        have hact := eval_old_forward hM hw hz hUnit ((hG unit x y).mp hy).2
        exact oldAct_unique hM hw hz hm hAlpha.2.1 hact
          (oldAct_one hM hw hz hzw hm hAlpha.2.2.1 (word_raw hW hx))
      · intro heq
        subst y
        exact (hG unit x x).mpr ⟨hUnitW,(eval_old_iff hM hw hz hzw hm hAlpha hW hb hUnit hx).mpr
          (oldAct_one hM hw hz hzw hm hAlpha.2.2.1 (word_raw hW hx))⟩
    · constructor
      · intro hy
        exact eval_unique hM hw hz hzw hm hAlpha hW hb ((hG x unit y).mp hy).2
          (eval_one hM hw hz hzw hm hAlpha hW hb hUnit hx)
      · intro heq
        subst y
        exact (hG x unit x).mpr ⟨hx,eval_one hM hw hz hzw hm hAlpha hW hb hUnit hx⟩
  · intro q hq
    refine ⟨?_,?_,?_⟩
    · intro input hi
      obtain ⟨y,hy⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (word_raw hW hq) hi
      exact ⟨y,eval_word hM hy,(hG q input y).mpr ⟨hq,hy⟩⟩
    · intro input y z _ hy hzv
      exact eval_unique hM hw hz hzw hm hAlpha hW hb ((hG q input y).mp hy).2 ((hG q input z).mp hzv).2
    · intro input other y _ _ hi ho
      exact eval_injective hM hw hz hzw hm hAlpha ((hG q input y).mp hi).2 ((hG q other y).mp ho).2
  · intro q v input a c y hq _ hi hqa hvc
    have hqa' := ((hG q v a).mp hqa).2
    have hvc' := ((hG v input c).mp hvc).2
    constructor
    · intro hay
      exact (hG q c y).mpr ⟨hq,eval_assoc hM hw hz hzw hm hAlpha hW hb hqa' hvc' ((hG a input y).mp hay).2⟩
    · intro hqy
      obtain ⟨z,hzv⟩ := eval_total hM hw hz hzw hm hAlpha hW hb (word_raw hW (eval_word hM hqa')) hi
      have he := eval_unique hM hw hz hzw hm hAlpha hW hb
        (eval_assoc hM hw hz hzw hm hAlpha hW hb hqa' hvc' hzv) ((hG q c y).mp hqy).2
      subst z
      exact (hG a input y).mpr ⟨eval_word hM hqa',hzv⟩

end PPAC.Migration.ConstructionProbeWordMonoid
