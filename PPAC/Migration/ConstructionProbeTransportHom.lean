/- Pinned ProbePresentations.Word.transport_quotient/letterAct/mul/transportHom.
Use the existing literal Word graph, reduction laws and pure Raw induction. -/
import PPAC.Migration.ConstructionProbeWordTransport
import PPAC.Migration.ConstructionProbeWordMonoidSyntax

namespace PPAC.Migration.ConstructionProbeTransportHom
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Old Cons old_unique)
open ConstructionProbeRawAction (OldAct cons_letter)
open ConstructionProbeWordQuotient (QuotientValue)
open ConstructionProbeLetterAction (LetterAct)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeAlphabetMap (ExitMap)
open ConstructionProbeRawTransport (ConstructorLaws SimulationLaws)
open ConstructionProbeWordTransport (WordGraph)
open ConstructionProbeEvaluation (Eval eval_word eval_old_iff eval_cons_iff)
open ConstructionProbeEvaluationSyntax (eval eval_freeClosed eval_semantics)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeLiftHom (PreservesProducts)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem transport_quotient {w D N S SN zero mul mulN A AN f H W WN a fa q Q r R : M.Carrier .set}
    (hH : MapsTo W WN H) (hSim : SimulationLaws w D N S SN zero mul mulN A AN f H)
    (ha : PureKuratowski.PairMember M a fa f)
    (hq : PureKuratowski.PairMember M q Q H) (hr : PureKuratowski.PairMember M r R H)
    (hval : QuotientValue w D S zero mul A W a q r) :
    QuotientValue w N SN zero mulN AN WN fa Q R :=
  ⟨hH.2 q Q hq,hH.2 r R hr,hSim.2 a fa r R q Q ha hr hq hval.2.2⟩

theorem transport_letterAct {w D N S SN zero mul mulN A AN b fb f g H W WN E EN s gs q Q r R : M.Carrier .set}
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hH : MapsTo W WN H) (hE : MapsTo S D E)
    (hCtor : ConstructorLaws w D N S SN zero f g H)
    (hSim : SimulationLaws w D N S SN zero mul mulN A AN f H) (hExit : ExitMap E EN f g)
    (hb : PureKuratowski.PairMember M b fb f) (hgs : PureKuratowski.PairMember M s gs g)
    (hq : PureKuratowski.PairMember M q Q H) (hr : PureKuratowski.PairMember M r R H)
    (hval : LetterAct w D S zero mul A b W E s q r) :
    LetterAct w N SN zero mulN AN fb WN EN gs Q R := by
  refine ⟨hg.2 s gs hgs,hH.2 q Q hq,?_⟩
  rcases hval.2.2 with ⟨hd,v,z,hv,hz,hact⟩ | ⟨hd,hcons⟩
  · obtain ⟨V,hV,_⟩ := hH.1.2 v hv.2.1
    obtain ⟨fz,hfz,_⟩ := hf.1.2 z (hE.2 s z hz)
    exact Or.inl ⟨((hSim.1 b fb q Q hb hq).1).mpr hd,V,fz,
      transport_quotient hH hSim hb hq hV hv,hExit s z gs fz hz hgs hfz,
      hSim.2 z fz v V r R hfz hV hr hact⟩
  · exact Or.inr ⟨fun h => hd (((hSim.1 b fb q Q hb hq).1).mp h),hCtor.2 s gs q Q r R hgs hcons hq hr⟩

/-- Exactly the two reduction comparisons consumed by the source multiplication induction. -/
def ReductionLaws (w D N S SN zero mul mulN A AN b fb W WN E EN f g H : M.Carrier .set) : Prop :=
  (∀ a fa q Q r R, PureKuratowski.PairMember M a fa f → PureKuratowski.PairMember M q Q H →
    PureKuratowski.PairMember M r R H → QuotientValue w D S zero mul A W a q r →
      QuotientValue w N SN zero mulN AN WN fa Q R) ∧
  (∀ s gs q Q r R, PureKuratowski.PairMember M s gs g → PureKuratowski.PairMember M q Q H →
    PureKuratowski.PairMember M r R H → LetterAct w D S zero mul A b W E s q r →
      LetterAct w N SN zero mulN AN fb WN EN gs Q R)

theorem reduction_laws {w D N S SN zero mul mulN A AN b fb f g H W WN E EN : M.Carrier .set}
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hH : MapsTo W WN H) (hE : MapsTo S D E)
    (hCtor : ConstructorLaws w D N S SN zero f g H)
    (hSim : SimulationLaws w D N S SN zero mul mulN A AN f H) (hExit : ExitMap E EN f g)
    (hb : PureKuratowski.PairMember M b fb f) : ReductionLaws w D N S SN zero mul mulN A AN b fb W WN E EN f g H :=
  ⟨fun _ _ _ _ _ _ ha hq hr hv => transport_quotient hH hSim ha hq hr hv,
    fun _ _ _ _ _ _ hgs hq hr hv => transport_letterAct hf hg hH hE hCtor hSim hExit hb hgs hq hr hv⟩

def EvalMapAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w D N S SN zero mul mulN A AN b fb W WN E EN H q : M.Carrier .set) : Prop :=
  ∀ Q input inputN y Y, PureKuratowski.PairMember M q Q H → PureKuratowski.PairMember M input inputN H →
    PureKuratowski.PairMember M y Y H → Eval hM w D S zero mul A b W E q input y →
      Eval hM w N SN zero mulN AN fb WN EN Q inputN Y

def evalMapAt {m : Nat} (w D N S SN zero mul mulN A AN b fb W WN E EN H q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 4)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ 3 2)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ 1 0)) (.imp (eval
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ
  b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ
  q.succ.succ.succ.succ.succ 3 1) (eval w.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ
  SN.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ fb.succ.succ.succ.succ.succ WN.succ.succ.succ.succ.succ
  EN.succ.succ.succ.succ.succ 4 2 0))))))))))

theorem evalMapAt_freeClosed {m : Nat} (w D N S SN zero mul mulN A AN b fb W WN E EN H q : Fin m) :
    (evalMapAt w D N S SN zero mul mulN A AN b fb W WN E EN H q).FreeClosed := by
  simp -implicitDefEqProofs [evalMapAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eval_freeClosed]

theorem evalMapAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N S SN zero mul mulN A AN b fb W WN E EN H q : Fin m) :
    Project.Formula.satisfies env (evalMapAt w D N S SN zero mul mulN A AN b fb W WN E EN H q) ↔
      EvalMapAt hM (env.bound w) (env.bound D) (env.bound N) (env.bound S) (env.bound SN) (env.bound zero)
        (env.bound mul) (env.bound mulN) (env.bound A) (env.bound AN) (env.bound b) (env.bound fb)
        (env.bound W) (env.bound WN) (env.bound E) (env.bound EN) (env.bound H) (env.bound q) := by
  simp only [evalMapAt,EvalMapAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,eval_semantics hM]
  rfl

theorem eval_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g W WN E EN e eN I IN H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hH : MapsTo W WN H) (hCtor : ConstructorLaws w D N S SN zero f g H)
    (hSim : SimulationLaws w D N S SN zero mul mulN A AN f H)
    (hRed : ReductionLaws w D N S SN zero mul mulN A AN b fb W WN E EN f g H) :
    ∀ q, Raw w D S q → EvalMapAt hM w D N S SN zero mul mulN A AN b fb W WN E EN H q := by
  let schema : Project.UnarySchema 17 := {
    body := evalMapAt 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 0
    freeClosed := evalMapAt_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 17 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases N (Fin.cases S (Fin.cases SN (Fin.cases zero (Fin.cases mul (Fin.cases mulN (Fin.cases A (Fin.cases AN (Fin.cases b (Fin.cases fb (Fin.cases W (Fin.cases WN (Fin.cases E (Fin.cases EN (fun _ => H)))))))))))))))),
      free := fun _ => w }
  have he (q) : schema.denote env q ↔ EvalMapAt hM w D N S SN zero mul mulN A AN b fb W WN E EN H q :=
    evalMapAt_semantics hM (env.push q) 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 0
  have hAll : ∀ q, Raw w D S q → schema.denote env q := by
    apply ConstructionProbeEvaluationLaws.raw_induction hM env schema hw hz hzw
    · intro x q hOld
      apply (he q).mpr
      intro Q input inputN y Y hQ hInput hY hEval
      obtain ⟨fx,hfx,_⟩ := hf.1.2 x hOld.1
      have hOldN := hCtor.1 x fx q Q hfx hOld hQ
      apply (eval_old_iff hM hw hz hzw hmN hAlphaN hWN (hf.2 b fb hb) hOldN (hH.2 input inputN hInput)).mpr
      exact hSim.2 x fx input inputN y Y hfx hInput hY
        ((eval_old_iff hM hw hz hzw hm hAlpha hW (function_input hf.1 hb) hOld (function_input hH.1 hInput)).mp hEval)
    · intro s t q hCons ih
      apply (he q).mpr
      intro Q input inputN y Y hQ hInput hY hEval
      have htW := (hW t).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hCons).mp
        ((hW q).mp (function_input hH.1 hQ))).1
      obtain ⟨T,hT,_⟩ := hH.1.2 t htW
      obtain ⟨gs,hgs,_⟩ := hg.1.2 s (cons_letter hCons)
      have hConsN := hCtor.2 s gs t T q Q hgs hCons hT hQ
      obtain ⟨v,hv,hLetter⟩ := (eval_cons_iff hM hw hz hzw hm hAlpha hW (function_input hf.1 hb) hCons).mp hEval
      obtain ⟨V,hV,_⟩ := hH.1.2 v (eval_word hM hv)
      exact (eval_cons_iff hM hw hz hzw hmN hAlphaN hWN (hf.2 b fb hb) hConsN).mpr
        ⟨V,(he t).mp ih T input inputN v V hT hInput hV hv,hRed.2 s gs v V y Y hgs hV hY hLetter⟩
  exact fun q hq => (he q).mp (hAll q hq)

theorem transport_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g W WN E EN e eN I IN H G GN : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hH : MapsTo W WN H) (hCtor : ConstructorLaws w D N S SN zero f g H)
    (hSim : SimulationLaws w D N S SN zero mul mulN A AN f H)
    (hRed : ReductionLaws w D N S SN zero mul mulN A AN b fb W WN E EN f g H)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN) : PreservesProducts G GN H := by
  intro q input y Q inputN Y hprod hQ hInput hY
  obtain ⟨hq,hEval⟩ := (hG q input y).mp hprod
  exact (hGN Q inputN Y).mpr ⟨hH.2 q Q hQ,
    eval_transport hM hw hz hzw hm hmN hAlpha hAlphaN hf hg hb hW hWN hH hCtor hSim hRed
      q (word_raw hW hq) Q input inputN y Y hQ hInput hY hEval⟩

theorem exists_transport_hom (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g W WN E EN e eN I IN G GN unit unitN : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Injection D N f) (hPres : PreservesProducts mul mulN f)
    (hFactors : ConstructionProbeAlphabetMap.FactorConservation N mulN f)
    (hAlphabet : ConstructionProbeAlphabetMap.AlphabetSimulation S SN A AN E EN f g)
    (hb : PureKuratowski.PairMember M b fb f) (hOne : PureKuratowski.PairMember M e eN f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hUnit : Old zero D e unit) (hUnitN : Old zero N eN unitN) :
    ∃ H, Injection W WN H ∧ WordGraph w D S SN f g W H ∧ PreservesProducts G GN H ∧
      PureKuratowski.PairMember M unit unitN H ∧ ReductionLaws w D N S SN zero mul mulN A AN b fb W WN E EN f g H := by
  obtain ⟨H,hH,hGraph,hCtor,hSim⟩ := ConstructionProbeWordTransport.exists_transport hM hw hz hzw hf hAlphabet.1
    (ConstructionProbeAlphabetMap.division_reflection hm hmN hf hPres hFactors) hAlphabet.2.2.2
    hPres hAlphabet.2.1 hb hW hWN
  have hRed := reduction_laws hf.1 hAlphabet.1.1 hH.1 hAlpha.2.2.2.1 hCtor hSim hAlphabet.2.2.1 hb
  have hMul := transport_mul hM hw hz hzw hm hmN hAlpha hAlphaN hf.1 hAlphabet.1.1 hb hW hWN hH.1 hCtor hSim hRed hG hGN
  have hUnitW := (hW unit).mpr (ConstructionProbeReduced.reduced_old hM hz hzw hUnit)
  obtain ⟨U,hU,_⟩ := hH.1.1.2 unit hUnitW
  have he := old_unique hM (hCtor.1 e eN unit U hOne hUnit hU) hUnitN
  exact ⟨H,hH,hGraph,hMul,he ▸ hU,hRed⟩

end PPAC.Migration.ConstructionProbeTransportHom
