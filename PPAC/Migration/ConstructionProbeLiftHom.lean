/- Pinned evalHom_oldAct/evalHom_letterAct/evalHom_mul and liftHom laws.
The target is an arbitrary internal monoid, with no cancellation hypothesis. -/
import PPAC.Migration.ConstructionProbeHomEvaluationSyntax
import PPAC.Migration.ConstructionProbeGenerator

namespace PPAC.Migration.ConstructionProbeLiftHom
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeHomEvaluation
open ConstructionProbeHomEvaluationSyntax (LiftGraph)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (Unit Associative)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def PreservesProducts (mul mulN F : M.Carrier .set) : Prop := ∀ x y z fx fy fz,
  Product mul x y z → PureKuratowski.PairMember M x fx F → PureKuratowski.PairMember M y fy F →
    PureKuratowski.PairMember M z fz F → Product mulN fx fy fz

def Equivariant (A F Q mulN : M.Carrier .set) : Prop := ∀ x s t fx qs qt,
  Product A x s t → PureKuratowski.PairMember M x fx F → PureKuratowski.PairMember M s qs Q →
    PureKuratowski.PairMember M t qt Q → Product mulN fx qs qt

def ExitCompatible (b E F Q mulN : M.Carrier .set) : Prop := ∀ s z qs fb fz,
  PureKuratowski.PairMember M s z E → PureKuratowski.PairMember M s qs Q →
    PureKuratowski.PairMember M b fb F → PureKuratowski.PairMember M z fz F → Product mulN qs fb fz

theorem eval_oldAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A N J mulN F Q a q r v fa y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN F) (hEq : Equivariant A F Q mulN)
    (hact : OldAct w D S zero mul A a q r) (hv : Eval hM w D S N mulN F Q q v)
    (hfa : PureKuratowski.PairMember M a fa F) (hy : Product mulN fa v y) :
    Eval hM w D S N mulN F Q r y := by
  rcases hact.2 with ⟨x,z,hq,haxz,hr⟩ | ⟨s,t,s',hq,hass,hr⟩
  · have hfx := eval_old_forward hM hw hz hq hv
    obtain ⟨fz,hfz,_⟩ := hF.1.2 z hr.1
    have he := product_unique hM hMul (hPres a x z fa v fz haxz hfa hfx hfz) hy
    subst fz
    exact (eval_old_iff hM hw hz hzw hJ hMul hF hQ hr).mpr hfz
  · obtain ⟨vt,hvt,qs,hqs,hsv⟩ := eval_cons_forward hM hw hq hv
    obtain ⟨qt,hqt,_⟩ := hQ.1.2 s' (cons_letter hr)
    have hfat := hEq a s s' fa qs qt hass hfa hqs hqt
    have hty := (hAssoc fa qs vt qt v y (hF.2 a fa hfa) (hQ.2 s qs hqs)
      (eval_range hM hvt) hfat hsv).mpr hy
    exact (eval_cons_iff hM hw hJ hMul hF hQ hr).mpr ⟨vt,hvt,qt,hqt,hty⟩

theorem eval_letterAct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E N J mulN F Q s q r v qs y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN F) (hEq : Equivariant A F Q mulN)
    (hExit : ExitCompatible b E F Q mulN) (hE : MapsTo S D E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hletter : ConstructionProbeLetterAction.LetterAct w D S zero mul A b W E s q r)
    (hv : Eval hM w D S N mulN F Q q v) (hqs : PureKuratowski.PairMember M s qs Q)
    (hy : Product mulN qs v y) : Eval hM w D S N mulN F Q r y := by
  rcases hletter.2.2 with ⟨_,u,z,hquot,hzE,hact⟩ | ⟨_,hcons⟩
  · obtain ⟨uv,huv⟩ := eval_total hM hw hJ hMul hF hQ (word_raw hW hquot.2.1)
    obtain ⟨fb,hfb,_⟩ := hF.1.2 b hb
    obtain ⟨fz,hfz,_⟩ := hF.1.2 z (hE.2 s z hzE)
    obtain ⟨bv,_,hbv⟩ := projected hM hJ hMul (hF.2 b fb hfb) (eval_range hM huv)
    have hqv := eval_oldAct hM hw hz hzw hJ hMul hF hQ hAssoc hPres hEq hquot.2.2 huv hfb hbv
    have he := eval_unique hM hw hJ hMul hF hQ hqv hv
    subst bv
    have hsfz := hExit s z qs fb fz hzE hqs hfb hfz
    have hzy := (hAssoc qs fb uv fz v y (hQ.2 s qs hqs) (hF.2 b fb hfb)
      (eval_range hM huv) hsfz hbv).mpr hy
    exact eval_oldAct hM hw hz hzw hJ hMul hF hQ hAssoc hPres hEq hact huv hfz hzy
  · exact (eval_cons_iff hM hw hJ hMul hF hQ hcons).mpr ⟨v,hv,qs,hqs,hy⟩

def multiplicative {m : Nat} (w D S zero mul A b W E N mulN F Q q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeEvaluationSyntax.eval
    w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ
    b.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ
    4 3) (.imp (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 2) (.imp
    (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 4 1) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ 2 1 0))
    (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ
    S.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ 3 0))))))))))

theorem multiplicative_freeClosed {m : Nat} (w D S zero mul A b W E N mulN F Q q : Fin m) :
    (multiplicative w D S zero mul A b W E N mulN F Q q).FreeClosed := by
  simp -implicitDefEqProofs [multiplicative,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeEvaluationSyntax.eval_freeClosed,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem multiplicative_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E N mulN F Q q : Fin m) :
    Project.Formula.satisfies env (multiplicative w D S zero mul A b W E N mulN F Q q) ↔
      ∀ input y fq fi fy,
        ConstructionProbeEvaluation.Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
          (env.bound mul) (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound q) input y →
        Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound N) (env.bound mulN) (env.bound F) (env.bound Q) (env.bound q) fq →
        Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound N) (env.bound mulN) (env.bound F) (env.bound Q) input fi →
        Product (env.bound mulN) fq fi fy →
        Eval hM (env.bound w) (env.bound D) (env.bound S) (env.bound N) (env.bound mulN) (env.bound F) (env.bound Q) y fy := by
  simp only [multiplicative,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),
    ConstructionProbeEvaluationSyntax.eval_semantics hM,ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

/-- The source Raw induction, using the existing pure-formula internal eliminator. -/
theorem eval_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E N J mulN F Q q input y fq fi fy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN F) (hEq : Equivariant A F Q mulN)
    (hExit : ExitCompatible b E F Q mulN) (hE : MapsTo S D E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hSource : ConstructionProbeEvaluation.Eval hM w D S zero mul A b W E q input y)
    (hq : Eval hM w D S N mulN F Q q fq) (hi : Eval hM w D S N mulN F Q input fi)
    (hp : Product mulN fq fi fy) : Eval hM w D S N mulN F Q y fy := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul (Fin.cases A
      (Fin.cases b (Fin.cases W (Fin.cases E (Fin.cases N (Fin.cases mulN (Fin.cases F (fun _ => Q)))))))))))),
    free := fun _ => w }
  let p : Project.UnarySchema 13 := {
    body := multiplicative 1 2 3 4 5 6 7 8 9 10 11 12 13 0
    freeClosed := multiplicative_freeClosed _ _ _ _ _ _ _ _ _ _ _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ∀ input y fq fi fy, ConstructionProbeEvaluation.Eval hM w D S zero mul A b W E q input y →
        Eval hM w D S N mulN F Q q fq → Eval hM w D S N mulN F Q input fi →
        Product mulN fq fi fy → Eval hM w D S N mulN F Q y fy :=
    multiplicative_semantics hM (env.push q) 1 2 3 4 5 6 7 8 9 10 11 12 13 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro input y fq fi fy hSource hq hi hp
    exact eval_oldAct hM hw hz hzw hJ hMul hF hQ hAssoc hPres hEq
      (ConstructionProbeEvaluation.eval_old_forward hM hw hz hOld hSource) hi
      (eval_old_forward hM hw hz hOld hq) hp) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro input y fq fi fy hSource hq hi hp
    obtain ⟨vt,hEt,hLetter⟩ := ConstructionProbeEvaluation.eval_cons_forward hM hw hCons hSource
    obtain ⟨ft,hHt,qs,hqs,hqprod⟩ := eval_cons_forward hM hw hCons hq
    obtain ⟨tv,_,hprod⟩ := projected hM hJ hMul (eval_range hM hHt) (eval_range hM hi)
    have hHvt := (he t).mp ih input vt ft fi tv hEt hHt hi hprod
    have hps := (hAssoc qs ft fi fq tv fy (hQ.2 s qs hqs) (eval_range hM hHt)
      (eval_range hM hi) hqprod hprod).mp hp
    exact eval_letterAct hM hw hz hzw hJ hMul hF hQ hAssoc hPres hEq hExit hE hW hb hLetter hHvt hqs hps)
  exact (he q).mp (hAll q (ConstructionProbeEvaluation.eval_raw hM hSource)) input y fq fi fy hSource hq hi hp

def BasicLiftLaws (zero D G mulN unit eN F L : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M unit eN L ∧ PreservesProducts G mulN L ∧
  (∀ x q y, Old zero D x q → (PureKuratowski.PairMember M q y L ↔ PureKuratowski.PairMember M x y F))

def LiftLaws (zero D G mulN unit eN F Q K L : M.Carrier .set) : Prop :=
  BasicLiftLaws zero D G mulN unit eN F L ∧
  (∀ s gen y, PureKuratowski.PairMember M s gen K →
    (PureKuratowski.PairMember M gen y L ↔ PureKuratowski.PairMember M s y Q))

theorem basic_lift_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e unit G L N J mulN eN F Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hAssoc : Associative N mulN)
    (hPres : PreservesProducts mul mulN F) (hEq : Equivariant A F Q mulN)
    (hExit : ExitCompatible b E F Q mulN) (hE : MapsTo S D E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hOne : PureKuratowski.PairMember M e eN F)
    (hG : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hL : LiftGraph hM w D S N mulN F Q W L) : BasicLiftLaws zero D G mulN unit eN F L := by
  refine ⟨?_,?_,?_⟩
  · exact (hL unit eN).mpr ⟨ConstructionProbeOldEmbedding.old_word hM hz hzw hW hUnit,
      (eval_old_iff hM hw hz hzw hJ hMul hF hQ hUnit).mpr hOne⟩
  · intro q input y fq fi fy hp hq hi hy
    have hqv := ((hL q fq).mp hq).2
    have hiv := ((hL input fi).mp hi).2
    obtain ⟨z,_,hzprod⟩ := projected hM hJ hMul (eval_range hM hqv) (eval_range hM hiv)
    have hzEval := eval_mul hM hw hz hzw hJ hMul hF hQ hAssoc hPres hEq hExit hE hW hb
      ((hG q input y).mp hp).2 hqv hiv hzprod
    have he := eval_unique hM hw hJ hMul hF hQ hzEval ((hL y fy).mp hy).2
    exact he ▸ hzprod
  · intro x q y hOld
    rw [hL q y,eval_old_iff hM hw hz hzw hJ hMul hF hQ hOld]
    exact and_iff_right (ConstructionProbeOldEmbedding.old_word hM hz hzw hW hOld)

theorem lift_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e unit G K L N J mulN eN F Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ i, ¬ (Project.FirstOrderSemantics.reduct M).mem i zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : Representatives N N J) (hMul : MapsTo J N mulN) (hF : MapsTo D N F) (hQ : MapsTo S N Q)
    (hUnitN : Unit N mulN eN) (hAssoc : Associative N mulN)
    (hPres : PreservesProducts mul mulN F) (hEq : Equivariant A F Q mulN)
    (hExit : ExitCompatible b E F Q mulN) (hE : MapsTo S D E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hOne : PureKuratowski.PairMember M e eN F)
    (hG : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGen : ConstructionProbeGenerator.GeneratorGraph w D S unit K)
    (hL : LiftGraph hM w D S N mulN F Q W L) : LiftLaws zero D G mulN unit eN F Q K L := by
  refine ⟨basic_lift_laws hM hw hz hzw hJ hMul hF hQ hAssoc hPres hEq hExit hE hW hb hUnit hOne hG hL,?_⟩
  intro s gen y hgen
  have hcons := (hGen s gen).mp hgen
  constructor
  · intro hy
    obtain ⟨uv,huv,qs,hqs,hprod⟩ := eval_cons_forward hM hw hcons ((hL gen y).mp hy).2
    have he := ForcingConditionGraphs.function_unique hF.1 (eval_old_forward hM hw hz hUnit huv) hOne
    subst uv
    have he := ((hUnitN.2 qs (hQ.2 s qs hqs) y).2).mp hprod
    exact he.symm ▸ hqs
  · intro hy
    exact (hL gen y).mpr ⟨hK.2 s gen hgen,(eval_cons_iff hM hw hJ hMul hF hQ hcons).mpr
      ⟨eN,(eval_old_iff hM hw hz hzw hJ hMul hF hQ hUnit).mpr hOne,
        y,hy,((hUnitN.2 y (hQ.2 s y hy) y).2).mpr rfl⟩⟩

end PPAC.Migration.ConstructionProbeLiftHom
