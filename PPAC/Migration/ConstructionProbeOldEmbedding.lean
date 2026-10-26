/- Pinned ProbeWords.Word.oldHom, factor and divisibility reflection.
The actual set graph is constructed by the existing native function interface. -/
import PPAC.Migration.ConstructionProbeWordMonoidSyntax

namespace PPAC.Migration.ConstructionProbeOldEmbedding
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeEvaluation
open ConstructionProbeWordMonoid
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeAlphabet (Alphabet)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (Injection)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem old_word (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W x q : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hq : Old zero D x q) :
    (Project.FirstOrderSemantics.reduct M).mem q W :=
  (hW q).mpr (ConstructionProbeReduced.reduced_old hM hz hzw hq)

theorem oldAct_eq_old_iff {w D S zero mul A x y input oy : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hy : Old zero D y oy) : OldAct w D S zero mul A x input oy ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧
        ∃ z, Old zero D z input ∧ Product mul x z y := by
  constructor
  · rintro ⟨hx,h⟩
    rcases h with ⟨z,y',hi,hprod,hy'⟩ | ⟨s,t,v,_,_,hcons⟩
    · have he := old_injective hy hy'
      subst y'
      exact ⟨hx,z,hi,hprod⟩
    · exact (old_ne_cons hz hy hcons).elim
  · rintro ⟨hx,z,hi,hprod⟩
    exact ⟨hx,Or.inl ⟨z,y,hi,hprod,hy⟩⟩

theorem old_mul_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G x ox input y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hx : Old zero D x ox) (hi : (Project.FirstOrderSemantics.reduct M).mem input W) :
    Product G ox input y ↔ OldAct w D S zero mul A x input y := by
  rw [hG ox input y,eval_old_iff hM hw hz hzw hm hAlpha hW hb hx hi]
  exact and_iff_right (old_word hM hz hzw hW hx)

theorem old_mul_eq_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G x y ox oy input : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hx : Old zero D x ox) (hy : Old zero D y oy)
    (hi : (Project.FirstOrderSemantics.reduct M).mem input W) :
    Product G ox input oy ↔ ∃ z, Old zero D z input ∧ Product mul x z y := by
  rw [old_mul_iff hM hw hz hzw hm hAlpha hW hb hG hx hi,oldAct_eq_old_iff hz hy]
  exact and_iff_right hx.1

theorem old_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G x y z ox oy oz : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hx : Old zero D x ox) (hy : Old zero D y oy) (hzv : Old zero D z oz)
    (hprod : Product mul x y z) : Product G ox oy oz :=
  (old_mul_eq_old_iff hM hw hz hzw hm hAlpha hW hb hG hx hzv
    (old_word hM hz hzw hW hy)).mpr ⟨y,hy,hprod⟩

theorem old_dvd_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G x y ox oy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hx : Old zero D x ox) (hy : Old zero D y oy) :
    Divides W G ox oy ↔ Divides D mul x y := by
  constructor
  · rintro ⟨input,hi,hprod⟩
    obtain ⟨z,hzv,hprod⟩ := (old_mul_eq_old_iff hM hw hz hzw hm hAlpha hW hb hG hx hy hi).mp hprod
    exact ⟨z,hzv.1,hprod⟩
  · rintro ⟨z,hzv,hprod⟩
    obtain ⟨oz,hoz⟩ := exists_old hM hzv (zero := zero)
    exact ⟨oz,old_word hM hz hzw hW hoz,old_mul hM hw hz hzw hm hAlpha hW hb hG hx hoz hy hprod⟩

theorem old_dvd_iff_headDiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G x ox q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hx : Old zero D x ox) (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    Divides W G ox q ↔ HeadDiv w D S zero mul A x q := by
  rw [ConstructionProbeWord.headDiv_iff hM hw hz hzw hW hx.1 hq]
  constructor
  · rintro ⟨input,hi,hprod⟩
    exact ⟨input,hi,(old_mul_iff hM hw hz hzw hm hAlpha hW hb hG hx hi).mp hprod⟩
  · rintro ⟨input,hi,hact⟩
    exact ⟨input,hi,(old_mul_iff hM hw hz hzw hm hAlpha hW hb hG hx hi).mpr hact⟩

def OldGraph (zero D H : M.Carrier .set) : Prop := ∀ x q,
  PureKuratowski.PairMember M x q H ↔ Old zero D x q

theorem exists_old_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W : M.Carrier .set}
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) : ∃ H, Injection D W H ∧ OldGraph zero D H := by
  let schema : Project.BinarySchema 2 := {
    body := old 2 3 1 0
    freeClosed := old_freeClosed _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases zero (fun _ => D), free := fun _ => zero }
  have he (x q : M.Carrier .set) : schema.denote env x q ↔ Old zero D x q :=
    old_semantics hM ((env.push x).push q) 2 3 1 0
  obtain ⟨H,hH,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := D) (target := W) (by
      intro x hx
      obtain ⟨q,hq⟩ := exists_old hM hx (zero := zero)
      exact ⟨q,(he x q).mpr hq⟩) (by
      intro x _ q r hq hr
      exact old_unique hM ((he x q).mp hq) ((he x r).mp hr)) (by
      intro x q _ hq
      exact old_word hM hz hzw hW ((he x q).mp hq))
  have hg : OldGraph zero D H := by
    intro x q
    exact (hgraph x q).trans ⟨fun h => (he x q).mp h.2,fun h => ⟨h.1,(he x q).mpr h⟩⟩
  refine ⟨H,⟨(ForcingSupportSize.native_mapsTo hM D W H).mpr hH,?_⟩,hg⟩
  intro x y q hx hy
  exact old_injective ((hg x q).mp hx) ((hg y q).mp hy)

theorem exit_ne_one {D mul e S I A E s z : M.Carrier .set}
    (hAlpha : Alphabet D mul e S I A E)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hzE : PureKuratowski.PairMember M s z E) : z ≠ e := by
  intro he
  subst z
  exact hAlpha.2.2.2.2.2 s e hs hzE ⟨s,hs,hAlpha.2.2.1.1 s hs⟩

theorem oldAct_exit_ne_one {w D S zero mul A E e I s z input unit : M.Carrier .set}
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hUnit : Old zero D e unit)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S)
    (hzE : PureKuratowski.PairMember M s z E) :
    ¬ OldAct w D S zero mul A z input unit := by
  intro h
  obtain ⟨hzD,x,hx,hprod⟩ := (oldAct_eq_old_iff hz hUnit).mp h
  exact exit_ne_one hAlpha hs hzE (hc z x hzD hx.1 hprod).1

theorem letterAct_ne_one {w D S zero mul A b W E e I s input unit : M.Carrier .set}
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hUnit : Old zero D e unit) :
    ¬ ConstructionProbeLetterAction.LetterAct w D S zero mul A b W E s input unit := by
  intro h
  rcases h.2.2 with ⟨_,v,z,_,hzE,hact⟩ | ⟨_,hcons⟩
  · exact oldAct_exit_ne_one hz hc hAlpha hUnit h.1 hzE hact
  · exact old_ne_cons hz hUnit hcons

theorem word_conical (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hc : Conical D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G) :
    Conical W G unit := by
  intro q input hq _ hprod
  have heval := ((hG q input unit).mp hprod).2
  rcases cases_raw hM hw hz hzw (word_raw hW hq) with ⟨x,hx⟩ | ⟨s,t,hcons⟩
  · obtain ⟨hxD,z,hzv,hxz⟩ := (oldAct_eq_old_iff hz hUnit).mp (eval_old_forward hM hw hz hx heval)
    obtain ⟨rfl,rfl⟩ := hc x z hxD hzv.1 hxz
    exact ⟨old_unique hM hx hUnit,old_unique hM hzv hUnit⟩
  · obtain ⟨v,_,hletter⟩ := eval_cons_forward hM hw hcons heval
    exact (letterAct_ne_one hz hc hAlpha hUnit hletter).elim

end PPAC.Migration.ConstructionProbeOldEmbedding
