/- Pinned ProbeWords.Word generators, their reductions and exact old gate.
Use the existing actual Word multiplication and native function graph constructor. -/
import PPAC.Migration.ConstructionProbeOldEmbedding

namespace PPAC.Migration.ConstructionProbeGenerator
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeEvaluation
open ConstructionProbeOldEmbedding ConstructionProbeWordMonoid
open ConstructionProbeLetterAction (LetterAct letterAct_oldAct_b)
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeAlphabet (Alphabet)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem not_headDiv_unit {w D S zero mul A b e unit : M.Carrier .set}
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hc : Conical D mul e) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hne : b ≠ e) (hUnit : Old zero D e unit) : ¬ HeadDiv w D S zero mul A b unit := by
  intro h
  obtain ⟨z,hzD,hprod⟩ := (headDiv_old_iff hz hUnit).mp h
  exact hne (hc b z hb hzD hprod).1

theorem generator_word (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W e unit s q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hc : Conical D mul e) (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hUnit : Old zero D e unit) (hq : Cons w D S s unit q) :
    (Project.FirstOrderSemantics.reduct M).mem q W :=
  (hW q).mpr ((ConstructionProbeReduced.reduced_cons hM hw hz hzw hq).mpr
    ⟨ConstructionProbeReduced.reduced_old hM hz hzw hUnit,not_headDiv_unit hz hc hb hne hUnit⟩)

def GeneratorGraph (w D S unit K : M.Carrier .set) : Prop := ∀ s q,
  PureKuratowski.PairMember M s q K ↔ Cons w D S s unit q

theorem exists_generator_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W e unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hc : Conical D mul e) (hW : WordCarrier w D S mul A b W)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hUnit : Old zero D e unit) : ∃ K, MapsTo S W K ∧ GeneratorGraph w D S unit K := by
  let schema : Project.BinarySchema 4 := {
    body := cons 2 3 4 1 5 0
    freeClosed := cons_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases S (fun _ => unit))), free := fun _ => w }
  have he (s q : M.Carrier .set) : schema.denote env s q ↔ Cons w D S s unit q :=
    cons_semantics hM ((env.push s).push q) 2 3 4 1 5 0
  obtain ⟨K,hK,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := S) (target := W) (by
      intro s hs
      obtain ⟨q,hq⟩ := exists_cons hM hw hs (old_raw hM hz hzw hUnit)
      exact ⟨q,(he s q).mpr hq⟩) (by
      intro s _ q r hq hr
      exact cons_unique hM hw ((he s q).mp hq) ((he s r).mp hr)) (by
      intro s q _ hq
      exact generator_word hM hw hz hzw hc hW hb hne hUnit ((he s q).mp hq))
  refine ⟨K,(ForcingSupportSize.native_mapsTo hM S W K).mpr hK,fun s q => ?_⟩
  exact (hgraph s q).trans ⟨fun h => (he s q).mp h.2,fun h => ⟨cons_letter h,(he s q).mpr h⟩⟩

theorem generator_mul_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen input y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hgen : Cons w D S s unit gen) (hgW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hi : (Project.FirstOrderSemantics.reduct M).mem input W) :
    Product G gen input y ↔ LetterAct w D S zero mul A b W E s input y := by
  constructor
  · intro hp
    obtain ⟨v,hv,hletter⟩ := eval_cons_forward hM hw hgen ((hG gen input y).mp hp).2
    have he := oldAct_unique hM hw hz hm hAlpha.2.1 (eval_old_forward hM hw hz hUnit hv)
      (oldAct_one hM hw hz hzw hm hAlpha.2.2.1 (word_raw hW hi))
    subst v
    exact hletter
  · intro hletter
    exact (hG gen input y).mpr ⟨hgW,(eval_cons_iff hM hw hz hzw hm hAlpha hW hb hgen).mpr
      ⟨input,(eval_old_iff hM hw hz hzw hm hAlpha hW hb hUnit hi).mpr
        (oldAct_one hM hw hz hzw hm hAlpha.2.2.1 (word_raw hW hi)),hletter⟩⟩

theorem generator_mul_b (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen z ob oz : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hgen : Cons w D S s unit gen) (hgW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hzE : PureKuratowski.PairMember M s z E) (hob : Old zero D b ob) (hoz : Old zero D z oz) :
    Product G gen ob oz := by
  have hbAct : OldAct w D S zero mul A b unit ob :=
    (oldAct_old_iff hz hUnit).mpr ⟨hb,b,((hm.1.2 b hb b).2).mpr rfl,hob⟩
  have hzAct : OldAct w D S zero mul A z unit oz :=
    (oldAct_old_iff hz hUnit).mpr ⟨hoz.1,z,((hm.1.2 z hoz.1 z).2).mpr rfl,hoz⟩
  exact (generator_mul_iff hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgW
    (old_word hM hz hzw hW hob)).mpr
      ((letterAct_oldAct_b hM hw hz hzw hm hAlpha hW (cons_letter hgen)
        (old_word hM hz hzw hW hUnit) hbAct hzE).mpr hzAct)

theorem generator_mul_of_not_headDiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen input y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hgen : Cons w D S s unit gen) (hgW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hi : (Project.FirstOrderSemantics.reduct M).mem input W)
    (hnot : ¬ HeadDiv w D S zero mul A b input) (hy : Cons w D S s input y) :
    Product G gen input y :=
  (generator_mul_iff hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgW hi).mpr
    ⟨cons_letter hgen,hi,Or.inr ⟨hnot,hy⟩⟩

/-- The source calculation used by Path.probe_transition. -/
theorem old_mul_generator (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit x ox s t gs gt : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hx : Old zero D x ox) (hgs : Cons w D S s unit gs) (hgt : Cons w D S t unit gt)
    (hsW : (Project.FirstOrderSemantics.reduct M).mem gs W) (hact : Product A x s t) :
    Product G ox gs gt :=
  (old_mul_iff hM hw hz hzw hm hAlpha hW hb hG hx hsW).mpr ⟨hx.1,Or.inr ⟨s,unit,t,hgs,hact,hgt⟩⟩

theorem exit_dvd_of_letterAct_eq_old {w D S zero mul A b W E e I s z input y oy : M.Carrier .set}
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hAlpha : Alphabet D mul e S I A E)
    (hzE : PureKuratowski.PairMember M s z E) (hy : Old zero D y oy)
    (hletter : LetterAct w D S zero mul A b W E s input oy) : Divides D mul z y := by
  rcases hletter.2.2 with ⟨_,v,z',_,hzE',hact⟩ | ⟨_,hcons⟩
  · have he := ForcingConditionGraphs.function_unique hAlpha.2.2.2.1.1 hzE' hzE
    subst z'
    obtain ⟨_,t,ht,hprod⟩ := (oldAct_eq_old_iff hz hy).mp hact
    exact ⟨t,ht.1,hprod⟩
  · exact (old_ne_cons hz hy hcons).elim

theorem generator_dvd_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit s gen z y oy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hgen : Cons w D S s unit gen) (hgW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hzE : PureKuratowski.PairMember M s z E) (hy : Old zero D y oy) :
    Divides W G gen oy ↔ Divides D mul z y := by
  constructor
  · rintro ⟨input,hi,hprod⟩
    exact exit_dvd_of_letterAct_eq_old hz hAlpha hzE hy
      ((generator_mul_iff hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgW hi).mp hprod)
  · rintro ⟨t,ht,hty⟩
    obtain ⟨r,hr,hbr⟩ := (hm.2.1 b hb).1 t ht
    obtain ⟨ot,hot⟩ := exists_old hM ht (zero := zero)
    obtain ⟨orw,hor⟩ := exists_old hM hr (zero := zero)
    have hzr := hAlpha.2.2.2.1.2 s z hzE
    have hbt : OldAct w D S zero mul A b ot orw := (oldAct_old_iff hz hot).mpr ⟨hb,r,hbr,hor⟩
    have hzt : OldAct w D S zero mul A z ot oy := (oldAct_old_iff hz hot).mpr ⟨hzr,y,hty,hy⟩
    have hletter := (letterAct_oldAct_b hM hw hz hzw hm hAlpha hW (cons_letter hgen)
      (old_word hM hz hzw hW hot) hbt hzE).mpr hzt
    exact ⟨orw,old_word hM hz hzw hW hor,
      (generator_mul_iff hM hw hz hzw hm hAlpha hW hb hUnit hG hgen hgW
        (old_word hM hz hzw hW hor)).mpr hletter⟩

end PPAC.Migration.ConstructionProbeGenerator
