/- Connect the actual /4 inverse-image graph to the actual addition graph.
Pinned consumer: ProbeMargins.exists_letter_interval's delta = gap / 4.
Use native successor arithmetic, existing same_den_sum and division order
reflection; no full real-field or general cancellation premise is assumed. -/
import PPAC.Migration.ConstructionCutDivisionSyntax

namespace PPAC.Migration.ConstructionCutQuarterSum
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
open ConstructionFractionScaling (Times)
open ConstructionCutAddition (SumCut)
open ConstructionCutDivision (Value)
open ConstructionBaseWeights (Digits)
open ForcingDiagramOrder (Product)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem two_mul_two (hM : FirstOrder.Theory.Models M nativeZF) {w one two three four : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hf : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three) : Mul hM two two four := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨zero,hz,hOne⟩ := hd.2.2.2.1
  have hAdd : Add hM two one three :=
    (ZF.ordinalAddition_successor_iff hZF I (SetTheory.Structure.IsOrdinal.of_no_members hz) hOne).mpr
      ⟨two,(ZF.ordinalAddition_zero_iff hZF I hz).mpr rfl,hd.2.2.2.2.2⟩
  have hAddFour : Add hM two two four :=
    (ZF.ordinalAddition_successor_iff hZF I (ord one hd.1) hd.2.2.2.2.1).mpr ⟨three,hAdd,hf⟩
  exact (ZF.ordinalMultiplication_successor_iff hZF I (ord two hd.2.1) (ord one hd.1) hd.2.2.2.2.1).mpr
    ⟨two,(mul_one hM hw hd.2.1 hd.1 hd.2.2.2.1).1,hAddFour⟩

theorem twice_sum_equiv (hM : FirstOrder.Theory.Models M nativeZF) {w one two three q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hr : Times hM w two q r) (hs : Sum hM w q q s) : Le hM w s r ∧ Le hM w r s := by
  obtain ⟨a,b,an,hq,han,hr⟩ := hr
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨previous,hp,hAdd⟩ := (ZF.ordinalMultiplication_successor_iff hZF (KuratowskiZF.interpretation hM)
    (ord a hq.1) (ord one hd.1) hd.2.2.2.2.1).mp han
  have he := ZF.ordinalMultiplication_one_right hZF (KuratowskiZF.interpretation hM) (ord a hq.1) hd.2.2.2.1 hp
  subst previous
  exact ConstructionFractionDifference.same_den_sum hM hw hq hq hr hAdd hs

theorem twice_ge (hM : FirstOrder.Theory.Models M nativeZF) {w one two three q r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hd : Digits w one two three)
    (hr : Times hM w two q r) : Le hM w q r := by
  have hrCopy := hr
  obtain ⟨a,b,_,hq,_,_⟩ := hrCopy
  obtain ⟨s,hs⟩ := ConstructionFractionAddition.sum_exists hM hw ⟨a,b,hq⟩ ⟨a,b,hq⟩
  exact le_trans hM hw (ConstructionBasePointBound.sum_left_le hM hw hs) (twice_sum_equiv hM hw hd hr hs).1

theorem times_comp (hM : FirstOrder.Theory.Models M nativeZF) {w n m k q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hm : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hk : Mul hM n m k) (hr : Times hM w n q r) (hs : Times hM w m r s) : Times hM w k q s := by
  obtain ⟨a,b,an,hq,han,hr⟩ := hr
  obtain ⟨a',b',anm,hr',hanm,hs⟩ := hs
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr.2.2.2 hr'.2.2.2
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  obtain ⟨ak,_,hak⟩ := mul_exists hM hw hq.1 (mul_range hM hw hn hm hk)
  have he := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord a hq.1) (ord n hn) (ord m hm) han hk hak hanm
  exact ⟨a,b,anm,hq,he ▸ hak,hs⟩

theorem value_comp (hM : FirstOrder.Theory.Models M nativeZF) {w Q n m k a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hm : (Project.FirstOrderSemantics.reduct M).mem m w)
    (hk : Mul hM n m k) (hb : Value hM w Q m a b) (hc : Value hM w Q n b c) : Value hM w Q k a c := by
  intro q
  constructor
  · intro hq
    obtain ⟨hqQ,r,hr,hrb⟩ := (hc q).mp hq
    obtain ⟨_,s,hs,hsa⟩ := (hb r).mp hrb
    exact ⟨hqQ,s,times_comp hM hw hn hm hk hr hs,hsa⟩
  · rintro ⟨hqQ,s,hs,hsa⟩
    obtain ⟨r,hr⟩ := ConstructionFractionScaling.exists_times hM hw hn ((hQ q).mp hqQ)
    obtain ⟨t,ht⟩ := ConstructionFractionScaling.exists_times hM hw hm (ConstructionFractionScaling.times_range hr)
    have he := ConstructionFractionScaling.times_unique hM hw (mul_range hM hw hn hm hk)
      (times_comp hM hw hn hm hk hr ht) hs
    have hta := he.symm ▸ hsa
    have hrb := (hb r).mpr ⟨(hQ r).mpr (ConstructionFractionScaling.times_range hr),t,ht,hta⟩
    exact (hc q).mpr ⟨hqQ,r,hr,hrb⟩

/-- The existing double sum really is multiplication by two on all cuts. -/
theorem double_value (hM : FirstOrder.Theory.Models M nativeZF) {w Q one two three c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hd : Digits w one two three) (hc : Cut hM w Q c) (hs : SumCut hM w Q c c d) : Value hM w Q two d c := by
  intro q
  constructor
  · intro hqc
    have hqQ := hc.1 q hqc
    obtain ⟨r,hr⟩ := ConstructionFractionScaling.exists_times hM hw hd.2.1 ((hQ q).mp hqQ)
    obtain ⟨s,hSum⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ q).mp hqQ) ((hQ q).mp hqQ)
    have he := twice_sum_equiv hM hw hd hr hSum
    exact ⟨hqQ,r,hr,(hs r).mpr ⟨(hQ r).mpr (ConstructionFractionScaling.times_range hr),
      Or.inr (Or.inr ⟨q,q,s,hqc,hqc,hSum,he.2⟩)⟩⟩
  · rintro ⟨hqQ,r,hr,hrd⟩
    obtain ⟨_,hmem⟩ := (hs r).mp hrd
    rcases hmem with hrc | hrc | ⟨u,v,s,hu,hv,hSum,hrs⟩
    · exact hc.2.1 q r hrc (twice_ge hM hw hd hr)
    · exact hc.2.1 q r hrc (twice_ge hM hw hd hr)
    · have useMax (m : M.Carrier .set) (hm : (Project.FirstOrderSemantics.reduct M).mem m c)
          (hum : Le hM w u m) (hvm : Le hM w v m) : (Project.FirstOrderSemantics.reduct M).mem q c := by
        have hmQ := hc.1 m hm
        obtain ⟨s',hSum'⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ m).mp hmQ) ((hQ m).mp hmQ)
        obtain ⟨t,ht⟩ := ConstructionFractionScaling.exists_times hM hw hd.2.1 ((hQ m).mp hmQ)
        have hst := le_trans hM hw (ConstructionFractionAddition.sum_mono hM hw hSum hSum' hum hvm)
          (twice_sum_equiv hM hw hd ht hSum').1
        have hqt := (ConstructionFractionScaling.order_iff hM hw hd.2.1 ⟨one,hd.2.2.2.2.1.predecessor_mem⟩ hr ht).mp
          (le_trans hM hw hrs hst)
        exact hc.2.1 q m hm hqt
      rcases le_total hM hw ((hQ u).mp (hc.1 u hu)) ((hQ v).mp (hc.1 v hv)) with huv | hvu
      · exact useMax v hv huv (le_refl hM hw ((hQ v).mp (hc.1 v hv)))
      · exact useMax u hu (le_refl hM hw ((hQ u).mp (hc.1 u hu))) hvu

theorem quarter_fourfold (hM : FirstOrder.Theory.Models M nativeZF) {w Q one two three four a c d e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hd : Digits w one two three) (hf : (Project.FirstOrderSemantics.reduct M).SuccessorOf four three)
    (hfw : (Project.FirstOrderSemantics.reduct M).mem four w)
    (ha : Cut hM w Q a) (hc : Cut hM w Q c) (hdCut : Cut hM w Q d) (he : Cut hM w Q e)
    (hquarter : Value hM w Q four a c) (hDouble : SumCut hM w Q c c d) (hFour : SumCut hM w Q d d e) : e = a := by
  have hdc := double_value hM hw hQ hd hc hDouble
  have hed := double_value hM hw hQ hd hdCut hFour
  have hec := value_comp hM hw hQ hd.2.1 hd.2.1 (two_mul_two hM hw hd hf) hed hdc
  have hae := (ConstructionCutDivision.order_iff hw hQ hfw ⟨three,hf.predecessor_mem⟩ ha he hquarter hec).mp (fun _ h => h)
  have hea := (ConstructionCutDivision.order_iff hw hQ hfw ⟨three,hf.predecessor_mem⟩ he ha hec hquarter).mp (fun _ h => h)
  exact (ModelTransfer.extensionality hM).eq_of_same_members e a (fun p => ⟨hea p,hae p⟩)

def LinkLaws (R G F : M.Carrier .set) : Prop := ∀ a c, PureKuratowski.PairMember M a c F →
  ∃ d, (Project.FirstOrderSemantics.reduct M).mem d R ∧ Product G c c d ∧ Product G d d a ∧
    ∀ d' e', Product G c c d' → Product G d' d' e' → e' = a

theorem exists_link (hM : FirstOrder.Theory.Models M nativeZF) {w Q R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q) (hR : CutCarrier hM w Q R) :
    ∃ I G one two three four F, ConstructionProbeLetters.Representatives R R I ∧ MapsTo I R G ∧
      ConstructionCutArithmetic.Graph hM w Q R G ∧ ConstructionCutArithmetic.Laws R G ∧ Digits w one two three ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf four three ∧ (Project.FirstOrderSemantics.reduct M).mem four w ∧
      MapsTo R R F ∧ ConstructionCutDivision.Graph hM w Q four R F ∧ ConstructionCutDivision.Laws F ∧ LinkLaws R G F := by
  obtain ⟨I,G,hI,hG,hAdd,hAddLaws⟩ := ConstructionCutArithmetic.exists_graph hM hw hQ hR
  obtain ⟨one,two,three,four,F,hd,hf,hfw,hF,hDiv,hDivLaws⟩ := ConstructionCutDivision.exists_quarter hM hw hQ hR
  refine ⟨I,G,one,two,three,four,F,hI,hG,hAdd,hAddLaws,hd,hf,hfw,hF,hDiv,hDivLaws,?_⟩
  intro a c hfc
  have ha := ((hDiv a c).mp hfc).1
  have hc := hF.2 a c hfc
  obtain ⟨d,hdCut,hDouble⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ((hR c).mp hc) ((hR c).mp hc)
  obtain ⟨e,heCut,hFour⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hdCut hdCut
  have hdR := (hR d).mpr hdCut
  have hcd := (hAdd c c d).mpr ⟨hc,hc,hDouble⟩
  have hda := (hAdd d d e).mpr ⟨hdR,hdR,hFour⟩
  have he := quarter_fourfold hM hw hQ hd hf hfw ((hR a).mp ha) ((hR c).mp hc) hdCut heCut
    ((hDiv a c).mp hfc).2 hDouble hFour
  have hda' : Product G d d a := he ▸ hda
  refine ⟨d,hdR,hcd,hda',?_⟩
  intro d' e' hd' he'
  have heD := ConstructionProbeHomEvaluation.product_unique hM hG hd' hcd
  subst d'
  exact ConstructionProbeHomEvaluation.product_unique hM hG he' hda'

end PPAC.Migration.ConstructionCutQuarterSum
