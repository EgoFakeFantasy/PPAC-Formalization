/- Distribution and positive affine scaling consumed by source same-head
margin. Reuse actual cut difference/sum/positive-product laws; no field or
additional inverse/associativity infrastructure is constructed. -/
import PPAC.Migration.ConstructionFractionProductArithmetic
import PPAC.Migration.ConstructionCutProduct
import PPAC.Migration.ConstructionProbeIntervals

namespace PPAC.Migration.ConstructionCutProductArithmetic
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionCutProduct (Value)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Rounded input cuts contain the exact product of any two members. -/
theorem point_mem (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q a b c q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Value hM w Q a b c)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q a)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r b)
    (hs : ConstructionFractionProduct.Product hM w q r s) :
    (Project.FirstOrderSemantics.reduct M).mem s c := by
  obtain ⟨q',hq',hqq'⟩ := ha.2.2.1 q hq
  obtain ⟨r',hr',hrr'⟩ := hb.2.2.1 r hr
  have hQ0 := (hQ q).mp (ha.1 q hq)
  have hQ1 := (hQ q').mp (ha.1 q' hq')
  have hR1 := (hQ r').mp (hb.1 r' hr')
  obtain ⟨mid,hMid⟩ := ConstructionFractionProduct.exists_product hM hw hQ0 hR1
  obtain ⟨out,hOut⟩ := ConstructionFractionProduct.exists_product hM hw hQ1 hR1
  obtain ⟨n,d,hRCoord⟩ := hR1
  have hStrict := ConstructionFractionProductArithmetic.positive_product_lt hM hw hMid hOut hRCoord
    (ConstructionFractionProduct.positive_numerator hM hw hRCoord hrr') hqq'
  have hLe := ConstructionFractionProduct.product_left_mono hM hw
    (ConstructionFractionProduct.product_comm hM hw hs)
    (ConstructionFractionProduct.product_comm hM hw hMid) hrr'.1
  exact (hc s).mpr ⟨(hQ s).mpr (ConstructionFractionProduct.product_range hs),q',r',out,hq',hr',hOut,
    le_lt_trans hM hw hLe hStrict⟩

/-- Exact left distribution on arbitrary internal nonnegative cuts, including zero. -/
theorem distrib (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q a b c bc ab ac abc : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hBC : SumCut hM w Q b c bc) (hAB : Value hM w Q a b ab)
    (hAC : Value hM w Q a c ac) (hABC : Value hM w Q a bc abc) : SumCut hM w Q ab ac abc := by
  intro p
  constructor
  · intro hp
    obtain ⟨hpQ,q,r,out,hqa,hrbc,hProd,hpOut⟩ := (hABC p).mp hp
    refine ⟨hpQ,?_⟩
    rcases ((hBC r).mp hrbc).2 with hrb | hrc | ⟨x,y,xy,hxb,hyc,hXY,hRXY⟩
    · exact Or.inl ((hAB p).mpr ⟨hpQ,q,r,out,hqa,hrb,hProd,hpOut⟩)
    · exact Or.inr (Or.inl ((hAC p).mpr ⟨hpQ,q,r,out,hqa,hrc,hProd,hpOut⟩))
    · have hqF := (hQ q).mp (ha.1 q hqa)
      obtain ⟨u,hU⟩ := ConstructionFractionProduct.exists_product hM hw hqF ((hQ x).mp (hb.1 x hxb))
      obtain ⟨v,hV⟩ := ConstructionFractionProduct.exists_product hM hw hqF ((hQ y).mp (hc.1 y hyc))
      obtain ⟨qxy,hQXY⟩ := ConstructionFractionProduct.exists_product hM hw hqF (ConstructionCutAssociativity.sum_fraction hXY)
      obtain ⟨uv,hUV⟩ := ConstructionFractionAddition.sum_exists hM hw
        (ConstructionFractionProduct.product_range hU) (ConstructionFractionProduct.product_range hV)
      have hOutLe := ConstructionFractionProduct.product_left_mono hM hw
        (ConstructionFractionProduct.product_comm hM hw hProd)
        (ConstructionFractionProduct.product_comm hM hw hQXY) hRXY
      have hEq := ConstructionFractionProductArithmetic.fraction_distrib hM hw hXY hQXY hU hV hUV
      exact Or.inr (Or.inr ⟨u,v,uv,point_mem hM hw hQ ha hb hAB hqa hxb hU,
        point_mem hM hw hQ ha hc hAC hqa hyc hV,hUV,
        le_trans hM hw hpOut.1 (le_trans hM hw hOutLe hEq.1)⟩)
  · rintro ⟨hpQ,hp⟩
    rcases hp with hp | hp | ⟨u,v,uv,hu,hv,hUV,hpUV⟩
    · exact ConstructionCutProduct.value_mono hAB hABC (fun _ h => h)
        (ConstructionCutArithmetic.sum_contains hb hc hBC).1 p hp
    · exact ConstructionCutProduct.value_mono hAC hABC (fun _ h => h)
        (ConstructionCutArithmetic.sum_contains hb hc hBC).2 p hp
    · obtain ⟨huQ,q1,r1,s1,hq1,hr1,hP1,huS1⟩ := (hAB u).mp hu
      obtain ⟨hvQ,q2,r2,s2,hq2,hr2,hP2,hvS2⟩ := (hAC v).mp hv
      have hCommon : ∃ q t1 t2, (Project.FirstOrderSemantics.reduct M).mem q a ∧
          ConstructionFractionProduct.Product hM w q r1 t1 ∧ ConstructionFractionProduct.Product hM w q r2 t2 ∧
          Lt hM w u t1 ∧ Lt hM w v t2 := by
        rcases le_total hM hw ((hQ q1).mp (ha.1 q1 hq1)) ((hQ q2).mp (ha.1 q2 hq2)) with h12 | h21
        · obtain ⟨t1,hT1⟩ := ConstructionFractionProduct.exists_product hM hw
            ((hQ q2).mp (ha.1 q2 hq2)) ((hQ r1).mp (hb.1 r1 hr1))
          exact ⟨q2,t1,s2,hq2,hT1,hP2,lt_le_trans hM hw huS1
            (ConstructionFractionProduct.product_left_mono hM hw hP1 hT1 h12),hvS2⟩
        · obtain ⟨t2,hT2⟩ := ConstructionFractionProduct.exists_product hM hw
            ((hQ q1).mp (ha.1 q1 hq1)) ((hQ r2).mp (hc.1 r2 hr2))
          exact ⟨q1,s1,t2,hq1,hP1,hT2,huS1,lt_le_trans hM hw hvS2
            (ConstructionFractionProduct.product_left_mono hM hw hP2 hT2 h21)⟩
      obtain ⟨q,t1,t2,hqa,hT1,hT2,huT1,hvT2⟩ := hCommon
      obtain ⟨rs,hRS⟩ := ConstructionFractionAddition.sum_exists hM hw
        ((hQ r1).mp (hb.1 r1 hr1)) ((hQ r2).mp (hc.1 r2 hr2))
      have hrsBC := (hBC rs).mpr ⟨(hQ rs).mpr (ConstructionCutAssociativity.sum_fraction hRS),
        Or.inr (Or.inr ⟨r1,r2,rs,hr1,hr2,hRS,le_refl hM hw (ConstructionCutAssociativity.sum_fraction hRS)⟩)⟩
      obtain ⟨out,hOut⟩ := ConstructionFractionProduct.exists_product hM hw ((hQ q).mp (ha.1 q hqa))
        (ConstructionCutAssociativity.sum_fraction hRS)
      obtain ⟨target,hTarget⟩ := ConstructionFractionAddition.sum_exists hM hw
        (ConstructionFractionProduct.product_range hT1) (ConstructionFractionProduct.product_range hT2)
      obtain ⟨mid,hMid⟩ := ConstructionFractionAddition.sum_exists hM hw
        (ConstructionFractionProduct.product_range hT1) ((hQ v).mp hvQ)
      have hUVMid := (ConstructionFractionAddition.sum_right_lt_iff hM hw hUV hMid).mpr huT1
      have hMidTarget := ConstructionFractionAddition.sum_mono hM hw hMid hTarget
        (le_refl hM hw (ConstructionFractionProduct.product_range hT1)) hvT2.1
      have hEq := ConstructionFractionProductArithmetic.fraction_distrib hM hw hRS hOut hT1 hT2 hTarget
      have hpOut := lt_le_trans hM hw (le_lt_trans hM hw hpUV (lt_le_trans hM hw hUVMid hMidTarget)) hEq.2
      exact (hABC p).mpr ⟨hpQ,q,rs,out,hqa,hrsBC,hOut,hpOut⟩

/-- Strict positive scaling follows from the EXISTING difference and positive
product laws once distribution is proved; no separate Archimedean proof. -/
theorem positive_strict (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q a b c ab ac : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (haN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a)
    (hBC : Strict b c) (hAB : Value hM w Q a b ab) (hAC : Value hM w Q a c ac) : Strict ab ac := by
  obtain ⟨gap,hGap,_,hGapSum,_,hGapPositive⟩ := ConstructionCutDifference.exists_difference hM hw hQ hb hc hBC.1
  obtain ⟨ag,hAG,hProdGap⟩ := ConstructionCutProduct.exists_product hM hw hQ ha hGap
  have hAGPositive := ConstructionCutProduct.value_nonempty hM hw hQ ha hGap hProdGap haN (hGapPositive hBC.2)
  have hDistrib := distrib hM hw hQ ha hb hGap hGapSum hAB hProdGap hAC
  exact ConstructionProbeIntervals.sum_positive hM hw hQ (ConstructionCutProduct.value_cut hM hw hQ ha hb hAB)
    hAG hAGPositive hDistrib

/-- The exact affine strict-gap calculation used in source same-head margin. -/
theorem affine_strict (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q scale offset a b c suffixSum da db dc x y marginSum : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hScale : Cut hM w Q scale) (hOffset : Cut hM w Q offset)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hScaleN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p scale)
    (hSuffixSum : SumCut hM w Q a c suffixSum) (hStrict : Strict suffixSum b)
    (hDA : Value hM w Q scale a da) (hDB : Value hM w Q scale b db) (hDC : Value hM w Q scale c dc)
    (hx : SumCut hM w Q offset da x) (hy : SumCut hM w Q offset db y)
    (hMarginSum : SumCut hM w Q x dc marginSum) : Strict marginSum y := by
  have hSuffixCut := ConstructionCutAssociativity.sum_is_cut hM hw hQ ha hc hSuffixSum
  obtain ⟨ds,hDS,hDSProd⟩ := ConstructionCutProduct.exists_product hM hw hQ hScale hSuffixCut
  have hDistrib := distrib hM hw hQ hScale ha hc hSuffixSum hDA hDC hDSProd
  have hScaledStrict := positive_strict hM hw hQ hScale hSuffixCut hb hScaleN hStrict hDSProd hDB
  have hDAcut := ConstructionCutProduct.value_cut hM hw hQ hScale ha hDA
  have hDCcut := ConstructionCutProduct.value_cut hM hw hQ hScale hc hDC
  have hDBcut := ConstructionCutProduct.value_cut hM hw hQ hScale hb hDB
  have hReassoc := (ConstructionProbeIntervals.reassociate hM hw hQ hOffset hDAcut hDCcut hx hDistrib).mp hMarginSum
  exact (ConstructionCutDifference.sum_strict_iff hM hw hQ hDS hDBcut hOffset
    (ConstructionCutArithmetic.sum_comm hM hw hReassoc) (ConstructionCutArithmetic.sum_comm hM hw hy)).mpr hScaledStrict

end PPAC.Migration.ConstructionCutProductArithmetic
