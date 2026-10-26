/- Pinned ProbeMargins.Word.uniform_margin_old_new:343.
Construct the actual max(floor-height(x),scale) witness. Existing interval,
floor, inside-cost, scale-cost and outside-block-factor producers are reused. -/
import PPAC.Migration.ConstructionProbeCostMargins
import PPAC.Migration.ConstructionProbeWeightBounds

namespace PPAC.Migration.ConstructionProbeOldNewMargin
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts ConstructionFractionOrder
open ConstructionCutAddition (SumCut)
open ConstructionCutArithmetic (MaxCut)
open ConstructionProbeIntervals (Strict)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeGates (HeadSome)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeLetterIntervals (UniformAt)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Both literal max branches lie strictly below the new height. -/
theorem bound_below_height (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q hx floor gap delta offset product hy lower bound sum : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hFloor : Cut hM w Q floor) (hGap : Cut hM w Q gap) (hDelta : Cut hM w Q delta)
    (hOffset : Cut hM w Q offset) (hProduct : Cut hM w Q product)
    (hHXFloor : Subset hx floor) (hGapSum : SumCut hM w Q hx gap floor)
    (hLower : SumCut hM w Q floor delta lower) (hLowerOffset : Strict lower offset)
    (hHeight : SumCut hM w Q offset product hy) (hMax : MaxCut gap delta bound)
    (hSum : SumCut hM w Q hx bound sum) : Strict sum hy := by
  have hOffsetLe := (ConstructionCutArithmetic.sum_contains hOffset hProduct hHeight).1
  have hLowerY : Strict lower hy :=
    ⟨fun p hp => hOffsetLe p (hLowerOffset.1 p hp),
      fun h => hLowerOffset.2 (fun p hp => h p (hOffsetLe p hp))⟩
  rcases ConstructionCutArithmetic.max_cases hM hw hQ hGap hDelta hMax with he | he
  · subst bound
    have heSum := ConstructionCutAddition.sum_unique hM hGapSum hSum
    subst sum
    exact ConstructionProbeIntervals.le_strict_trans
      (ConstructionCutArithmetic.sum_contains hFloor hDelta hLower).1 hLowerY
  · subst bound
    exact ConstructionProbeIntervals.le_strict_trans
      (ConstructionCutArithmetic.sum_mono hSum hLower hHXFloor (fun _ h => h)) hLowerY

/-- Source old-to-new margin on the SAME actual Word and mapped weights.
No gap, maximum, margin or missed-cost bound is supplied as an oracle. -/
theorem uniform_margin_old_new (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul S A b zero W Emb H C Off V B F K E one u unit four e G unitW HL LC Cap x ox z s hx hy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hUnit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hmW : ForcingDiagramPoset.LeftCancelMonoid W G unitW)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hW : WordCarrier w D S mul A b W)
    (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hH : MapsTo D R H) (hC : MapsTo D R C) (hF : MapsTo S R F)
    (hV : MapsTo S R V) (hB : MapsTo S R B) (hHL : MapsTo W R HL) (hCap : MapsTo W R Cap)
    (hFloor : ConstructionProbeLetterFloor.FloorLaws D S A K H F)
    (hCost : ConstructionProbeCostBounds.CostBounds hM w Q D mul S A K H C F)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B)
    (hHeight : ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hLC : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hCB : ConstructionProbeGateCap.Bounds unit LC)
    (hEmbed : ConstructionProbeOldEmbeddingSyntax.EmbeddingLaws w D S zero mul A W G e unitW Emb)
    (hExit : ConstructionProbeConditionalJoins.ExitGates w D S zero mul A W G)
    (hxo : PureKuratowski.PairMember M x ox Emb) (hzW : (Project.FirstOrderSemantics.reduct M).mem z W)
    (hHead : HeadSome w D S z s) (hxz : Divides W G ox z)
    (hxh : PureKuratowski.PairMember M ox hx HL) (hyh : PureKuratowski.PairMember M z hy HL) :
    UniformAt hM w Q W G LC ox z hx hy := by
  have hxD := ForcingConditionGraphs.function_input hEmb.1 hxo
  have hOldHX := (hHeight.1 x ox hx ((hOld x ox).mp hxo)).mp hxh
  have hHX := (hR hx).mp (hH.2 x hx hOldHX)
  have hXS := (ConstructionProbeGates.headDiv_of_head_eq_some hM hw hz hHead).mp
    ((hEmbed.2.2.2.2 x ox z hxo hzW).mp hxz)
  obtain ⟨tail,hCons⟩ := hHead
  obtain ⟨v,htv,offset,delta,product,hOffset,hDelta,hProduct,hYSum⟩ :=
    (hHeight.2 s tail z hy hCons hzW).mp hyh
  have hs := ConstructionProbeRawAction.cons_letter hCons
  obtain ⟨outside,hOutside,_⟩ := hB.1.2 s hs
  obtain ⟨floor,t,exit,ht,he,c,hCtx,_,hInterval,_⟩ := hI s offset delta outside hOffset hDelta hOutside
  obtain ⟨hOffsetCut,hDeltaCut,_,_,_,lower,_,_,_,_,_,_,hLower,hLowerOffset,_,_,_⟩ := hInterval
  have hFloorCut := (hR floor).mp (hF.2 s floor hCtx.1)
  have hHXFloor := (hFloor s floor hCtx.1).2.1 x hx hxD hXS hOldHX
  obtain ⟨gap,hGap,hGapValue,hGapSum,_,_⟩ :=
    ConstructionCutDifference.exists_difference hM hw hQ hHX hFloorCut hHXFloor
  obtain ⟨bound,hBound,hMax⟩ := ConstructionCutArithmetic.exists_max hM hw hQ hGap hDeltaCut
  obtain ⟨sum,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hHX hBound
  have hProductCut := ConstructionCutProduct.value_cut hM hw hQ hDeltaCut ((hR v).mp (hHL.2 tail v htv)) hProduct
  have hStrict := bound_below_height hM hw hQ hFloorCut hGap hDeltaCut hOffsetCut hProductCut
    hHXFloor hGapSum hLower hLowerOffset hYSum hMax hSum
  have hInside := ConstructionProbeHeightIntervalGraphs.inside_bounds hM hw hQ hR hH hC hF hCost
  refine ⟨bound,sum,hBound,hSum,hStrict,?_⟩
  intro q cq hq hqc hqz hqx
  by_cases hSame : HeadSome w D S q s
  · obtain ⟨qt,hQt⟩ := hSame
    have hLe := ConstructionProbeWeightBounds.cost_le_scale hM hw hQ hR hu hone hUnit hV hCB hLC hQt hq hqc hDelta
    exact fun p hp => (hMax p).mpr (Or.inr (hLe p hp))
  · obtain ⟨g,og,cg,hgo,hgc,hqg,hgz,hCostBound⟩ :=
      ConstructionProbeCostMargins.cost_other_block_factor hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hLC hEmbed hExit
        hq hzW hSame ⟨tail,hCons⟩ hqz hqc
    have hgD := ForcingConditionGraphs.function_input hEmb.1 hgo
    have hGS := (ConstructionProbeGates.headDiv_of_head_eq_some hM hw hz ⟨tail,hCons⟩).mp
      ((hEmbed.2.2.2.2 g og z hgo hzW).mp hgz)
    have hgNot : ¬ Divides D mul g x := by
      intro hgx
      exact hqx (ConstructionProbeGates.divides_trans hmW hq hqg
        ((hEmbed.2.2.2.1 g x og ox hgo hxo).mpr hgx))
    obtain ⟨gap',_,hGapValue',_,hCGGap'⟩ := hInside s floor x g hx cg hCtx.1 hxD hgD hXS hGS hgNot hOldHX hgc
    have heGap := ConstructionCutDifference.value_unique hM hGapValue hGapValue'
    have hCGGap : Subset cg gap := by simpa only [← heGap] using hCGGap'
    exact fun p hp => (hMax p).mpr (Or.inl (hCGGap p (hCostBound p hp)))

end PPAC.Migration.ConstructionProbeOldNewMargin
