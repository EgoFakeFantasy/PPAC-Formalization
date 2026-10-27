/- Pinned MergerCones.copies_coordinate_margin:289, retaining one strict
bound for the WHOLE class of missed divisors represented in coordinate i.
Reuse old UniformMargins, actual copiesCost estimates and copiesHeight_gap.
No pointwise-only replacement, internal Choice or new arithmetic backend. -/
import PPAC.Migration.ConstructionMergerAverageGap

namespace PPAC.Migration.ConstructionMergerCoordinateMargin
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeLetters (Representatives)
open ConstructionMergerCoordinates (HasRep)
open ConstructionMergerCopyCones (Reaches)
open ConstructionMergerFiniteWeights (HeightValue CostValue)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem half_strict (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q one two a cap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htwo : (Project.FirstOrderSemantics.reduct M).SuccessorOf two one)
    (htwow : (Project.FirstOrderSemantics.reduct M).mem two w)
    (ha : Cut hM w Q a) (haN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p a)
    (hCap : ConstructionCutDivision.Value hM w Q two a cap) : Strict cap a := by
  have hcp := ConstructionCutDivision.value_cut hw hQ htwow ⟨one,htwo.predecessor_mem⟩ ha hCap
  have hcpN := (ConstructionCutDivision.nonempty_iff hw hQ htwow ⟨one,htwo.predecessor_mem⟩ ha hCap).mpr haN
  obtain ⟨three,hthree,hthreew⟩ := hw.1.2 two htwow
  have hd : ConstructionBaseWeights.Digits w one two three := ⟨ho,htwow,hthreew,hone,htwo,hthree⟩
  obtain ⟨double,hDoubleCut,hDoubleSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hcp hcp
  have hDiv := ConstructionCutQuarterSum.double_value hM hw hQ hd hcp hDoubleSum
  have hDA := (ConstructionCutDivision.order_iff hw hQ htwow ⟨one,htwo.predecessor_mem⟩ hDoubleCut ha hDiv hCap).mp (fun _ h => h)
  have hAD := (ConstructionCutDivision.order_iff hw hQ htwow ⟨one,htwo.predecessor_mem⟩ ha hDoubleCut hCap hDiv).mp (fun _ h => h)
  have he : double = a := (ModelTransfer.extensionality hM).eq_of_same_members double a (fun p => ⟨hDA p,hAD p⟩)
  exact he ▸ ConstructionProbeIntervals.sum_positive hM hw hQ hcp hcp hcpN hDoubleSum

/-- A single coordinate-class bound, quantified before every missed letter. -/
def CoordinateBound (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q n R mulCut Id top cap CC D L A projection i z t bound : M.Carrier .set) : Prop :=
  ∀ d cd, (Project.FirstOrderSemantics.reduct M).mem d L →
    CostValue hM w Q n R mulCut Id top cap CC d cd → Reaches D A d t → ¬ Reaches D A d z →
    HasRep projection i d → Subset cd bound

theorem copies_coordinate_margin (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R zero add mulCut Id n CH CC D mul e P C L projection A Height Cost top J one u two unitHeight cap z t a b i : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hId : ForcingConditionGraphs.IdentityGraph R Id)
    (hAdd : ConstructionCutArithmetic.Graph hM w Q R add)
    (hMul : ConstructionCutProduct.Graph hM w Q R mulCut)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ j, (Project.FirstOrderSemantics.reduct M).mem j n)
    (ho : (Project.FirstOrderSemantics.reduct M).mem one w)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (htwo : (Project.FirstOrderSemantics.reduct M).SuccessorOf two one)
    (htwow : (Project.FirstOrderSemantics.reduct M).mem two w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hC : Representatives n D C) (hL : ConstructionMergerCopies.Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProj : ConstructionMergerCopies.Projection n D mul P C projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mul P projection)
    (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hJ : Representatives n L J) (hCH : MapsTo J R CH) (hCC : MapsTo J R CC)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hCost : MapsTo D R Cost) (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hUniform : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul Height Cost)
    (hGraph : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hCoordC : ConstructionMergerCoordinates.Graph n L projection Cost top CC)
    (hEdge : PureKuratowski.PairMember M e unitHeight Height)
    (hCap : ConstructionCutDivision.Value hM w Q two unitHeight cap)
    (hzL : (Project.FirstOrderSemantics.reduct M).mem z L) (htL : (Project.FirstOrderSemantics.reduct M).mem t L)
    (ha : HeightValue hM w Q n R add Id zero CH z a) (hb : HeightValue hM w Q n R add Id zero CH t b)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i n)
    (hReach : Reaches D A z t) (hne : z ≠ t) :
    ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧
      CoordinateBound hM w Q n R mulCut Id top cap CC D L A projection i z t bound := by
  obtain ⟨c,_,hzc⟩ := ConstructionProbeAction.projected hM hJ hCH hi hzL
  obtain ⟨d,_,htd⟩ := ConstructionProbeAction.projected hM hJ hCH hi htL
  obtain ⟨gap,part,avgGap,hGapCut,_,hPointSum,hPartCut,hPartDiv,hAvgCut,_,hAvgSum,hPartLe⟩ :=
    ConstructionMergerAverageGap.copiesHeight_gap hM hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hp hEq hCopy hHeight hHB hUniform hGraph ha hb hi hzc htd hReach
  have hACut : Cut hM w Q a := by
    obtain ⟨sum,hSum,hDiv⟩ := ha
    exact ConstructionCutDivision.value_cut hw hQ hn hnp
      ((hR sum).mp (ConstructionMergerFiniteWeights.coordinateEval_range hM hSum)) hDiv
  have hOldCut := (hR unitHeight).mp (hHeight.2 e unitHeight hEdge)
  have hOldN := (hHB e unitHeight hEdge).1
  have hTopN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p top := by
    obtain ⟨p,hp⟩ := hOldN
    exact ⟨p,(hHB e unitHeight hEdge).2.1 p hp⟩
  have hcapCut := ConstructionCutDivision.value_cut hw hQ htwow ⟨one,htwo.predecessor_mem⟩ hOldCut hCap
  have hcapN := (ConstructionCutDivision.nonempty_iff hw hQ htwow ⟨one,htwo.predecessor_mem⟩ hOldCut hCap).mpr hOldN
  have hCostBounds := (ConstructionMergerCoordinateLaws.coordinate_bounds hz hTopN hHB hCB hGraph hCoordC).2
  have hEst (v cv) (hv : CostValue hM w Q n R mulCut Id top cap CC v cv) :=
    ConstructionMergerWeightEstimates.copiesCost_estimates hM hw hz hzw hQ hR hn hnp hu hone hunit hTopN hId hMul hJ hCC hCostBounds ((hR cap).mpr hcapCut) hcapN hv
  have hFinish (bound) (hBoundCut : Cut hM w Q bound) (hStrict : Strict bound avgGap)
      (hBound : CoordinateBound hM w Q n R mulCut Id top cap CC D L A projection i z t bound) :
      ∃ bound total, Cut hM w Q bound ∧ SumCut hM w Q a bound total ∧ Strict total b ∧
        CoordinateBound hM w Q n R mulCut Id top cap CC D L A projection i z t bound := by
    obtain ⟨total,_,hTotal⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hACut hBoundCut
    exact ⟨bound,total,hBoundCut,hTotal,(ConstructionCutDifference.sum_strict_iff hM hw hQ hBoundCut hAvgCut hACut
      (ConstructionCutArithmetic.sum_comm hM hw hTotal) (ConstructionCutArithmetic.sum_comm hM hw hAvgSum)).mpr hStrict,hBound⟩
  by_cases hzRep : HasRep projection i z
  · obtain ⟨x,hxz⟩ := hzRep
    obtain ⟨y,hyt⟩ := ConstructionMergerCoordinates.hasRep_of_reaches hm hC hp hCopy ⟨x,hxz⟩ hReach
    have hxc := (ConstructionMergerCoordinates.graph_copy_iff hC hp hEq hGraph hxz).mp hzc
    have hyd := (ConstructionMergerCoordinates.graph_copy_iff hC hp hEq hGraph hyt).mp htd
    have hxy := (ConstructionMergerCopyCones.reaches_same_copy_iff hm hC hp hEq hCopy hxz hyt).mp hReach
    have hnyx : ¬ ConstructionBaseMonoid.Divides D mul y x := by
      intro hyx
      have he := ConstructionProbeGateCap.divides_antisymm hm hc (ConstructionProbeAction.projected_indices hC hp hxz).2 hxy hyx
      subst y
      exact hne (ConstructionProbeHomEvaluation.product_unique hM hp hxz hyt)
    obtain ⟨oldBound,oldTotal,hOldBoundCut,hOldSum,hOldStrict,hOldMissed⟩ := hUniform x y c d hxc hyd hxy hnyx
    have hCCut := (hR c).mp (hHeight.2 x c hxc)
    have hOldGapStrict := (ConstructionCutDifference.sum_strict_iff hM hw hQ hOldBoundCut hGapCut hCCut
      (ConstructionCutArithmetic.sum_comm hM hw hOldSum) (ConstructionCutArithmetic.sum_comm hM hw hPointSum)).mp hOldStrict
    obtain ⟨bound,hDivBound⟩ := ConstructionCutDivision.exists_value hM w Q n oldBound
    have hBoundCut := ConstructionCutDivision.value_cut hw hQ hn hnp hOldBoundCut hDivBound
    have hSmall := (ConstructionCutDivision.strict_iff hw hQ hn hnp hOldBoundCut hGapCut hDivBound hPartDiv).mpr hOldGapStrict
    have hStrict : Strict bound avgGap := ⟨fun p hp => hPartLe p (hSmall.1 p hp),fun h => hSmall.2 (fun p hp => h p (hPartLe p hp))⟩
    apply hFinish bound hBoundCut hStrict
    intro v cv _ hcv hvt hvz hvRep
    obtain ⟨q,hqv⟩ := hvRep
    have hqD := (ConstructionProbeAction.projected_indices hC hp hqv).2
    have hqy := (ConstructionMergerCopyCones.reaches_same_copy_iff hm hC hp hEq hCopy hqv hyt).mp hvt
    have hnqx : ¬ ConstructionBaseMonoid.Divides D mul q x := fun h => hvz ((ConstructionMergerCopyCones.reaches_same_copy_iff hm hC hp hEq hCopy hqv hxz).mpr h)
    obtain ⟨cq,hcq,_⟩ := hCost.1.2 q hqD
    have hCQCut := (hR cq).mp (hCost.2 q cq hcq)
    obtain ⟨divCQ,hDivCQ⟩ := ConstructionCutDivision.exists_value hM w Q n cq
    have hCoord := (ConstructionMergerCoordinates.graph_copy_iff hC hp hEq hCoordC hqv).mpr hcq
    have hCopyLe := (hEst v cv hcv).2.2 i cq divCQ hCoord hDivCQ
    have hBoundLe := (ConstructionCutDivision.order_iff hw hQ hn hnp hCQCut hOldBoundCut hDivCQ hDivBound).mpr
      (hOldMissed q cq hqD hcq hqy hnqx)
    exact fun p hp => hBoundLe p (hCopyLe p hp)
  · by_cases htRep : HasRep projection i t
    · obtain ⟨y,hyt⟩ := htRep
      have hyd := (ConstructionMergerCoordinates.graph_copy_iff hC hp hEq hGraph hyt).mp htd
      have hcZero : c = zero := by
        rcases ((hGraph i z c).mp hzc).2.2 with ⟨x,hx,_⟩ | ⟨_,hc0⟩
        · exact (hzRep ⟨x,hx⟩).elim
        · exact hc0
      have hDCut := (hR d).mp (hHeight.2 y d hyd)
      have hGapEq : gap = d := by
        have he : d = gap := ConstructionCutAddition.sum_unique hM hPointSum (by
          simpa only [hcZero] using (ConstructionCutArithmetic.sum_zero hz hGapCut).1)
        exact he.symm
      have hOldOrder := ConstructionProbeParent.height_order hM hm hc hR hHeight hHB hUniform
      have hey : ConstructionBaseMonoid.Divides D mul e y := ⟨y,(ConstructionProbeAction.projected_indices hC hp hyt).2,((hm.1.2 y (ConstructionProbeAction.projected_indices hC hp hyt).2 y).1).mpr rfl⟩
      have hOldLe := hOldOrder.2.2 e y unitHeight d hEdge hyd hey
      have hHalfStrict := half_strict hM hw hQ ho hone htwo htwow hOldCut hOldN hCap
      have hCapStrict : Strict cap gap := by
        rw [hGapEq]
        exact ⟨fun p hp => hOldLe p (hHalfStrict.1 p hp),fun h => hHalfStrict.2 (fun p hp => h p (hOldLe p hp))⟩
      obtain ⟨bound,hDivBound⟩ := ConstructionCutDivision.exists_value hM w Q n cap
      have hBoundCut := ConstructionCutDivision.value_cut hw hQ hn hnp hcapCut hDivBound
      have hSmall := (ConstructionCutDivision.strict_iff hw hQ hn hnp hcapCut hGapCut hDivBound hPartDiv).mpr hCapStrict
      have hStrict : Strict bound avgGap := ⟨fun p hp => hPartLe p (hSmall.1 p hp),fun h => hSmall.2 (fun p hp => h p (hPartLe p hp))⟩
      exact hFinish bound hBoundCut hStrict (fun v cv _ hcv _ _ _ => (hEst v cv hcv).2.1 bound hDivBound)
    · have hStrictAB := (ConstructionMergerHeightComparison.copiesHeight_order hM hw hz hzw hQ hR hId hAdd hn hnp hm hc hC hL hp hProj hEq hCopy hJ hCH hHeight hHB hUniform hGraph hzL htL ha hb hReach).2 hne
      have hZeroCut : Cut hM w Q zero := (hR zero).mp (ConstructionMergerCoordinateLaws.empty_cut_mem hM hR hz (hHeight.2 e unitHeight hEdge))
      exact ⟨zero,a,hZeroCut,(ConstructionCutArithmetic.sum_zero hz hACut).2,hStrictAB,
        fun _ _ _ _ hvt _ hvRep => (htRep (ConstructionMergerCoordinates.hasRep_of_reaches hm hC hp hCopy hvRep hvt)).elim⟩

end PPAC.Migration.ConstructionMergerCoordinateMargin
