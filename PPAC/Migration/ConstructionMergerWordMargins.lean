/- Pinned MergerCones.uniform_margin_snoc:430 and subsequent source margins.
Reuse actual literal weight graphs, SAME Word divisibility decomposition,
existing copy margins/cut arithmetic/native Raw induction. The source result
is existential: snoc uses the valid room*(unit/4) witness, avoiding needless
8-vs-4 arithmetic; actual source height/cost formulas are UNCHANGED. -/
import PPAC.Migration.ConstructionMergerWordCosts
import PPAC.Migration.ConstructionMergerWordDivisibility
import PPAC.Migration.ConstructionProbeUniformMargins

namespace PPAC.Migration.ConstructionMergerWordMargins
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeRaw (Raw Old Cons)
open ConstructionProbeLetterIntervals (UniformAt UniformMargins MissedBound)
open ConstructionBaseMonoid (Divides)
open ConstructionMergerCopyCones (Reaches)
open ConstructionMergerWordParameters (Recipe)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source theta is strictly above unit/4, and EVERY literal cost factor is
at most unit/4. The right minimum branch and old cost<=unit suffice. -/
theorem parameter_gap_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R S four unit quarter eighth HD CD letter theta sigma factor : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hfour : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hfp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i four)
    (hUnit : Cut hM w Q unit) (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hHD : MapsTo S R HD) (hCD : MapsTo S R CD)
    (hHDB : ConstructionCutWeights.RangeBound unit HD) (hCDB : ConstructionProbeGateCap.Bounds unit CD)
    (hRecipe : Recipe hM w Q four unit quarter eighth HD CD letter theta sigma factor) :
    Strict quarter theta ∧ Subset factor quarter := by
  obtain ⟨h,c,qh,qc,hh,hc,hQH,hQC,hTheta,_,_,hMin⟩ := hRecipe
  have hHCut := (hR h).mp (hHD.2 letter h hh)
  have hCCut := (hR c).mp (hCD.2 letter c hc)
  have hQuarterCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hUnit hQuarter
  have hQHCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hHCut hQH
  have hQHN := (ConstructionCutDivision.nonempty_iff hw hQ hfour hfp hHCut hQH).mpr (hHDB letter h hh).1
  have hQCLe := (ConstructionCutDivision.order_iff hw hQ hfour hfp hCCut hUnit hQC hQuarter).mpr (hCDB letter c hc).2
  exact ⟨ConstructionProbeIntervals.sum_positive hM hw hQ hQuarterCut hQHCut hQHN hTheta,
    fun p hp => hQCLe p ((ConstructionCutMinimum.value_bounds hMin).2 p hp)⟩

/-- Exact source existential UniformMargin for ONE snoc, uniformly for the
WHOLE missed-divisor class. No new bound/weight/maximum oracle is assumed. -/
theorem uniform_margin_snoc (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W mul A T G one u unit four quarter eighth H C HD CD O V B HL CL letter pref out a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hfour : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hfp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i four)
    (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hHD : MapsTo S R HD) (hCD : MapsTo S R CD)
    (hHDB : ConstructionCutWeights.RangeBound unit HD) (hCDB : ConstructionProbeGateCap.Bounds unit CD)
    (hO : MapsTo S R O) (hV : MapsTo S R V) (hB : MapsTo S R B)
    (hParams : ∀ s theta sigma factor, PureKuratowski.PairMember M s theta O → PureKuratowski.PairMember M s sigma V →
      PureKuratowski.PairMember M s factor B → Recipe hM w Q four unit quarter eighth HD CD s theta sigma factor)
    (hHL : MapsTo W R HL) (hHeightBound : ConstructionCutWeights.RangeBound unit HL)
    (hHeight : ConstructionMergerWordHeights.LiteralLaws hM w Q D S zero unit H O HL)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hCons : Cons w D S letter pref out) (ha : PureKuratowski.PairMember M pref a HL)
    (hb : PureKuratowski.PairMember M out b HL) : UniformAt hM w Q W G CL pref out a b := by
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  have hACut := (hR a).mp (hHL.2 pref a ha)
  have hQuarterCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hUnit hQuarter
  obtain ⟨a',ha',theta,room,prod,ho,hRoom,hDiff,hVRoom,hProd,hSum⟩ := (hHeight.2 letter pref out b hCons).mp hb
  have he := ForcingConditionGraphs.function_unique hHL.1 ha' ha
  subst a'
  have hs := ConstructionProbeRawAction.cons_letter hCons
  obtain ⟨sigma,hv,_⟩ := hV.1.2 letter hs
  obtain ⟨factor,hf,_⟩ := hB.1.2 letter hs
  have hThetaCut := (hR theta).mp (hO.2 letter theta ho)
  have hGap := (parameter_gap_bounds hM hw hQ hR hfour hfp hUnit hQuarter hHD hCD hHDB hCDB (hParams letter theta sigma factor ho hv hf)).1
  have hRoomN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p room := by
    obtain ⟨r,_,hr,_,_,hN⟩ := ConstructionCutDifference.exists_difference hM hw hQ hACut hUnit (hHeightBound pref a ha).2.1
    have he := ConstructionCutDifference.value_unique hM hr hDiff
    exact he ▸ hN (hHeightBound pref a ha).2.2
  obtain ⟨bound,hBound,hBoundProd⟩ := ConstructionCutProduct.exists_product hM hw hQ hRoom hQuarterCut
  obtain ⟨total,_,hTotal⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hACut hBound
  have hProdCut := ConstructionCutProduct.value_cut hM hw hQ hRoom hThetaCut hProd
  have hSmall := ConstructionCutProductArithmetic.positive_strict hM hw hQ hRoom hQuarterCut hThetaCut hRoomN hGap hBoundProd hProd
  have hStrict := (ConstructionCutDifference.sum_strict_iff hM hw hQ hBound hProdCut hACut
    (ConstructionCutArithmetic.sum_comm hM hw hTotal) (ConstructionCutArithmetic.sum_comm hM hw hSum)).mpr hSmall
  refine ⟨bound,total,hBound,hTotal,hStrict,?_⟩
  intro d cd _ hdc hdo hdp
  rcases (ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hW hTable hMult hCons).mp hdo with h | ⟨last,hDCons,_⟩
  · exact (hdp h).elim
  · obtain ⟨h,room',factor',hh,hDiff',_,hf',hProd'⟩ :=
      (ConstructionMergerWordCosts.cost_snoc_iff hM hw hz hW hCostGraph hDCons).mp hdc
    have he := ForcingConditionGraphs.function_unique hHL.1 hh ha
    subst h
    have he := ConstructionCutDifference.value_unique hM hDiff' hDiff
    subst room'
    have hLastS := ConstructionProbeRawAction.cons_letter hDCons
    obtain ⟨theta',ho',_⟩ := hO.1.2 last hLastS
    obtain ⟨sigma',hv',_⟩ := hV.1.2 last hLastS
    have hFactorBound := (parameter_gap_bounds hM hw hQ hR hfour hfp hUnit hQuarter hHD hCD hHDB hCDB
      (hParams last theta' sigma' factor' ho' hv' hf')).2
    exact ConstructionCutProduct.value_mono hProd' hBoundProd (fun _ h => h) hFactorBound

theorem uniform_margin_same_prefix (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W mul A T G one u unit four quarter eighth H C HD CD O V B HL CL z t pref left right a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hfour : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hfp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i four)
    (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hHD : MapsTo S R HD) (hCD : MapsTo S R CD)
    (hO : MapsTo S R O) (hV : MapsTo S R V) (hB : MapsTo S R B)
    (hParams : ∀ s theta sigma factor, PureKuratowski.PairMember M s theta O → PureKuratowski.PairMember M s sigma V →
      PureKuratowski.PairMember M s factor B → Recipe hM w Q four unit quarter eighth HD CD s theta sigma factor)
    (hHL : MapsTo W R HL) (hHeightBound : ConstructionCutWeights.RangeBound unit HL)
    (hHeight : ConstructionMergerWordHeights.LiteralLaws hM w Q D S zero unit H O HL)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hLetterUniform : ∀ x y hx hy, PureKuratowski.PairMember M x hx HD → PureKuratowski.PairMember M y hy HD →
      Reaches D A x y → x ≠ y → ConstructionMergerUniformMargin.UniformAt hM w Q D S A CD x y hx hy)
    (hLeft : Cons w D S z pref left) (hRight : Cons w D S t pref right)
    (ha : PureKuratowski.PairMember M left a HL) (hb : PureKuratowski.PairMember M right b HL)
    (hReach : Reaches D A z t) (hne : z ≠ t) : UniformAt hM w Q W G CL left right a b := by
  have hUnit := ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit
  have hQuarterCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hUnit hQuarter
  obtain ⟨v,hvp,thetaZ,room,prodZ,hoZ,hRoom,hDiff,hVRoom,hProdZ,hSumZ⟩ := (hHeight.2 z pref left a hLeft).mp ha
  obtain ⟨v',hvp',thetaT,room',prodT,hoT,_,hDiff',_,hProdT,hSumT⟩ := (hHeight.2 t pref right b hRight).mp hb
  have he := ForcingConditionGraphs.function_unique hHL.1 hvp' hvp
  subst v'
  have he := ConstructionCutDifference.value_unique hM hDiff' hDiff
  subst room'
  have hvCut := (hR v).mp (hHL.2 pref v hvp)
  have hACut := (hR a).mp (hHL.2 left a ha)
  have hThetaZCut := (hR thetaZ).mp (hO.2 z thetaZ hoZ)
  have hThetaTCut := (hR thetaT).mp (hO.2 t thetaT hoT)
  have hzS := ConstructionProbeRawAction.cons_letter hLeft
  have htS := ConstructionProbeRawAction.cons_letter hRight
  obtain ⟨sigmaZ,hvZ,_⟩ := hV.1.2 z hzS
  obtain ⟨factorZ,hbZ,_⟩ := hB.1.2 z hzS
  obtain ⟨sigmaT,hvT,_⟩ := hV.1.2 t htS
  obtain ⟨factorT,hbT,_⟩ := hB.1.2 t htS
  obtain ⟨heightZ,costZ,qHZ,qCZ,hHZ,_,hQHZ,_,hThetaZ,_,_,_⟩ := hParams z thetaZ sigmaZ factorZ hoZ hvZ hbZ
  obtain ⟨heightT,costT,qHT,qCT,hHT,_,hQHT,_,hThetaT,_,_,_⟩ := hParams t thetaT sigmaT factorT hoT hvT hbT
  have hHZCut := (hR heightZ).mp (hHD.2 z heightZ hHZ)
  have hHTCut := (hR heightT).mp (hHD.2 t heightT hHT)
  have hQHZCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hHZCut hQHZ
  have hQHTCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hHTCut hQHT
  obtain ⟨c,oldTotal,hC,hOldSum,hOldStrict,hMissed⟩ := hLetterUniform z t heightZ heightT hHZ hHT hReach hne
  have hOldTotalCut := ConstructionCutAssociativity.sum_is_cut hM hw hQ hHZCut hC hOldSum
  obtain ⟨cq,hCQ⟩ := ConstructionCutDivision.exists_value hM w Q four c
  obtain ⟨sq,hSQ⟩ := ConstructionCutDivision.exists_value hM w Q four oldTotal
  have hCQCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hC hCQ
  have hSQCut := ConstructionCutDivision.value_cut hw hQ hfour hfp hOldTotalCut hSQ
  have hDivSum := ConstructionMergerAverageGap.division_sum hM hw hQ hfour hfp hHZCut hC hOldSum hQHZ hCQ hSQ
  have hDivStrict := (ConstructionCutDivision.strict_iff hw hQ hfour hfp hOldTotalCut hHTCut hSQ hQHT).mpr hOldStrict
  obtain ⟨suffixTheta,_,hSuffix⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hQuarterCut hSQCut
  have hThetaSuffix := (ConstructionProbeIntervals.reassociate hM hw hQ hQuarterCut hQHZCut hCQCut hThetaZ hDivSum).mpr hSuffix
  have hSuffixStrict := (ConstructionCutDifference.sum_strict_iff hM hw hQ hSQCut hQHTCut hQuarterCut
    (ConstructionCutArithmetic.sum_comm hM hw hSuffix) (ConstructionCutArithmetic.sum_comm hM hw hThetaT)).mpr hDivStrict
  have hRoomN : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p room := by
    obtain ⟨r,_,hr,_,_,hN⟩ := ConstructionCutDifference.exists_difference hM hw hQ hvCut hUnit (hHeightBound pref v hvp).2.1
    have he := ConstructionCutDifference.value_unique hM hr hDiff
    exact he ▸ hN (hHeightBound pref v hvp).2.2
  obtain ⟨bound,hBound,hBoundProd⟩ := ConstructionCutProduct.exists_product hM hw hQ hRoom hCQCut
  obtain ⟨total,_,hTotal⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ hACut hBound
  have hStrict := ConstructionCutProductArithmetic.affine_strict hM hw hQ hRoom hvCut hThetaZCut hThetaTCut hCQCut
    hRoomN hThetaSuffix hSuffixStrict hProdZ hProdT hBoundProd hSumZ hSumT hTotal
  refine ⟨bound,total,hBound,hTotal,hStrict,?_⟩
  intro d cd _ hdc hdt hdz
  rcases (ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hW hTable hMult hRight).mp hdt with hdp | ⟨last,hDCons,hLastT⟩
  · exact (hdz ((ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hW hTable hMult hLeft).mpr (Or.inl hdp))).elim
  · have hLastZ : ¬ Reaches D A last z := fun h => hdz
      ((ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hW hTable hMult hLeft).mpr (Or.inr ⟨last,hDCons,h⟩))
    obtain ⟨v',room',factor,hh,hDiff',_,hf,hCostProd⟩ :=
      (ConstructionMergerWordCosts.cost_snoc_iff hM hw hz hW hCostGraph hDCons).mp hdc
    have he := ForcingConditionGraphs.function_unique hHL.1 hh hvp
    subst v'
    have he := ConstructionCutDifference.value_unique hM hDiff' hDiff
    subst room'
    have hLastS := ConstructionProbeRawAction.cons_letter hDCons
    obtain ⟨theta,ho,_⟩ := hO.1.2 last hLastS
    obtain ⟨sigma,hv,_⟩ := hV.1.2 last hLastS
    obtain ⟨height,cost,qh,qc,_,hCost,_,hQC,_,_,_,hMin⟩ := hParams last theta sigma factor ho hv hf
    have hCostCut := (hR cost).mp (hCD.2 last cost hCost)
    have hCostLe := hMissed last cost hLastS hCost hLastT hLastZ
    have hQCLe := (ConstructionCutDivision.order_iff hw hQ hfour hfp hCostCut hC hQC hCQ).mpr hCostLe
    have hFactorLe : Subset factor cq := fun p hp => hQCLe p ((ConstructionCutMinimum.value_bounds hMin).2 p hp)
    exact ConstructionCutProduct.value_mono hCostProd hBoundProd (fun _ h => h) hFactorLe

theorem old_comparison_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W Pair G T x y ox oy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hPair : ConstructionProbeLetters.Representatives W W Pair)
    (hG : MapsTo Pair W G) (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G) (hX : Old zero D x ox) (hY : Old zero D y oy) :
    Divides W G ox oy ↔ Divides D mul x y :=
  ConstructionMergerWordDivisibility.old_dvd_iff hM hw hz hzw hW hPair hG hTable hMult
    (ConstructionProbeRaw.old_raw hM hz hzw hY) hX (ConstructionMergerWordDivisibility.leading_old hY)

/-- The source whole missed-cost family of an old comparison is EXACTLY unchanged,
including incomparable/equal comparisons; no strictness hypothesis is added. -/
theorem old_missed_costs_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W mul A T Pair G unit HL C B CL x y ox oy cd : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hPair : ConstructionProbeLetters.Representatives W W Pair)
    (hG : MapsTo Pair W G) (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hX : Old zero D x ox) (hY : Old zero D y oy) :
    ConstructionProbeCostSupremum.CostMember W G CL ox oy cd ↔ ConstructionProbeCostSupremum.CostMember D mul C x y cd := by
  constructor
  · rintro ⟨d,_,hdc,hdy,hdx⟩
    obtain ⟨q,_,hprod⟩ := hdy
    obtain ⟨a,b,hA,hB,hAB⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hPair hG hTable hMult hY hprod
    refine ⟨a,hA.1,(ConstructionMergerWordCosts.cost_old_iff hM hz hzw hW hCostGraph hA).mp hdc,⟨b,hB.1,hAB⟩,?_⟩
    exact fun h => hdx ((old_comparison_iff hM hw hz hzw hW hPair hG hTable hMult hA hX).mpr h)
  · rintro ⟨a,ha,hac,hay,hax⟩
    obtain ⟨oa,hA⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) ha
    exact ⟨oa,(hW oa).mpr (ConstructionProbeRaw.old_raw hM hz hzw hA),
      (ConstructionMergerWordCosts.cost_old_iff hM hz hzw hW hCostGraph hA).mpr hac,
      (old_comparison_iff hM hw hz hzw hW hPair hG hTable hMult hA hY).mpr hay,
      fun h => hax ((old_comparison_iff hM hw hz hzw hW hPair hG hTable hMult hA hX).mp h)⟩

/-- Source uniform_margin_old; SAME old bound and exact cost-family transport. -/
theorem uniform_margin_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W mul A T Pair G unit H O HL C B CL x y ox oy a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hPair : ConstructionProbeLetters.Representatives W W Pair)
    (hG : MapsTo Pair W G) (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hHeight : ConstructionMergerWordHeights.LiteralLaws hM w Q D S zero unit H O HL)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hOldUniform : UniformMargins hM w Q D mul H C)
    (hX : Old zero D x ox) (hY : Old zero D y oy)
    (ha : PureKuratowski.PairMember M ox a HL) (hb : PureKuratowski.PairMember M oy b HL)
    (hxy : Divides D mul x y) (hyx : ¬ Divides D mul y x) : UniformAt hM w Q W G CL ox oy a b := by
  obtain ⟨bound,total,hBound,hTotal,hStrict,hMissed⟩ := hOldUniform x y a b
    ((hHeight.1 x ox a hX).mp ha) ((hHeight.1 y oy b hY).mp hb) hxy hyx
  refine ⟨bound,total,hBound,hTotal,hStrict,?_⟩
  intro d cd hd hdc hdy hdx
  obtain ⟨old,hold,hcost,hOldY,hOldX⟩ :=
    (old_missed_costs_iff hM hw hz hzw hW hPair hG hTable hMult hCostGraph hX hY).mp ⟨d,hd,hdc,hdy,hdx⟩
  exact hMissed old cd hold hcost hOldY hOldX

/-- Source old_cost_supremum: SAME exact least upper bound, for EVERY old comparison. -/
theorem old_cap_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q D S zero W mul A T Pair G unit HL C B CL x y ox oy cap : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hPair : ConstructionProbeLetters.Representatives W W Pair)
    (hG : MapsTo Pair W G) (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hX : Old zero D x ox) (hY : Old zero D y oy) :
    ConstructionProbeCostSupremum.Cap W G CL ox oy cap ↔ ConstructionProbeCostSupremum.Cap D mul C x y cap := by
  have he (cd) := old_missed_costs_iff hM hw hz hzw hW hPair hG hTable hMult hCostGraph hX hY (cd := cd)
  constructor
  · rintro ⟨f,hf,hUpper,hLeast⟩
    exact ⟨f,fun cd => (hf cd).trans (he cd),hUpper,hLeast⟩
  · rintro ⟨f,hf,hUpper,hLeast⟩
    exact ⟨f,fun cd => (hf cd).trans (he cd).symm,hUpper,hLeast⟩

/-- Actual common supremum is constructed even for empty/incomparable old classes. -/
theorem exists_old_common_supremum (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W mul A T Pair G unit HL C B CL x y ox oy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hR : CutCarrier hM w Q R) (hUnit : Cut hM w Q unit)
    (hW : ConstructionProbeRaw.Carrier w D S W) (hPair : ConstructionProbeLetters.Representatives W W Pair)
    (hG : MapsTo Pair W G) (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hC : MapsTo D R C) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hX : Old zero D x ox) (hY : Old zero D y oy) :
    ∃ cap, Cut hM w Q cap ∧ ConstructionProbeCostSupremum.Cap D mul C x y cap ∧ ConstructionProbeCostSupremum.Cap W G CL ox oy cap := by
  obtain ⟨f,hf,hfR⟩ := ConstructionProbeCostSupremum.exists_family hM (x := x) (y := y) hC
  have hBound : ConstructionRealCuts.UpperBound f unit := by
    intro cd hcd
    obtain ⟨d,_,hdc,_,_⟩ := (hf cd).mp hcd
    exact (hCB d cd hdc).2
  obtain ⟨cap,hCap,hUpper,hLeast⟩ := ConstructionRealCuts.bounded_union hM hR hfR hUnit hBound
  have hOld : ConstructionProbeCostSupremum.Cap D mul C x y cap := ⟨f,hf,hUpper,hLeast⟩
  exact ⟨cap,hCap,hOld,(old_cap_iff hM hw hz hzw hW hPair hG hTable hMult hCostGraph hX hY).mpr hOld⟩

/-- Pinned word_uniform_margin:493. The UNCHANGED pure atTarget invariant
and native Raw induction cover ALL comparisons at ALL internal lengths. -/
theorem word_uniform_margin (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D S zero W mul A T G one u unit four quarter eighth H C HD CD O V B HL CL Pair unitW : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hunit : ConstructionRealCuts.Principal hM w Q u unit)
    (hfour : (Project.FirstOrderSemantics.reduct M).mem four w)
    (hfp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i four)
    (hQuarter : ConstructionCutDivision.Value hM w Q four unit quarter)
    (hW : ConstructionProbeRaw.Carrier w D S W)
    (hTable : ConstructionMergerWordAction.ActionTable w D S zero mul A T)
    (hMult : ConstructionMergerWordProduct.Laws w D S zero T G)
    (hHD : MapsTo S R HD) (hCD : MapsTo S R CD)
    (hHDB : ConstructionCutWeights.RangeBound unit HD) (hCDB : ConstructionProbeGateCap.Bounds unit CD)
    (hO : MapsTo S R O) (hV : MapsTo S R V) (hB : MapsTo S R B)
    (hParams : ∀ s theta sigma factor, PureKuratowski.PairMember M s theta O → PureKuratowski.PairMember M s sigma V →
      PureKuratowski.PairMember M s factor B → Recipe hM w Q four unit quarter eighth HD CD s theta sigma factor)
    (hHL : MapsTo W R HL) (hHeightBound : ConstructionCutWeights.RangeBound unit HL)
    (hHeight : ConstructionMergerWordHeights.LiteralLaws hM w Q D S zero unit H O HL)
    (hCostGraph : ∀ q y, PureKuratowski.PairMember M q y CL ↔ (Project.FirstOrderSemantics.reduct M).mem q W ∧
      ConstructionMergerWordCosts.Value hM w Q D S zero unit HL C B q y)
    (hPair : ConstructionProbeLetters.Representatives W W Pair) (hG : MapsTo Pair W G)
    (hWordM : ForcingDiagramPoset.LeftCancelMonoid W G unitW) (hWordCon : ForcingDiagramPoset.Conical W G unitW)
    (hOldUniform : UniformMargins hM w Q D mul H C)
    (hLetterUniform : ∀ x y hx hy, PureKuratowski.PairMember M x hx HD → PureKuratowski.PairMember M y hy HD →
      Reaches D A x y → x ≠ y → ConstructionMergerUniformMargin.UniformAt hM w Q D S A CD x y hx hy) :
    UniformMargins hM w Q W G HL CL := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases Q (Fin.cases W (Fin.cases G (Fin.cases HL (fun _ => CL))))), free := fun _ => w }
  let p : Project.UnarySchema 6 := {
    body := ConstructionProbeUniformMargins.atTarget 1 2 3 4 5 6 0
    freeClosed := ConstructionProbeUniformMargins.atTarget_freeClosed _ _ _ _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔ ∀ x a b,
      (Project.FirstOrderSemantics.reduct M).mem x W → (Project.FirstOrderSemantics.reduct M).mem q W →
      PureKuratowski.PairMember M x a HL → PureKuratowski.PairMember M q b HL →
      Divides W G x q → ¬ Divides W G q x → UniformAt hM w Q W G CL x q a b :=
    ConstructionProbeUniformMargins.atTarget_semantics hM (env.push q) 1 2 3 4 5 6 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro oldY target hOldY
    apply (he target).mpr
    intro x a b _ _ hxa htb hxy hnyx
    obtain ⟨q,_,hprod⟩ := hxy
    obtain ⟨oldX,oldQ,hOldX,hOldQ,hOldProd⟩ :=
      ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw hW hPair hG hTable hMult hOldY hprod
    have hOldDiv : Divides D mul oldX oldY := ⟨oldQ,hOldQ.1,hOldProd⟩
    have hOldNot : ¬ Divides D mul oldY oldX := fun h =>
      hnyx ((old_comparison_iff hM hw hz hzw hW hPair hG hTable hMult hOldY hOldX).mpr h)
    exact uniform_margin_old hM hw hz hzw hW hPair hG hTable hMult hHeight hCostGraph hOldUniform hOldX hOldY hxa htb hOldDiv hOldNot) (by
    intro letter pref target hCons ih
    apply (he target).mpr
    intro x a b hx _ hxa htb hxy hnyx
    have hpref := (hW pref).mpr (ConstructionProbeRaw.cons_raw hCons).1
    rcases (ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hW hTable hMult hCons).mp hxy with hxPref | ⟨last,hXCons,hReach⟩
    · by_cases hEq : x = pref
      · subst x
        exact uniform_margin_snoc hM hw hz hzw hQ hR hu hunit hfour hfp hQuarter hW hTable hMult hHD hCD hHDB hCDB hO hV hB hParams hHL hHeightBound hHeight hCostGraph hCons hxa htb
      · obtain ⟨hp,hpEdge,_⟩ := hHL.1.2 pref hpref
        have hNoPrefX : ¬ Divides W G pref x := fun h => hEq (ConstructionProbeGateCap.divides_antisymm hWordM hWordCon hx hxPref h)
        have hPrev := (he pref).mp ih x a hp hx hpref hxa hpEdge hxPref hNoPrefX
        have hNext := uniform_margin_snoc hM hw hz hzw hQ hR hu hunit hfour hfp hQuarter hW hTable hMult hHD hCD hHDB hCDB hO hV hB hParams hHL hHeightBound hHeight hCostGraph hCons hpEdge htb
        exact ConstructionProbeUniformMargins.uniform_trans hM hw hQ ((hR a).mp (hHL.2 x a hxa)) ((hR hp).mp (hHL.2 pref hp hpEdge)) hPrev hNext
    · have hNe : last ≠ letter := by
        intro heq
        subst last
        have heWord := ConstructionProbeRaw.cons_unique hM hw hXCons hCons
        apply hnyx
        simpa only [heWord] using hxy
      exact uniform_margin_same_prefix hM hw hz hzw hQ hR hu hunit hfour hfp hQuarter hW hTable hMult hHD hCD hO hV hB hParams hHL hHeightBound hHeight hCostGraph hLetterUniform hXCons hCons hxa htb hReach hNe)
  intro x y a b hxa hyb hxy hnyx
  have hx := ForcingConditionGraphs.function_input hHL.1 hxa
  have hy := ForcingConditionGraphs.function_input hHL.1 hyb
  exact (he y).mp (hAll y ((hW y).mp hy)) x a b hx hy hxa hyb hxy hnyx

end PPAC.Migration.ConstructionMergerWordMargins
