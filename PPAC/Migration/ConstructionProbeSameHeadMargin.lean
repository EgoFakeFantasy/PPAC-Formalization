/- Pinned ProbeMargins.cons_dvd_cons_iff:406 / uniform_margin_same_head:415.
Reuse actual generator multiplication/cancellation, existing outside-block
factors and exact affine scaling. The suffix margin is the source IH. -/
import PPAC.Migration.ConstructionCutProductArithmetic
import PPAC.Migration.ConstructionProbeCostMargins

namespace PPAC.Migration.ConstructionProbeSameHeadMargin
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (Old Cons)
open ConstructionProbeGates (HeadSome)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeLetterIntervals (UniformAt)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source cons cancellation, directly from existing generator products. -/
theorem cons_dvd_cons_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unitW s gen Y Z qY qZ : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hAlpha : ConstructionProbeAlphabet.Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hMult : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hUnit : Old zero D e unitW) (hGen : Cons w D S s unitW gen)
    (hGenW : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hY : Cons w D S s Y qY) (hZ : Cons w D S s Z qZ)
    (hqY : (Project.FirstOrderSemantics.reduct M).mem qY W)
    (hqZ : (Project.FirstOrderSemantics.reduct M).mem qZ W) : Divides W G qY qZ ↔ Divides W G Y Z := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult
  have hYR := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hY).mp ((hW qY).mp hqY)
  have hZR := (ConstructionProbeReduced.reduced_cons hM hw hz hzw hZ).mp ((hW qZ).mp hqZ)
  have hYW := (hW Y).mpr hYR.1
  have hZW := (hW Z).mpr hZR.1
  exact ConstructionProbeConditionalJoins.left_mul_dvd_iff hmW hGenW hYW hZW
    (ConstructionProbeGenerator.generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb hUnit hMult hGen hGenW hYW hYR.2 hY)
    (ConstructionProbeGenerator.generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb hUnit hMult hGen hGenW hZW hZR.2 hZ)

/-- Exact source same-head margin, with witness scale(s)*suffixBound.
Every outside-block divisor divides both endpoints and hence cannot be missed. -/
theorem uniform_margin_same_head (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb H C Off V Cap LC HL e G unitW E I s Y Z qY qZ hy hzv x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hAlpha : ConstructionProbeAlphabet.Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hW : WordCarrier w D S mul A b W)
    (hMult : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hUnit : Old zero D e unitW) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hOff : MapsTo S R Off) (hV : MapsTo S R V) (hHL : MapsTo W R HL) (hLC : MapsTo W R LC)
    (hVP : ∀ s d, PureKuratowski.PairMember M s d V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d)
    (hHeight : ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL)
    (hCost : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hExit : ConstructionProbeConditionalJoins.ExitGates w D S zero mul A W G)
    (hY : Cons w D S s Y qY) (hZ : Cons w D S s Z qZ)
    (hqY : (Project.FirstOrderSemantics.reduct M).mem qY W) (hqZ : (Project.FirstOrderSemantics.reduct M).mem qZ W)
    (hHY : PureKuratowski.PairMember M Y hy HL) (hHZ : PureKuratowski.PairMember M Z hzv HL)
    (hX : PureKuratowski.PairMember M qY x HL) (hYH : PureKuratowski.PairMember M qZ y HL)
    (hMargin : UniformAt hM w Q W G LC Y Z hy hzv) : UniformAt hM w Q W G LC qY qZ x y := by
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult
  have hEmbed := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult hOld
  obtain ⟨Gen,hGenMap,hGenGraph⟩ := ConstructionProbeGenerator.exists_generator_graph hM hw hz hzw hCon hW hb hne hUnit
  obtain ⟨gen,hgen,_⟩ := hGenMap.1.2 s (ConstructionProbeRawAction.cons_letter hY)
  have hGenCons := (hGenGraph s gen).mp hgen
  have hGenW := hGenMap.2 s gen hgen
  obtain ⟨vY,hVY,o,d,py,hO,hD,hPY,hOSum⟩ := (hHeight.2 s Y qY x hY hqY).mp hX
  have heY := ForcingConditionGraphs.function_unique hHL.1 hVY hHY
  subst vY
  obtain ⟨vZ,hVZ,o',d',pz,hO',hD',hPZ,hOSum'⟩ := (hHeight.2 s Z qZ y hZ hqZ).mp hYH
  have heZ := ForcingConditionGraphs.function_unique hHL.1 hVZ hHZ
  subst vZ
  have heO := ForcingConditionGraphs.function_unique hOff.1 hO hO'
  subst o'
  have heD := ForcingConditionGraphs.function_unique hV.1 hD hD'
  subst d'
  have hScale := (hR d).mp (hV.2 s d hD)
  have hOffset := (hR o).mp (hOff.2 s o hO)
  have hYCut := (hR hy).mp (hHL.2 Y hy hHY)
  have hZCut := (hR hzv).mp (hHL.2 Z hzv hHZ)
  obtain ⟨c,suffixSum,hC,hSuffixSum,hStrict,hMissed⟩ := hMargin
  obtain ⟨bound,hBound,hBoundProd⟩ := ConstructionCutProduct.exists_product hM hw hQ hScale hC
  obtain ⟨sum,_,hSum⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ((hR x).mp (hHL.2 qY x hX)) hBound
  have hNewStrict := ConstructionCutProductArithmetic.affine_strict hM hw hQ hScale hOffset hYCut hZCut hC
    (hVP s d hD) hSuffixSum hStrict hPY hPZ hBoundProd hOSum hOSum' hSum
  refine ⟨bound,sum,hBound,hSum,hNewStrict,?_⟩
  intro q cq hq hqc hqZdiv hqYnot
  by_cases hSame : HeadSome w D S q s
  · obtain ⟨D,hDCons⟩ := hSame
    have hDZ := (cons_dvd_cons_iff hM hw hz hzw hm hAlpha hW hb hMult hUnit hGenCons hGenW hDCons hZ hq hqZ).mp hqZdiv
    have hDYnot : ¬ Divides W G D Y := fun h => hqYnot
      ((cons_dvd_cons_iff hM hw hz hzw hm hAlpha hW hb hMult hUnit hGenCons hGenW hDCons hY hq hqY).mpr h)
    obtain ⟨cd,hCD,d',prod,cap,hD',hProd,_,hMin⟩ := (hCost.2 s D q cq hDCons hq).mp hqc
    have heD := ForcingConditionGraphs.function_unique hV.1 hD hD'
    subst d'
    have hLe := hMissed D cd (ForcingConditionGraphs.function_input hLC.1 hCD) hCD hDZ hDYnot
    have hProductLe := ConstructionCutProduct.value_mono hProd hBoundProd (fun _ h => h) hLe
    exact fun p hp => hProductLe p ((ConstructionCutMinimum.value_bounds hMin).1 p hp)
  · obtain ⟨g,og,hgOld,hqg,hgZ⟩ := ConstructionProbeProfiles.old_factor_of_other_block hM hw hz hzw hm hAlpha hW hb hMult hUnit hExit hq hqZ hSame ⟨Z,hZ⟩ hqZdiv
    have hgo := (hOld g og).mpr hgOld
    have hGY := (hEmbed.2.2.2.2 g og qY hgo hqY).mpr
      ((ConstructionProbeGates.headDiv_of_same_head hM hw hz ⟨Y,hY⟩ ⟨Z,hZ⟩).mpr
        ((hEmbed.2.2.2.2 g og qZ hgo hqZ).mp hgZ))
    exact (hqYnot (ConstructionProbeGates.divides_trans hmW hq hqg hGY)).elim

end PPAC.Migration.ConstructionProbeSameHeadMargin
