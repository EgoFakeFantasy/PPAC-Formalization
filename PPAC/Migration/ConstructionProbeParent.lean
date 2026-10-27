/- Pinned MonoidBase.ProbeData.extension/inclusion: eliminate all supplied
Path/alphabet/floor/interval implementation data by existing native producers.
The only path input is the source request's actual Path, not new construction laws. -/
import PPAC.Migration.ConstructionOperationSource
import PPAC.Migration.ConstructionProbeOldCostSupremum
import PPAC.Migration.ConstructionPersistentProfiles
import PPAC.Migration.ConstructionProbeWordCardinality

namespace PPAC.Migration.ConstructionProbeParent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionRealCuts
open ConstructionProbeRaw (Old)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeLetterIntervals (UniformMargins)
open ConstructionProbeCostSupremum (Family Cap)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source HeightCost.strictMono_height's order consequence, reusing the
existing monoid antisymmetry and actual sum membership. -/
theorem height_order (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e H C unit : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hR : CutCarrier hM w Q R) (hH : MapsTo D R H)
    (hHB : ConstructionCutWeights.RangeBound unit H)
    (hUniform : UniformMargins hM w Q D mul H C) :
    ConstructionProbeLetterFloor.HeightOrder D mul R H := by
  refine ⟨hH,fun x c hxc => (hHB x c hxc).1,?_⟩
  intro x y hx hy hxh hyh hxy
  by_cases hyx : ConstructionBaseMonoid.Divides D mul y x
  · have he := ConstructionProbeGateCap.divides_antisymm hm hc
      (ForcingConditionGraphs.function_input hH.1 hxh) hxy hyx
    subst y
    have hv := ForcingConditionGraphs.function_unique hH.1 hxh hyh
    exact fun p hp => hv ▸ hp
  · obtain ⟨cap,sum,_,hSum,hStrict,_⟩ := hUniform x y hx hy hxh hyh hxy hyx
    exact fun p hp => hStrict.1 p ((hSum p).mpr ⟨((hR hx).mp (hH.2 x hx hxh)).1 p hp,Or.inl hp⟩)

/-- Source HeightCost.point_margin in the existing additive contract;
all missed divisors are paid by the SAME uniform bound. -/
theorem point_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul e H C : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hR : CutCarrier hM w Q R) (hH : MapsTo D R H) (hC : MapsTo D R C)
    (hUniform : UniformMargins hM w Q D mul H C) :
    ConstructionProbeCostBounds.PointBound hM w D mul H C := by
  intro x y d hx hy cd hxh hyh hdc hxy hdy hdx
  have hdD := ForcingConditionGraphs.function_input hC.1 hdc
  have hyx : ¬ ConstructionBaseMonoid.Divides D mul y x :=
    fun hyx => hdx (ConstructionProbeGates.divides_trans hm hdD hdy hyx)
  obtain ⟨cap,sum,hcap,hSum,hStrict,hMissed⟩ := hUniform x y hx hy hxh hyh hxy hyx
  have hcdCap := hMissed d cd hdD hdc hdy hdx
  obtain ⟨small,_,hSmall⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ
    ((hR hx).mp (hH.2 x hx hxh)) ((hR cd).mp (hC.2 d cd hdc))
  have hle := ConstructionCutArithmetic.sum_mono hSmall hSum (fun _ hp => hp) hcdCap
  exact (ConstructionCutAddition.bound_iff_subset hQ ((hR hx).mp (hH.2 x hx hxh))
    ((hR cd).mp (hC.2 d cd hdc)) hSmall).mpr (fun p hp => hStrict.1 p (hle p hp))

/-- Execute the original ProbeData request using only its parent weighted
monoid, distinguished nonunit and actual Path. All letter/floor/interval data
and the complete successor/inclusion/request package are CONSTRUCTED. -/
theorem exists_probe_with_source (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul b zero H C one u unit e node mark a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hH : MapsTo D R H) (hHB : ConstructionCutWeights.RangeBound unit H)
    (hC : MapsTo D R C) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hmarkNe : mark ≠ e)
    (hPath : ConstructionProbePath.Path w D mul e zero a node) :
    ∃ S A E Off V projection, ConstructionOperationSource.Alpha w D mul e zero mark a node S A E projection ∧
    ∃ W unitW J G O markN KG P gen oa ob mapped,
      WordCarrier w D S mul A b W ∧ Old zero D e unitW ∧
      ConstructionProbeLetters.Representatives W W J ∧ MapsTo J W G ∧
      ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G ∧
      ForcingDiagramPoset.LeftCancelMonoid W G unitW ∧ ForcingDiagramPoset.Conical W G unitW ∧
      ConstructionProbeSharedIntersections.ConditionalJoins W G ∧
      ConstructionProbeOldEmbedding.OldGraph zero D O ∧
      ConstructionProbeConservative.Conservative D W mul G O ∧
      ConstructionProbeOldEmbeddingSyntax.EmbeddingLaws w D S zero mul A W G e unitW O ∧
      ConstructionPersistentProfiles.HasOldGates D W mul G O ∧
      PureKuratowski.PairMember M mark markN O ∧
      (Project.FirstOrderSemantics.reduct M).mem markN W ∧ markN ≠ unitW ∧
      MapsTo S W KG ∧ ConstructionProbeGenerator.GeneratorGraph w D S unitW KG ∧
      MapsTo w W P ∧ ConstructionProbeIndexedGenerators.ProbeGraph w projection e KG P ∧
      PureKuratowski.PairMember M zero gen P ∧ PureKuratowski.PairMember M a oa O ∧
      PureKuratowski.PairMember M b ob O ∧ ConstructionProbeMappedPath.NodeMap node O mapped ∧
      ConstructionPersistentProfiles.ProbeProfile w W G oa ob markN gen mapped ∧
      (∀ x, ¬ PureKuratowski.PairMember M x gen O) ∧
      (∀ mu, (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
        ForcingSupportSize.Small D mu → ForcingSupportSize.Small W mu) ∧
      (∀ a0 b0 d0 p0 node0, ConstructionPersistentProfiles.ProbeProfile w D mul a0 b0 d0 p0 node0 →
        ∃ mapped0 fa fb fd fp, ConstructionProbeMappedPath.NodeMap node0 O mapped0 ∧
          PureKuratowski.PairMember M a0 fa O ∧ PureKuratowski.PairMember M b0 fb O ∧
          PureKuratowski.PairMember M d0 fd O ∧ PureKuratowski.PairMember M p0 fp O ∧
          ConstructionPersistentProfiles.ProbeProfile w W G fa fb fd fp mapped0) ∧
      ∃ HL GateCap LC, (MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL ∧
      ConstructionCutWeights.RangeBound unit HL ∧ MapsTo W R GateCap ∧
      ConstructionProbeGateCap.Graph D W mul G O C unit GateCap ∧ ConstructionProbeGateCap.Bounds unit GateCap ∧
      MapsTo W R LC ∧ ConstructionProbeCostFold.Laws hM w D S zero W Q C V GateCap LC ∧
      ConstructionProbeGateCap.Bounds unit LC ∧ UniformMargins hM w Q W G HL LC ∧
      (∀ x y hx hy, PureKuratowski.PairMember M x hx HL → PureKuratowski.PairMember M y hy HL →
        ConstructionBaseMonoid.Divides W G x y → ¬ ConstructionBaseMonoid.Divides W G y x →
        ∃ cap sum, Cut hM w Q cap ∧ Cap W G LC x y cap ∧ ConstructionCutAddition.SumCut hM w Q hx cap sum ∧
          ConstructionProbeIntervals.Strict sum hy ∧ ConstructionProbeLetterIntervals.MissedBound W G LC x y cap) ∧
      (∀ L, MapsTo W R L → ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V L → L = HL) ∧
      (∀ L, MapsTo W R L → ConstructionProbeCostFold.Laws hM w D S zero W Q C V GateCap L → L = LC) ∧
      ∀ x y ox oy, PureKuratowski.PairMember M x ox O → PureKuratowski.PairMember M y oy O →
        ∃ f0 f1 cap, Family D mul C x y f0 ∧ Family W G LC ox oy f1 ∧ Cut hM w Q cap ∧
          Cap D mul C x y cap ∧ Cap W G LC ox oy cap ∧
          ∀ c0 c1, Cap D mul C x y c0 → Cap W G LC ox oy c1 → c0 = c1) ∧
      ∀ x ox v, PureKuratowski.PairMember M x ox O →
        (PureKuratowski.PairMember M ox v HL ↔ PureKuratowski.PairMember M x v H) ∧
        (PureKuratowski.PairMember M ox v LC ↔ PureKuratowski.PairMember M x v C) := by
  obtain ⟨pairs,hpairs⟩ := ConstructionProbePath.exists_ordered_pairs hM w
  obtain ⟨factor,_,hFactor⟩ := ConstructionProbePath.exists_factor_table hM hm hPath hpairs
  obtain ⟨T,hTm,hTerminal⟩ := ConstructionProbePath.exists_terminal_table hM hm hPath
  have hTable := ConstructionProbePath.table_laws hM hw hz hm hPath hFactor hTerminal
  have hMeets := ConstructionProbeTransitions.meets_laws hM hw hm hPath hFactor hTable
  obtain ⟨CRep,hRep⟩ := ConstructionProbeLetters.exists_representatives hM w D
  obtain ⟨S,hLetters⟩ := ConstructionProbeLetters.exists_letters hM w D mul factor CRep
  obtain ⟨projection,hProjectionMap,hProjection⟩ := ConstructionProbeLetters.exists_projection hM hLetters
  have hEq := ConstructionProbeLetters.equality_law hM hRep hMeets hProjection
  obtain ⟨I,A,hI,hAMap,hAction⟩ := ConstructionProbeAction.exists_action hM hm hFactor hRep hLetters hProjectionMap hProjection hEq
  have hActionLaws := ConstructionProbeAction.action_laws hM hm hFactor hRep hLetters hProjectionMap hProjection hEq hAction
  obtain ⟨K,hK,hTarget⟩ := ConstructionProbeTarget.exists_target hM hm hFactor hRep hLetters hProjectionMap hProjection hEq hTm hTable
  have hTargetLaws := ConstructionProbeTarget.target_laws hm hFactor hRep hProjectionMap hEq hTm hTable hAction hTarget
  obtain ⟨E,hEm,hExit⟩ := ConstructionProbeAlphabet.exists_exit hM hm hK hmark
  have hAlpha := ConstructionProbeAlphabet.alphabet_laws hm hCon hI hAMap hActionLaws hK hTargetLaws hmark hmarkNe hEm hExit
  have hCone := ConstructionProbeCones.cone_laws hM hm hPath hFactor hTable hRep hLetters hProjectionMap hProjection hEq hMeets hI hAMap hAction hActionLaws hK hTargetLaws
  have hOrder := height_order hM hm hCon hR hH hHB hUniform
  have hPoint := point_bound hM hw hQ hm hR hH hC hUniform
  obtain ⟨F,hF,_,hFloor,hCost⟩ := ConstructionProbeCostBounds.exists_cost_bounds hm hI hAMap hK hTargetLaws hOrder hPoint hCone hw hQ hR hC hJoins hActionLaws
  obtain ⟨digitOne,two,three,hDigits⟩ := ConstructionBaseWeights.digits_exists hw
  obtain ⟨four,hFour,hFourW⟩ := hw.1.2 three hDigits.2.2.1
  obtain ⟨Off,V,B,hOff,hV,hB,_,_,_,hIntervals,_⟩ := ConstructionProbeHeightIntervalGraphs.exists_heightIntervals hM hw hQ hR hm hCon hmark hmarkNe hK hEm hExit hH hC hF hFloor hCost hUniform hDigits hFour hFourW
  refine ⟨S,A,E,Off,V,projection,⟨I,K,factor,T,CRep,hAlpha,hCone,hK,hFactor,hTm,hTerminal,hTargetLaws,hExit,hRep,hProjectionMap,hLetters,hProjection,hAction⟩,?_⟩
  exact ConstructionProbeSuccessor.exists_probe_successor hM hw hz hzw hQ hR hu hone hunit
    hm hCon hAlpha hb hne hH hHB hC hCB hOff hV hB hF hFloor hCost hIntervals hUniform hJoins hCone hmark hmarkNe
    hPath hRep hProjectionMap hTerminal hTargetLaws hExit hLetters hProjection

theorem exists_probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul b zero H C one u unit e node mark a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hH : MapsTo D R H) (hHB : ConstructionCutWeights.RangeBound unit H)
    (hC : MapsTo D R C) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hmarkNe : mark ≠ e)
    (hPath : ConstructionProbePath.Path w D mul e zero a node) :
    ∃ S A E Off V projection, ∃ W unitW J G O markN KG P gen oa ob mapped,
      WordCarrier w D S mul A b W ∧ Old zero D e unitW ∧
      ConstructionProbeLetters.Representatives W W J ∧ MapsTo J W G ∧
      ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G ∧
      ForcingDiagramPoset.LeftCancelMonoid W G unitW ∧ ForcingDiagramPoset.Conical W G unitW ∧
      ConstructionProbeSharedIntersections.ConditionalJoins W G ∧
      ConstructionProbeOldEmbedding.OldGraph zero D O ∧
      ConstructionProbeConservative.Conservative D W mul G O ∧
      ConstructionProbeOldEmbeddingSyntax.EmbeddingLaws w D S zero mul A W G e unitW O ∧
      ConstructionPersistentProfiles.HasOldGates D W mul G O ∧
      PureKuratowski.PairMember M mark markN O ∧
      (Project.FirstOrderSemantics.reduct M).mem markN W ∧ markN ≠ unitW ∧
      MapsTo S W KG ∧ ConstructionProbeGenerator.GeneratorGraph w D S unitW KG ∧
      MapsTo w W P ∧ ConstructionProbeIndexedGenerators.ProbeGraph w projection e KG P ∧
      PureKuratowski.PairMember M zero gen P ∧ PureKuratowski.PairMember M a oa O ∧
      PureKuratowski.PairMember M b ob O ∧ ConstructionProbeMappedPath.NodeMap node O mapped ∧
      ConstructionPersistentProfiles.ProbeProfile w W G oa ob markN gen mapped ∧
      (∀ x, ¬ PureKuratowski.PairMember M x gen O) ∧
      (∀ mu, (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
        ForcingSupportSize.Small D mu → ForcingSupportSize.Small W mu) ∧
      (∀ a0 b0 d0 p0 node0, ConstructionPersistentProfiles.ProbeProfile w D mul a0 b0 d0 p0 node0 →
        ∃ mapped0 fa fb fd fp, ConstructionProbeMappedPath.NodeMap node0 O mapped0 ∧
          PureKuratowski.PairMember M a0 fa O ∧ PureKuratowski.PairMember M b0 fb O ∧
          PureKuratowski.PairMember M d0 fd O ∧ PureKuratowski.PairMember M p0 fp O ∧
          ConstructionPersistentProfiles.ProbeProfile w W G fa fb fd fp mapped0) ∧
      ∃ HL GateCap LC, (MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL ∧
      ConstructionCutWeights.RangeBound unit HL ∧ MapsTo W R GateCap ∧
      ConstructionProbeGateCap.Graph D W mul G O C unit GateCap ∧ ConstructionProbeGateCap.Bounds unit GateCap ∧
      MapsTo W R LC ∧ ConstructionProbeCostFold.Laws hM w D S zero W Q C V GateCap LC ∧
      ConstructionProbeGateCap.Bounds unit LC ∧ UniformMargins hM w Q W G HL LC ∧
      (∀ x y hx hy, PureKuratowski.PairMember M x hx HL → PureKuratowski.PairMember M y hy HL →
        ConstructionBaseMonoid.Divides W G x y → ¬ ConstructionBaseMonoid.Divides W G y x →
        ∃ cap sum, Cut hM w Q cap ∧ Cap W G LC x y cap ∧ ConstructionCutAddition.SumCut hM w Q hx cap sum ∧
          ConstructionProbeIntervals.Strict sum hy ∧ ConstructionProbeLetterIntervals.MissedBound W G LC x y cap) ∧
      (∀ L, MapsTo W R L → ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V L → L = HL) ∧
      (∀ L, MapsTo W R L → ConstructionProbeCostFold.Laws hM w D S zero W Q C V GateCap L → L = LC) ∧
      ∀ x y ox oy, PureKuratowski.PairMember M x ox O → PureKuratowski.PairMember M y oy O →
        ∃ f0 f1 cap, Family D mul C x y f0 ∧ Family W G LC ox oy f1 ∧ Cut hM w Q cap ∧
          Cap D mul C x y cap ∧ Cap W G LC ox oy cap ∧
          ∀ c0 c1, Cap D mul C x y c0 → Cap W G LC ox oy c1 → c0 = c1) ∧
      ∀ x ox v, PureKuratowski.PairMember M x ox O →
        (PureKuratowski.PairMember M ox v HL ↔ PureKuratowski.PairMember M x v H) ∧
        (PureKuratowski.PairMember M ox v LC ↔ PureKuratowski.PairMember M x v C) := by
  obtain ⟨S,A,E,Off,V,projection,_,hResult⟩ := exists_probe_with_source hM
    hw hz hzw hQ hR hu hone hunit hm hCon hb hne hH hHB hC hCB hUniform hJoins hmark hmarkNe hPath
  exact ⟨S,A,E,Off,V,projection,hResult⟩

end PPAC.Migration.ConstructionProbeParent
