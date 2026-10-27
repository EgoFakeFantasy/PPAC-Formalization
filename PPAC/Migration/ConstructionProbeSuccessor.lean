/- Pinned MonoidBase.ProbeData.extension/inclusion:180-196.
Compose the accepted actual profile extension and complete Word HeightCost on the
SAME carrier/embedding. The distinguished nonunit is the image of the old marker.
Actual path/alphabet/interval inputs remain explicit; no final Con claim. -/
import PPAC.Migration.ConstructionProbeHeightCost
import PPAC.Migration.ConstructionProbeOldCostSupremum
import PPAC.Migration.ConstructionPersistentProfiles
import PPAC.Migration.ConstructionProbeWordCardinality

namespace PPAC.Migration.ConstructionProbeSuccessor
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

/-- Actual Probe request, weighted successor and all inclusion fields, under the existing
source path/alphabet/interval producers. No new Word, graph or margin is assumed. -/
theorem exists_probe_successor (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul S A b zero H C Off V B F K E one u unit four e I node factor projection mark a CRep T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hAlpha : ConstructionProbeAlphabet.Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hH : MapsTo D R H) (hHB : ConstructionCutWeights.RangeBound unit H)
    (hC : MapsTo D R C) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hOff : MapsTo S R Off) (hV : MapsTo S R V) (hB : MapsTo S R B) (hF : MapsTo S R F)
    (hFloor : ConstructionProbeLetterFloor.FloorLaws D S A K H F)
    (hCostBounds : ConstructionProbeCostBounds.CostBounds hM w Q D mul S A K H C F)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hCone : ConstructionProbeCones.ConeLaws w D mul e zero node factor S projection A)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D) (hmarkNe : mark ≠ e)
    (hPath : ConstructionProbePath.Path w D mul e zero a node)
    (hRep : ConstructionProbeLetters.Representatives w D CRep)
    (hProjectionMap : MapsTo CRep S projection)
    (hTerminal : ConstructionProbePath.TerminalTable w D mul node a T)
    (hTarget : ConstructionProbeTarget.TargetLaws mul projection T A K)
    (hExit : ConstructionProbeAlphabet.ExitGraph mul K mark E)
    (hLetters : ConstructionProbeLetters.Letters w D mul factor CRep S)
    (hProjection : ConstructionProbeLetters.Projection w D mul factor CRep projection) :
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
  obtain ⟨W,unitW,J,G,KG,P,gen,oa,ad,oad,ob,hW,hUnit,hWW,hGmap,hG,hmW,hcW,hJW,hKG,hGen,hP,hProbe,hp0,hOlda,hProduct,hOldad,hOldb,hProfile⟩ :=
    ConstructionProbeProfiles.exists_profile_extension hM hw hz hzw hm hCon hAlpha hb hne hCone hJoins
      hPath hRep hProjectionMap hTerminal hTarget hExit hmark hmarkNe
  obtain ⟨O,hO,hEmbed,hConservative⟩ := ConstructionProbeConservative.exists_conservative_old hM hw hz hzw hm hAlpha hW hb hG hUnit hCone
  have hEmb := hConservative.1.1
  have hGates := ConstructionPersistentProfiles.probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hG hUnit hO hJoins hConservative
  obtain ⟨mapped,markN,hNodeMap,hOldMark,hInitialProfile⟩ := ConstructionPersistentProfiles.initial_profile hM
    hw hz hzw hm hAlpha hW hb hG hO hEmb hPath.1 (hP.2 zero gen hp0) hOlda hOldb hOldad hmark hProduct hProfile
  have hmarkN := (hO mark markN).mpr hOldMark
  have hmarkNW := hEmb.2 mark markN hmarkN
  have hmarkNe : markN ≠ unitW := by
    intro heq
    exact hmarkNe (hConservative.1.2 mark e unitW (heq ▸ hmarkN) hEmbed.1)
  have hNew : ∀ x, ¬ PureKuratowski.PairMember M x gen O := by
    intro x hx
    obtain ⟨_,s,_,hsg⟩ := (hProbe zero gen).mp hp0
    exact ConstructionProbeRaw.old_ne_cons hz ((hO x gen).mp hx) ((hGen s gen).mp hsg)
  have hSize : ∀ mu, (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu →
      ForcingSupportSize.Small D mu → ForcingSupportSize.Small W mu := by
    intro mu hmu hD
    exact ConstructionProbeWordCardinality.extension_cardinal_le hM hw hmu hD hRep hLetters hProjectionMap hProjection hW
  have hPres : ConstructionProbeLiftHom.PreservesProducts mul G O :=
    fun x y z fx fy fz hp hx hy hzv => hEmbed.2.1 x y z fx fy fz hx hy hzv hp
  have hPersistent := fun a0 b0 d0 p0 node0 (hProfile0 : ConstructionPersistentProfiles.ProbeProfile w D mul a0 b0 d0 p0 node0) =>
    ConstructionPersistentProfiles.exists_mapped_profile hM hm hmW hConservative hPres hGates
      (a := a0) (b := b0) (d := d0) (p := p0) (node := node0) hProfile0
  obtain ⟨HL,GateCap,LC,hWeights⟩ := ConstructionProbeHeightCost.exists_heightCost hM hw hz hzw hQ hR hu hone hunit
    hm hCon hAlpha hb hne hW hG hUnit hEmb hO hH hHB hC hCB hOff hV hB hF hFloor hCostBounds hI hUniform hJoins hConservative
  have hHeight := hWeights.2.1
  have hCost := hWeights.2.2.2.2.2.2.2.1
  refine ⟨W,unitW,J,G,O,markN,KG,P,gen,oa,ob,mapped,hW,hUnit,hWW,hGmap,hG,hmW,hcW,hJW,hO,hConservative,hEmbed,hGates,hmarkN,hmarkNW,hmarkNe,
    hKG,hGen,hP,hProbe,hp0,(hO a oa).mpr hOlda,(hO b ob).mpr hOldb,hNodeMap,hInitialProfile,hNew,hSize,hPersistent,
    HL,GateCap,LC,hWeights,?_⟩
  intro x ox v hxo
  exact ⟨hHeight.1 x ox v ((hO x ox).mp hxo),hCost.1 x ox v ((hO x ox).mp hxo)⟩

end PPAC.Migration.ConstructionProbeSuccessor
