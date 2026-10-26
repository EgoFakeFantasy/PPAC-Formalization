/- Pinned ProbeMargins.Word.heightCost:494 and old_cost_supremum:515.
Construct actual SAME-W height/cap/cost graphs and all HeightCost fields;
consume the complete object-formula Raw induction rather than margin oracles. -/
import PPAC.Migration.ConstructionProbeUniformMargins
import PPAC.Migration.ConstructionProbeOldCostSupremum

namespace PPAC.Migration.ConstructionProbeHeightCost
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

/-- Source HeightCost on all internal Word elements, with exact equations,
whole-graph uniqueness and old missed-cost supremum preservation. -/
theorem exists_heightCost (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R D mul S A b zero W Emb H C Off V B F K E one u unit four e G unitW I : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : Carrier w Q) (hR : CutCarrier hM w Q R)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hAlpha : ConstructionProbeAlphabet.Alphabet D mul e S I A E)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hne : b ≠ e)
    (hW : WordCarrier w D S mul A b W)
    (hMult : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hUnit : Old zero D e unitW) (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hH : MapsTo D R H) (hHB : ConstructionCutWeights.RangeBound unit H)
    (hC : MapsTo D R C) (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hOff : MapsTo S R Off) (hV : MapsTo S R V) (hB : MapsTo S R B) (hF : MapsTo S R F)
    (hFloor : ConstructionProbeLetterFloor.FloorLaws D S A K H F)
    (hCostBounds : ConstructionProbeCostBounds.CostBounds hM w Q D mul S A K H C F)
    (hI : ConstructionProbeHeightIntervalGraphs.Laws hM w Q four D mul S A K E H C F Off V B)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hConservative : ConstructionProbeConservative.Conservative D W mul G Emb) :
    ∃ HL GateCap LC, MapsTo W R HL ∧ ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL ∧
      ConstructionCutWeights.RangeBound unit HL ∧ MapsTo W R GateCap ∧
      ConstructionProbeGateCap.Graph D W mul G Emb C unit GateCap ∧ ConstructionProbeGateCap.Bounds unit GateCap ∧
      MapsTo W R LC ∧ ConstructionProbeCostFold.Laws hM w D S zero W Q C V GateCap LC ∧
      ConstructionProbeGateCap.Bounds unit LC ∧ UniformMargins hM w Q W G HL LC ∧
      (∀ x y hx hy, PureKuratowski.PairMember M x hx HL → PureKuratowski.PairMember M y hy HL →
        ConstructionBaseMonoid.Divides W G x y → ¬ ConstructionBaseMonoid.Divides W G y x →
        ∃ cap sum, Cut hM w Q cap ∧ Cap W G LC x y cap ∧ ConstructionCutAddition.SumCut hM w Q hx cap sum ∧
          ConstructionProbeIntervals.Strict sum hy ∧ ConstructionProbeLetterIntervals.MissedBound W G LC x y cap) ∧
      (∀ L, MapsTo W R L → ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V L → L = HL) ∧
      (∀ L, MapsTo W R L → ConstructionProbeCostFold.Laws hM w D S zero W Q C V GateCap L → L = LC) ∧
      ∀ x y ox oy, PureKuratowski.PairMember M x ox Emb → PureKuratowski.PairMember M y oy Emb →
        ∃ f0 f1 cap, Family D mul C x y f0 ∧ Family W G LC ox oy f1 ∧ Cut hM w Q cap ∧
          Cap D mul C x y cap ∧ Cap W G LC ox oy cap ∧
          ∀ c0 c1, Cap D mul C x y c0 → Cap W G LC ox oy c1 → c0 = c1 := by
  obtain ⟨HL,GateCap,LC,hHL,hHeight,hHBNew,hCap,hCapG,hCapB,hLC,hCost,hCBNew,_,hHU,hCU⟩ :=
    ConstructionProbeWeightBounds.exists_bounded_weights hM hw hz hzw hQ hR hu hone hunit hm hCon hW hEmb hOld hH hHB hC hCB hOff hV hB hF hI
  have hMargin := ConstructionProbeUniformMargins.uniform_margin hM hw hz hzw hQ hR hu hone hunit hm hCon hAlpha hb hne hW hMult hUnit hEmb hOld hH hC hF hOff hV hB hHL hLC hCap hFloor hCostBounds hI hHeight hCapG hCost hHBNew hCBNew hUniform hJoins hConservative
  have hSupMargin : ∀ x y hx hy, PureKuratowski.PairMember M x hx HL → PureKuratowski.PairMember M y hy HL →
      ConstructionBaseMonoid.Divides W G x y → ¬ ConstructionBaseMonoid.Divides W G y x →
      ∃ cap sum, Cut hM w Q cap ∧ Cap W G LC x y cap ∧ ConstructionCutAddition.SumCut hM w Q hx cap sum ∧
        ConstructionProbeIntervals.Strict sum hy ∧ ConstructionProbeLetterIntervals.MissedBound W G LC x y cap := by
    intro x y hx hy hxh hyh hxy hyx
    exact ConstructionProbeCostSupremum.canonical_uniform hM hw hQ hR hLC ((hR hx).mp (hHL.2 x hx hxh))
      (hMargin x y hx hy hxh hyh hxy hyx)
  have hUnitR := (hR unit).mpr (principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hu⟩) hunit)
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult
  have hEmbed := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hMult hOld
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  have hGates := ConstructionPersistentProfiles.probe_has_old_gates hM hw hz hzw hm hAlpha hW hb hMult hUnit hOld hJoins hConservative
  exact ⟨HL,GateCap,LC,hHL,hHeight,hHBNew,hCap,hCapG,hCapB,hLC,hCost,hCBNew,hMargin,hSupMargin,hHU,hCU,
    fun _ _ _ _ hxo hyo => ConstructionProbeOldCostSupremum.exists_common_cap hM hw hz hzw hR hUnitR hW hm hmW hCon hEmb hOld hC hLC hCap hCapG hCost hCB hDiv hGates hxo hyo⟩

end PPAC.Migration.ConstructionProbeHeightCost
