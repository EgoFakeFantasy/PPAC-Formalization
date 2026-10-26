/- Pinned ProbeMargins cost_le_gate, cost_other_block_factor and
uniform_margin_old. Consume the existing literal Gate/ExitGates and old factor;
no gate existence, old embedding, Word induction or arithmetic is rebuilt. -/
import PPAC.Migration.ConstructionProbeOldCostFactors
import PPAC.Migration.ConstructionProbeHeightFold
import PPAC.Migration.ConstructionProbeLetterIntervals

namespace PPAC.Migration.ConstructionProbeCostMargins
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (Old)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeGates (Gate HeadSome)
open ConstructionProbeOldCostFactors (Reflection cost_le_minimum cost_old_factor)
open ConstructionProbeLetterIntervals (UniformAt UniformMargins)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The already proved literal Gate profile is exactly OldMinimum. -/
theorem minimum_of_gate {w D S zero mul A W G Emb q s g : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hg : (Project.FirstOrderSemantics.reduct M).mem g D)
    (hGate : Gate w D S zero mul A W G q s g) :
    ConstructionProbeGateCap.OldMinimum D W mul G Emb q g := by
  refine ⟨hg,?_⟩
  intro y oy hy
  exact ConstructionProbeGates.gate_dvd_old_iff hz hGate ((hOld y oy).mp hy) (hEmb.2 y oy hy)

/-- Source cost_le_gate, with the literal native Gate rather than an oracle. -/
theorem cost_le_gate (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb C V Cap LC e G unit q s g c cg : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C) (hCap : MapsTo W R Cap)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hDiv : Reflection D W mul G Emb)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hg : (Project.FirstOrderSemantics.reduct M).mem g D)
    (hGate : Gate w D S zero mul A W G q s g)
    (hcg : PureKuratowski.PairMember M g cg C) (hqc : PureKuratowski.PairMember M q c LC) : Subset c cg :=
  cost_le_minimum hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hq
    (minimum_of_gate hz hEmb hOld hg hGate) hcg hqc

/-- Source outside-block factor, reusing the existing exit-gate producer. -/
theorem cost_other_block_factor (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb C V Cap LC e G unit unitW q z s c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C) (hCap : MapsTo W R Cap)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hEmbed : ConstructionProbeOldEmbeddingSyntax.EmbeddingLaws w D S zero mul A W G e unitW Emb)
    (hExit : ConstructionProbeConditionalJoins.ExitGates w D S zero mul A W G)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W)
    (hqHead : ¬ HeadSome w D S q s) (hzHead : HeadSome w D S z s)
    (hqz : Divides W G q z) (hqc : PureKuratowski.PairMember M q c LC) :
    ∃ g og cg, PureKuratowski.PairMember M g og Emb ∧ PureKuratowski.PairMember M g cg C ∧
      Divides W G q og ∧ Divides W G og z ∧ Subset c cg := by
  have hDiv := ConstructionProbeOldCostFactors.reflection_of_embedding hEmbed
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw (ConstructionProbeWord.word_raw hW hq) with ⟨g,hgq⟩ | ⟨t,tail,hCons⟩
  · have hgEmb := (hOld g q).mpr hgq
    have hg := ForcingConditionGraphs.function_input hEmb.1 hgEmb
    obtain ⟨cg,hcg,_⟩ := hC.1.2 g hg
    have he := ForcingConditionGraphs.function_unique hC.1 ((hL.1 g q c hgq).mp hqc) hcg
    exact ⟨g,q,cg,hgEmb,hcg,(hDiv g g q q hgEmb hgEmb).mpr
      ⟨e,hm.1.1,(hm.1.2 g hg g).2.mpr rfl⟩,hqz,fun p hp => he ▸ hp⟩
  · have hzNot : ¬ HeadSome w D S z t := by
      intro hzt
      have hts := ConstructionProbeGates.head_unique hM hw hzt hzHead
      subst t
      exact hqHead ⟨tail,hCons⟩
    obtain ⟨g,hg,hGate⟩ := hExit q t z hq ⟨tail,hCons⟩ hzW hqz hzNot
    obtain ⟨og,hgEmb,_⟩ := hEmb.1.2 g hg
    obtain ⟨cg,hcg,_⟩ := hC.1.2 g hg
    have hMin := minimum_of_gate hz hEmb hOld hg hGate
    have hqg := (hMin.2 g og hgEmb).mpr ⟨e,hm.1.1,(hm.1.2 g hg g).2.mpr rfl⟩
    have hgz := (hEmbed.2.2.2.2 g og z hgEmb hzW).mpr ((hGate z hzW).mp ⟨hqz,hzNot⟩)
    exact ⟨g,og,cg,hgEmb,hcg,hqg,hgz,
      cost_le_gate hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hq hg hGate hcg hqc⟩

/-- Source old-old strict margin on the same actual height/cost graphs. -/
theorem uniform_margin_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb H C Off V Cap HL LC e G unit unitW x y ox oy hx hy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hmW : ForcingDiagramPoset.LeftCancelMonoid W G unitW)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C) (hCap : MapsTo W R Cap)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hHeight : ConstructionProbeHeightFold.Laws hM w D S zero W Q H Off V HL)
    (hDiv : Reflection D W mul G Emb) (hGates : ConstructionPersistentProfiles.HasOldGates D W mul G Emb)
    (hUniform : UniformMargins hM w Q D mul H C)
    (hxo : PureKuratowski.PairMember M x ox Emb) (hyo : PureKuratowski.PairMember M y oy Emb)
    (hxh : PureKuratowski.PairMember M ox hx HL) (hyh : PureKuratowski.PairMember M oy hy HL)
    (hxy : Divides D mul x y) (hNot : ¬ Divides D mul y x) : UniformAt hM w Q W G LC ox oy hx hy := by
  have hxOld := (hOld x ox).mp hxo
  have hyOld := (hOld y oy).mp hyo
  obtain ⟨bound,sum,hBound,hSum,hStrict,hMissed⟩ := hUniform x y hx hy
    ((hHeight.1 x ox hx hxOld).mp hxh) ((hHeight.1 y oy hy hyOld).mp hyh) hxy hNot
  refine ⟨bound,sum,hBound,hSum,hStrict,?_⟩
  intro q c hq hqc hqy hqx
  obtain ⟨g,og,cg,hgo,hgc,hMin,hqg,hgy,hCost⟩ :=
    cost_old_factor hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hGates hq hyo hqy hqc
  have hgNot : ¬ Divides D mul g x := by
    intro hgx
    exact hqx (ConstructionProbeGates.divides_trans hmW hq hqg ((hDiv g x og ox hgo hxo).mpr hgx))
  exact fun p hp => hMissed g cg hMin.1 hgc hgy hgNot p (hCost p hp)

end PPAC.Migration.ConstructionProbeCostMargins
