/- Pinned cost_le_gate/cost_old_factor. Reuse the completed old-image
reflection and HasOldGates profile; no gate-existence or join proof is rebuilt. -/
import PPAC.Migration.ConstructionProbeCostFold

namespace PPAC.Migration.ConstructionProbeOldCostFactors
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (Old Cons)
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeGateCap (OldMinimum)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The precise existing old-embedding field, kept on the same graph. -/
def Reflection (D W mul G Emb : M.Carrier .set) : Prop := ∀ x y ox oy,
  PureKuratowski.PairMember M x ox Emb → PureKuratowski.PairMember M y oy Emb →
    (Divides W G ox oy ↔ Divides D mul x y)

theorem reflection_of_embedding {w D S zero mul A W G e unitW Emb : M.Carrier .set}
    (h : ConstructionProbeOldEmbeddingSyntax.EmbeddingLaws w D S zero mul A W G e unitW Emb) :
    Reflection D W mul G Emb := h.2.2.2.1

theorem minimum_of_image {D W mul G Emb x q : M.Carrier .set}
    (hEmb : MapsTo D W Emb) (hDiv : Reflection D W mul G Emb)
    (hxq : PureKuratowski.PairMember M x q Emb) : OldMinimum D W mul G Emb q x :=
  ⟨ForcingConditionGraphs.function_input hEmb.1 hxq,fun y oy hy => hDiv x y q oy hxq hy⟩

/-- The source cap equation and min bound, for every least old right multiple. -/
theorem cost_le_minimum (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb C V Cap LC e G unit q g c cg : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C) (hCap : MapsTo W R Cap)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hDiv : Reflection D W mul G Emb)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hMin : OldMinimum D W mul G Emb q g)
    (hcg : PureKuratowski.PairMember M g cg C) (hqc : PureKuratowski.PairMember M q c LC) : Subset c cg := by
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw (ConstructionProbeWord.word_raw hW hq) with ⟨x,hxq⟩ | ⟨s,t,hCons⟩
  · have hMinX := minimum_of_image hEmb hDiv ((hOld x q).mpr hxq)
    have he := ConstructionProbeGateCap.minimum_unique hm hCon hEmb hMin hMinX
    subst g
    have he := ForcingConditionGraphs.function_unique hC.1 ((hL.1 x q c hxq).mp hqc) hcg
    exact fun p hp => he ▸ hp
  · obtain ⟨v,_,d,prod,cap,_,_,hcap,hmin⟩ := (hL.2 s t q c hCons hq).mp hqc
    have hgate := ConstructionProbeGateCap.cap_eq hCapG hq hMin hcg
    have he := ForcingConditionGraphs.function_unique hCap.1 hcap hgate
    exact fun p hp => he ▸ ((ConstructionCutMinimum.value_bounds hmin).2 p hp)

/-- Exact source old-factor conclusion, using the already completed old/gate
alternatives and actual old-image profile. All witnesses are internal. -/
theorem cost_old_factor (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb C V Cap LC e G unit q y oy c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C) (hCap : MapsTo W R Cap)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit Cap)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V Cap LC)
    (hDiv : Reflection D W mul G Emb) (hGates : ConstructionPersistentProfiles.HasOldGates D W mul G Emb)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hy : PureKuratowski.PairMember M y oy Emb)
    (hqy : Divides W G q oy) (hqc : PureKuratowski.PairMember M q c LC) :
    ∃ g og cg, PureKuratowski.PairMember M g og Emb ∧ PureKuratowski.PairMember M g cg C ∧
      OldMinimum D W mul G Emb q g ∧ Divides W G q og ∧ Divides D mul g y ∧ Subset c cg := by
  have hFactor : ∃ g og, PureKuratowski.PairMember M g og Emb ∧ OldMinimum D W mul G Emb q g ∧ Divides W G q og := by
    rcases hGates q hq ⟨y,oy,hy,hqy⟩ with ⟨g,hgq⟩ | ⟨g,og,hgate⟩
    · have hg := ForcingConditionGraphs.function_input hEmb.1 hgq
      exact ⟨g,q,hgq,minimum_of_image hEmb hDiv hgq,
        (hDiv g g q q hgq hgq).mpr ⟨e,hm.1.1,(hm.1.2 g hg g).2.mpr rfl⟩⟩
    · exact ⟨g,og,hgate.1,ConstructionProbeGateCap.minimum_of_oldGate hEmb hgate,hgate.2.1⟩
  obtain ⟨g,og,hg,hmin,hqg⟩ := hFactor
  obtain ⟨cg,hcg,_⟩ := hC.1.2 g hmin.1
  exact ⟨g,og,cg,hg,hcg,hmin,hqg,(hmin.2 y oy hy).mp hqy,
    cost_le_minimum hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hq hmin hcg hqc⟩

end PPAC.Migration.ConstructionProbeOldCostFactors
