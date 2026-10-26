/- Pinned ProbeMargins.Word.old_cost_supremum:515.
Reuse the existing exact Family/Cap/bounded_union and cost_old_factor. Old
costs embed unchanged; every new missed cost is dominated by an old missed cost. -/
import PPAC.Migration.ConstructionProbeCostMargins
import PPAC.Migration.ConstructionProbeCostSupremum

namespace PPAC.Migration.ConstructionProbeOldCostSupremum
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionBaseMonoid (Divides)
open ConstructionProbeOldCostFactors (Reflection)
open ConstructionProbeCostSupremum (CostMember Family Cap)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source S0 subset S1, using the literal old cost equation. -/
theorem old_member_image (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul W Q Emb C V CapGraph LC G x y ox oy cd : M.Carrier .set}
    (hEmb : MapsTo D W Emb) (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V CapGraph LC)
    (hDiv : Reflection D W mul G Emb)
    (hxo : PureKuratowski.PairMember M x ox Emb) (hyo : PureKuratowski.PairMember M y oy Emb)
    (hMember : CostMember D mul C x y cd) : CostMember W G LC ox oy cd := by
  obtain ⟨g,hg,hgc,hgy,hgx⟩ := hMember
  obtain ⟨og,hgo,_⟩ := hEmb.1.2 g hg
  exact ⟨og,hEmb.2 g og hgo,(hL.1 g og cd ((hOld g og).mp hgo)).mpr hgc,
    (hDiv g y og oy hgo hyo).mpr hgy,fun h => hgx ((hDiv g x og ox hgo hxo).mp h)⟩

/-- Source pointwise old domination, on all internal missed divisor codes. -/
theorem new_member_dominated (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb C V CapGraph LC e G unit unitW x y ox oy cd : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : ConstructionProbeWord.WordCarrier w D S mul A b W)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hmW : ForcingDiagramPoset.LeftCancelMonoid W G unitW)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C) (hCap : MapsTo W R CapGraph)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit CapGraph)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V CapGraph LC)
    (hDiv : Reflection D W mul G Emb) (hGates : ConstructionPersistentProfiles.HasOldGates D W mul G Emb)
    (hxo : PureKuratowski.PairMember M x ox Emb) (hyo : PureKuratowski.PairMember M y oy Emb)
    (hMember : CostMember W G LC ox oy cd) : ∃ cg, CostMember D mul C x y cg ∧ Subset cd cg := by
  obtain ⟨q,hq,hqc,hqy,hqx⟩ := hMember
  obtain ⟨g,og,cg,hgo,hgc,hMin,hqg,hgy,hBound⟩ :=
    ConstructionProbeOldCostFactors.cost_old_factor hM hw hz hzw hW hm hCon hEmb hOld hC hCap hCapG hL hDiv hGates hq hyo hqy hqc
  refine ⟨cg,⟨g,hMin.1,hgc,hgy,?_⟩,hBound⟩
  intro hgx
  exact hqx (ConstructionProbeGates.divides_trans hmW hq hqg ((hDiv g x og ox hgo hxo).mpr hgx))

/-- Construct both actual missed-cost families and their SAME unique supremum.
This includes empty families and arbitrary old endpoints without x<=y. -/
theorem exists_common_cap (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Emb C V CapGraph LC e G unit unitW x y ox oy : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hR : CutCarrier hM w Q R) (hUnit : (Project.FirstOrderSemantics.reduct M).mem unit R)
    (hW : ConstructionProbeWord.WordCarrier w D S mul A b W)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hmW : ForcingDiagramPoset.LeftCancelMonoid W G unitW)
    (hCon : ForcingDiagramPoset.Conical D mul e) (hEmb : MapsTo D W Emb)
    (hOld : ConstructionProbeOldEmbedding.OldGraph zero D Emb) (hC : MapsTo D R C)
    (hLC : MapsTo W R LC) (hCap : MapsTo W R CapGraph)
    (hCapG : ConstructionProbeGateCap.Graph D W mul G Emb C unit CapGraph)
    (hL : ConstructionProbeCostFold.Laws hM w D S zero W Q C V CapGraph LC)
    (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hDiv : Reflection D W mul G Emb) (hGates : ConstructionPersistentProfiles.HasOldGates D W mul G Emb)
    (hxo : PureKuratowski.PairMember M x ox Emb) (hyo : PureKuratowski.PairMember M y oy Emb) :
    ∃ f0 f1 cap, Family D mul C x y f0 ∧ Family W G LC ox oy f1 ∧ Cut hM w Q cap ∧
      Cap D mul C x y cap ∧ Cap W G LC ox oy cap ∧
      ∀ c0 c1, Cap D mul C x y c0 → Cap W G LC ox oy c1 → c0 = c1 := by
  obtain ⟨f0,hF0,hF0R⟩ := ConstructionProbeCostSupremum.exists_family hM (x := x) (y := y) hC
  obtain ⟨f1,hF1,_⟩ := ConstructionProbeCostSupremum.exists_family hM (mul := G) (x := ox) (y := oy) hLC
  have hUpper : ∀ bound, UpperBound f0 bound ↔ UpperBound f1 bound := by
    intro bound
    constructor
    · intro h cd hcd
      obtain ⟨cg,hcg,hLe⟩ := new_member_dominated hM hw hz hzw hW hm hmW hCon hEmb hOld hC hCap hCapG hL hDiv hGates hxo hyo ((hF1 cd).mp hcd)
      exact fun p hp => h cg ((hF0 cg).mpr hcg) p (hLe p hp)
    · intro h cd hcd
      exact h cd ((hF1 cd).mpr (old_member_image hM hEmb hOld hL hDiv hxo hyo ((hF0 cd).mp hcd)))
  have hUnitBound : UpperBound f0 unit := by
    intro cd hcd
    obtain ⟨g,_,hgc,_,_⟩ := (hF0 cd).mp hcd
    exact (hCB g cd hgc).2
  obtain ⟨cap,hCapCut,hUB,hLeast⟩ := bounded_union hM hR hF0R ((hR unit).mp hUnit) hUnitBound
  have hOldCap : Cap D mul C x y cap := ⟨f0,hF0,hUB,hLeast⟩
  have hNewCap : Cap W G LC ox oy cap :=
    ⟨f1,hF1,(hUpper cap).mp hUB,fun t ht => hLeast t ((hUpper t).mpr ht)⟩
  exact ⟨f0,f1,cap,hF0,hF1,hCapCut,hOldCap,hNewCap,fun c0 c1 hc0 hc1 =>
    (ConstructionProbeCostSupremum.cap_unique hM hOldCap hc0).symm.trans
      (ConstructionProbeCostSupremum.cap_unique hM hNewCap hc1)⟩

end PPAC.Migration.ConstructionProbeOldCostSupremum
