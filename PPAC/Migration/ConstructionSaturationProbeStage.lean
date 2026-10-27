/- Pinned SaturatedMonoids.probe_stage:24.
Use the accepted SAME-tower countable_stage on the actual countable parameter
range plus {a,b}. Reflect the full path using the existing conservative map.
No external countability or newly postulated reflected path. -/
import PPAC.Migration.ConstructionSaturationCover

namespace PPAC.Migration.ConstructionSaturationProbeStage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ForcingSupportSize (MapsTo Small)
open ForcingConditionGraphs (function_input function_unique)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbePath (Path)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem parameters (hM : FirstOrder.Theory.Models M nativeZF)
    {w N a b node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a N)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b N) (hNode : MapsTo w N node) :
    ∃ S, (Project.FirstOrderSemantics.reduct M).MemberSubset S N ∧
      (Project.FirstOrderSemantics.reduct M).mem a S ∧ (Project.FirstOrderSemantics.reduct M).mem b S ∧
      MapsTo w S node ∧ Small S w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hNative := (ForcingSupportSize.native_mapsTo hM w N node).mp hNode
  obtain ⟨range,hRange⟩ := ZF.exists_range_of_setFunction hZF I hNative.1 hNative.2.1
  have hRangeSub : rawM.MemberSubset range N := by
    intro x hx
    obtain ⟨i,hix⟩ := (hRange x).mp hx
    exact hNative.output_mem_of_pairMember hix
  have hToRange : rawM.IsSetFunctionFromTo I node w range :=
    ⟨hNative.1,hNative.2.1,fun i hi => by
      obtain ⟨x,_,hix⟩ := hNative.2.2 i hi
      exact ⟨x,(hRange x).mpr ⟨i,hix⟩,hix⟩⟩
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF I w
  have hInfinite : rawM.IsInfiniteCardinal I w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l I hZF hw,id,hId.1⟩
  have hRangeSmall := ExistingOrdinalImage.ordinal_image_bound_l I hZF hInfinite.1.1
    ⟨id,hId.1⟩ hToRange (fun x hx => by
      obtain ⟨i,hix⟩ := (hRange x).mp hx
      exact ⟨i,hNative.input_mem_of_pairMember hix,hix⟩)
  obtain ⟨z,_,hzw⟩ := hw.1.1
  have single_small {x S} (hS : ∀ v, rawM.mem v S ↔ v = x) : rawM.CardinalLessOrEqual I S w := by
    obtain ⟨f,hf,_⟩ := ZF.exists_constantFunction hZF I (source := S) hzw
    refine ⟨f,hf,fun p q v hp hq => ?_⟩
    exact ((hS p).mp (hf.input_mem_of_pairMember hp)).trans
      ((hS q).mp (hf.input_mem_of_pairMember hq)).symm
  obtain ⟨sa,hsa⟩ := KP.exists_singleton hKP a
  obtain ⟨sb,hsb⟩ := KP.exists_singleton hKP b
  obtain ⟨pair,hPair⟩ := KP.exists_unionOfTwo hKP sa sb
  have hPairSmall := ExistingCardinalBounds.infinite_union_two_l I hZF hw hInfinite
    (single_small hsa) (single_small hsb) hPair
  obtain ⟨S,hS⟩ := KP.exists_unionOfTwo hKP range pair
  have hSmall := ExistingCardinalBounds.infinite_union_two_l I hZF hw hInfinite hRangeSmall hPairSmall hS
  refine ⟨S,?_,(hS a).mpr (Or.inr ((hPair a).mpr (Or.inl ((hsa a).mpr rfl)))),
    (hS b).mpr (Or.inr ((hPair b).mpr (Or.inr ((hsb b).mpr rfl)))),?_,
    (ForcingSupportSize.native_small hM S w).mpr hSmall⟩
  · intro x hx
    rcases (hS x).mp hx with hx | hx
    · exact hRangeSub x hx
    · rcases (hPair x).mp hx with hx | hx
      · exact ((hsa x).mp hx) ▸ ha
      · exact ((hsb x).mp hx) ▸ hb
  · refine ⟨hNode.1,fun i x hix => ?_⟩
    exact (hS x).mpr (Or.inl ((hRange x).mpr ⟨i,hix⟩))

theorem reflect_path
    {w D N mul mulN e eN zero a fa node mapped f : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hmN : ForcingDiagramPoset.LeftCancelMonoid N mulN eN)
    (hCons : ConstructionProbeConservative.Conservative D N mul mulN f)
    (hPres : ConstructionProbeLiftHom.PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f)
    (ha : PureKuratowski.PairMember M a fa f)
    (hNode : MapsTo w D node) (hMap : NodeMap node f mapped)
    (hPath : Path w N mulN eN zero fa mapped) : Path w D mul e zero a node := by
  refine ⟨hNode,function_input hCons.1.1.1 ha,?_,?_,?_⟩
  · obtain ⟨x,hzx,hxe⟩ := (hMap zero eN).mp hPath.2.2.1
    have he := hCons.1.2 x e eN hxe hOne
    exact he ▸ hzx
  · intro i j hi hj hij
    obtain ⟨factor,ni,nj,hni,hnj,hfactor,hprod⟩ := hPath.2.2.2.1 i j hi hj hij
    obtain ⟨xi,hxi,hfxi⟩ := (hMap i ni).mp hni
    obtain ⟨xj,hxj,hfxj⟩ := (hMap j nj).mp hnj
    obtain ⟨t,ht,hxt⟩ := ConstructionProbeAlphabetMap.factor_eq hm hmN hCons.1 hPres hCons.2.1
      hfxi hfxj hfactor hprod
    exact ⟨t,xi,xj,hxi,hxj,function_input hCons.1.1.1 ht,hxt⟩
  · intro i hi
    obtain ⟨factor,ni,hni,hfactor,hprod⟩ := hPath.2.2.2.2 i hi
    obtain ⟨xi,hxi,hfxi⟩ := (hMap i ni).mp hni
    obtain ⟨t,ht,hxt⟩ := ConstructionProbeAlphabetMap.factor_eq hm hmN hCons.1 hPres hCons.2.1
      hfxi ha hfactor hprod
    exact ⟨t,xi,hxi,function_input hCons.1.1.1 ht,hxt⟩

def ProbeStage (w zero history F kappa a b node : M.Carrier .set) : Prop :=
  ∃ j D mul e mark H C incoming base leg a0 b0 node0,
    (Project.FirstOrderSemantics.reduct M).mem j kappa ∧
    Row history j D mul e mark H C incoming base j ∧ ForcingDiagramOrder.Product F j kappa leg ∧
    PureKuratowski.PairMember M a0 a leg ∧ PureKuratowski.PairMember M b0 b leg ∧
    NodeMap node0 leg node ∧ Path w D mul e zero a0 node0 ∧
    (Project.FirstOrderSemantics.reduct M).mem b0 D ∧ b0 ≠ e

theorem probe_stage (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C B history F P zero kappa
      N mulN eN markN HN CN incoming base a b node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hB : (Project.FirstOrderSemantics.reduct M).IsOrdinal B)
    (hV : Valid hM w Q R top D mul e mark H C B history)
    (hCover : ConstructionSaturationCover.Covered w history F kappa)
    (hF : ConstructionTowerTransitions.Matrix B history zero P F)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B)
    (hRow : Row history kappa N mulN eN markN HN CN incoming base kappa)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b N) (hne : b ≠ eN)
    (hPath : Path w N mulN eN zero a node) : ProbeStage w zero history F kappa a b node := by
  obtain ⟨S,hSub,haS,hbS,hNodeS,hSmall⟩ := parameters hM hw hPath.2.1 hb hPath.1
  obtain ⟨identity,hPerm,hIdentity⟩ := ForcingConditionGraphs.exists_identity hM S
  have hIdentityMaps : MapsTo S N identity := ⟨hPerm.1.1,fun x y hxy => hSub y (hPerm.1.2 x y hxy)⟩
  obtain ⟨j,D0,mul0,e0,mark0,H0,C0,in0,base0,leg,lift,hj,hRow0,hLeg,hLift,hComposition⟩ :=
    hCover N mulN eN markN HN CN incoming base S identity hRow hSmall hIdentityMaps
  have hjB := hB.transitive kappa hk j hj
  have hLegIn := (ConstructionTowerTransitions.matrix_at hV.1 hF hjB hk (Or.inl hj)
    (row_field 6 hRow)).mp hLeg
  have hMap := (hV.2.2.1 j kappa D0 mul0 e0 mark0 H0 C0 in0 base0
    N mulN eN markN HN CN incoming base leg hjB hk (Or.inl hj) hRow0 hRow hLegIn).1
  have hObject0 := (hV.2.1 j hjB D0 mul0 e0 mark0 H0 C0 in0 base0 hRow0).1
  have hObjectN := (hV.2.1 kappa hk N mulN eN markN HN CN incoming base hRow).1
  have retract {x y} (hx : (Project.FirstOrderSemantics.reduct M).mem x S)
      (hxy : PureKuratowski.PairMember M x y lift) : PureKuratowski.PairMember M y x leg := by
    obtain ⟨z,hxz,hzx⟩ := (hComposition x x).mp ((hIdentity x x).mpr ⟨hx,rfl⟩)
    exact (function_unique hLift.1 hxz hxy) ▸ hzx
  obtain ⟨a0,ha0,_⟩ := hLift.1.2 a haS
  obtain ⟨b0,hb0,_⟩ := hLift.1.2 b hbS
  obtain ⟨node0,hNode0,hNodeMap⟩ := ConstructionProbeMappedPath.exists_node_map hM hNodeS hLift
  have hFinalNode : NodeMap node0 leg node := by
    intro i x
    constructor
    · intro hix
      have hxS := hNodeS.2 i x hix
      obtain ⟨y,hxy,_⟩ := hLift.1.2 x hxS
      exact ⟨y,(hNodeMap i y).mpr ⟨x,hix,hxy⟩,retract hxS hxy⟩
    · rintro ⟨y,hiy,hyx⟩
      obtain ⟨x',hix',hx'y⟩ := (hNodeMap i y).mp hiy
      have he := ((hIdentity x' x).mp ((hComposition x' x).mpr ⟨y,hx'y,hyx⟩)).2
      exact he ▸ hix'
  have haLeg := retract haS ha0
  have hbLeg := retract hbS hb0
  have hPath0 := reflect_path hObject0.1 hObjectN.1 hMap.1 hMap.2.1 hMap.2.2.1
    haLeg hNode0 hFinalNode hPath
  refine ⟨j,D0,mul0,e0,mark0,H0,C0,in0,base0,leg,a0,b0,node0,hj,hRow0,hLeg,haLeg,hbLeg,
    hFinalNode,hPath0,hLift.2 b b0 hb0,?_⟩
  intro he
  exact hne (function_unique hMap.1.1.1.1 (he ▸ hbLeg) hMap.2.2.1)

end PPAC.Migration.ConstructionSaturationProbeStage
