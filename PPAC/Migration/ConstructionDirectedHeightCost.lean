/- Pinned DirectLimits.cost_le_old_sup:222 / old_cost_supremum:251 /
heightCost:295. Same actual monoid and two actual descended weight graphs.
Preserve the actual least upper bound, including empty/incomparable intervals. -/
import PPAC.Migration.ConstructionDirectedWeights

namespace PPAC.Migration.ConstructionDirectedHeightCost
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family HomLaws ConicalFamily)
open ConstructionDirectedConservativeData
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ConstructionDirectedMonoid (UnitImage)
open ConstructionDirectedFactors
open ConstructionDirectedWeightData
open ConstructionRealCuts (Cut CutCarrier Subset UpperBound)
open ConstructionProbeCostSupremum (Cap CostMember)
open ConstructionProbeLetterIntervals (UniformMargins MissedBound)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {J E Domains F Muls Units C L projection B G unit w Q R top Heights Costs HL LC : M.Carrier .set}

def ExactMargins (hM : FirstOrder.Theory.Models M nativeZF) (w Q D mul H C : M.Carrier .set) : Prop :=
  ∀ x y hx hy, PureKuratowski.PairMember M x hx H → PureKuratowski.PairMember M y hy H →
    ConstructionBaseMonoid.Divides D mul x y → ¬ ConstructionBaseMonoid.Divides D mul y x →
    ∃ cap sum, Cut hM w Q cap ∧ Cap D mul C x y cap ∧
      ConstructionCutAddition.SumCut hM w Q hx cap sum ∧ ConstructionProbeIntervals.Strict sum hy ∧
      MissedBound D mul C x y cap

def OldSuprema (hM : FirstOrder.Theory.Models M nativeZF) (w Q D L mul G Ci LC f : M.Carrier .set) : Prop :=
  ∀ x y fx fy, PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
    ∃ f0 f1 cap, ConstructionProbeCostSupremum.Family D mul Ci x y f0 ∧
      ConstructionProbeCostSupremum.Family L G LC fx fy f1 ∧ Cut hM w Q cap ∧
      Cap D mul Ci x y cap ∧ Cap L G LC fx fy cap ∧
      ∀ c0 c1, Cap D mul Ci x y c0 → Cap L G LC fx fy c1 → c0 = c1

/-- Source cost_le_old_sup: every arbitrary new missed divisor is tested
at an actual common future; source hSup supplies the SAME old cap. -/
theorem missed_bound_limit (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    (hWC : WeightFamily J Domains R Costs) (hLC : MapsTo L R LC)
    (hCostGraph : ConstructionDirectedWeights.Graph J Domains Costs projection LC)
    (hSup : SupremumLaws J E Domains F Muls Costs)
    {i D mul Ci f x y fx fy cap : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (hCi : PureKuratowski.PairMember M i Ci Costs)
    (hf : MapsTo D L f)
    (hFG : ∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z)
    (hfx : PureKuratowski.PairMember M x fx f) (hfy : PureKuratowski.PairMember M y fy f)
    (hCap : Cap D mul Ci x y cap) : MissedBound L G LC fx fy cap := by
  intro d cd hd hdc hdy hdx
  obtain ⟨j,z,hz,hzd⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP hd
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hz.1
  have hxD := ForcingConditionGraphs.function_input hf.1 hfx
  have hyD := ForcingConditionGraphs.function_input hf.1 hfy
  obtain ⟨xx,hxx⟩ := hT.1 i k x ⟨hi,D,hD,hxD⟩ hk hik
  obtain ⟨Dk,mk,ek,hDk,hmk,hek,_⟩ := ConstructionDirectedMonoidData.family_at hFam hk
  obtain ⟨t,hFt,htx⟩ := hxx.2.2
  have hCov := hCons i k D Dk mul mk t hi hk hik hD hDk hm hmk hFt
  obtain ⟨yy,hyyD,hty,hyy⟩ := transition_value hCov.1 hi hk hD hDk hFt hyD
  have hxp := projected_transition hM hC hp hE hT hEq hik hxx ((hFG x fx).mp hfx).2
  have hyp := projected_transition hM hC hp hE hT hEq hik hyy ((hFG y fy).mp hfy).2
  obtain ⟨zz,hzz,_,hzp⟩ := ConstructionDirectedLimitCarrier.projected_later hM hC hp hE hT hEq hk hjk hzd
  have hzzD := ConstructionDirectedMonoidData.domain_mem hFam hDk hzz
  obtain ⟨gk,hgk,hGK,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hk hDk
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hk hDk hmk hek hgk hGK
  have hgx := (hGK xx fx).mpr ⟨hCov.1.1.2 x xx htx,hxp⟩
  have hgy := (hGK yy fy).mpr ⟨hyyD,hyp⟩
  have hgz := (hGK zz d).mpr ⟨hzzD,hzp⟩
  obtain ⟨Ck,hCk,_⟩ := hWC.1.2 k hk
  have hCz := (ConstructionDirectedWeights.projection_equation hWC hLC hCostGraph hk hDk hCk hzzD hzp).mp hdc
  have hCapK := hSup i k D Dk mul mk Ci Ck t hi hk hik hD hDk hm hmk hCi hCk hFt x y xx yy cap htx hty hCap
  obtain ⟨family,hFamily,hUpper,_⟩ := hCapK
  exact hUpper cd ((hFamily cd).mpr ⟨zz,hzzD,hCz,(hCore.2.2 zz yy d fy hgz hgy).mp hdy,
    fun h => hdx ((hCore.2.2 zz xx d fx hgz hgx).mpr h)⟩)

/-- Source old_cost_supremum: the old cap remains the ACTUAL least bound,
using old costs embedded unchanged and all later missed costs bounded above. -/
theorem cap_limit (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    (hWC : WeightFamily J Domains R Costs) (hLC : MapsTo L R LC)
    (hCostGraph : ConstructionDirectedWeights.Graph J Domains Costs projection LC)
    (hSup : SupremumLaws J E Domains F Muls Costs)
    {i D mul e Ci f x y fx fy cap : M.Carrier .set}
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units) (hCi : PureKuratowski.PairMember M i Ci Costs)
    (hf : MapsTo D L f)
    (hFG : ∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z)
    (hfx : PureKuratowski.PairMember M x fx f) (hfy : PureKuratowski.PairMember M y fy f)
    (hCap : Cap D mul Ci x y cap) : Cap L G LC fx fy cap := by
  have hMiss := missed_bound_limit hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hWC hLC hCostGraph hSup hi hD hm hCi hf hFG hfx hfy hCap
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he hf hFG
  obtain ⟨f1,hF1,_⟩ := ConstructionProbeCostSupremum.exists_family hM (mul := G) (x := fx) (y := fy) hLC
  refine ⟨f1,hF1,?_,?_⟩
  · intro cd hcd
    obtain ⟨d,hd,hdc,hdy,hdx⟩ := (hF1 cd).mp hcd
    exact hMiss d cd hd hdc hdy hdx
  · intro bound hBound
    obtain ⟨f0,hF0,_,hLeast⟩ := hCap
    apply hLeast bound
    intro cd hcd
    obtain ⟨d,hd,hdc,hdy,hdx⟩ := (hF0 cd).mp hcd
    obtain ⟨fd,hfd,_⟩ := hf.1.2 d hd
    have hCd := (ConstructionDirectedWeights.projection_equation hWC hLC hCostGraph hi hD hCi hd ((hFG d fd).mp hfd).2).mpr hdc
    exact hBound cd ((hF1 cd).mpr ⟨fd,hf.2 d fd hfd,hCd,(hCore.2.2 d y fd fy hfd hfy).mpr hdy,
      fun h => hdx ((hCore.2.2 d x fd fx hfd hfx).mp h)⟩)

/-- Construct both exact families and SAME unique cap for ALL old pairs.
The bounded-union interface already handles empty families; no extra cases. -/
theorem old_suprema (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    (hWC : WeightFamily J Domains R Costs) (hLC : MapsTo L R LC)
    (hCostGraph : ConstructionDirectedWeights.Graph J Domains Costs projection LC)
    (hSup : SupremumLaws J E Domains F Muls Costs)
    (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hBounds : CostBounds J Costs top)
    {i D mul e Ci f : M.Carrier .set} (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (he : PureKuratowski.PairMember M i e Units) (hCi : PureKuratowski.PairMember M i Ci Costs)
    (hf : MapsTo D L f)
    (hFG : ∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z) :
    OldSuprema hM w Q D L mul G Ci LC f := by
  intro x y fx fy hfx hfy
  obtain ⟨f0,hF0,hF0R⟩ := ConstructionProbeCostSupremum.exists_family hM (x := x) (y := y) (hWC.2 i D Ci hi hD hCi)
  have hUpper : UpperBound f0 top := by
    intro cd hcd
    obtain ⟨d,_,hdc,_,_⟩ := (hF0 cd).mp hcd
    exact (hBounds i Ci hi hCi d cd hdc).2
  obtain ⟨cap,hCapCut,hUpperCap,hLeast⟩ := ConstructionRealCuts.bounded_union hM hR hF0R hTop hUpper
  have hCap : Cap D mul Ci x y cap := ⟨f0,hF0,hUpperCap,hLeast⟩
  have hCapL := cap_limit hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hWC hLC hCostGraph hSup hi hD hm he hCi hf hFG hfx hfy hCap
  obtain ⟨f1,hF1,_⟩ := ConstructionProbeCostSupremum.exists_family hM (mul := G) (x := fx) (y := fy) hLC
  exact ⟨f0,f1,cap,hF0,hF1,hCapCut,hCap,hCapL,fun c0 c1 hc0 hc1 =>
    (ConstructionProbeCostSupremum.cap_unique hM hc0 hCap).trans (ConstructionProbeCostSupremum.cap_unique hM hCapL hc1)⟩

theorem exact_margins (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    (hWC : WeightFamily J Domains R Costs) (hLC : MapsTo L R LC)
    (hCostGraph : ConstructionDirectedWeights.Graph J Domains Costs projection LC)
    (hSup : SupremumLaws J E Domains F Muls Costs)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hWH : WeightFamily J Domains R Heights) (hHL : MapsTo L R HL)
    (hHeightGraph : ConstructionDirectedWeights.Graph J Domains Heights projection HL)
    (hUniform : UniformFamily hM w Q J Domains Muls Heights Costs) :
    ExactMargins hM w Q L G HL LC := by
  intro a b va vb ha hb hab hba
  have haL := ForcingConditionGraphs.function_input hHL.1 ha
  have hbL := ForcingConditionGraphs.function_input hHL.1 hb
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq haL hbL
  obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
  have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
  have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD hy
  obtain ⟨Hi,hHi,_⟩ := hWH.1.2 i hx.1
  obtain ⟨Ci,hCi,_⟩ := hWC.1.2 i hx.1
  have hxaH := (ConstructionDirectedWeights.projection_equation hWH hHL hHeightGraph hx.1 hD hHi hxD hxa).mp ha
  have hybH := (ConstructionDirectedWeights.projection_equation hWH hHL hHeightGraph hx.1 hD hHi hyD hyb).mp hb
  obtain ⟨f,hf,hFG,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hx.1 hD
  have hfx := (hFG x a).mpr ⟨hxD,hxa⟩
  have hfy := (hFG y b).mpr ⟨hyD,hyb⟩
  have hCore := stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hx.1 hD hm he hf hFG
  have hStrict1 := (hCore.2.2 x y a b hfx hfy).mp hab
  have hStrict2 := fun h => hba ((hCore.2.2 y x b a hfy hfx).mpr h)
  have hU := hUniform i D mul Hi Ci hx.1 hD hm hHi hCi x y _ _ hxaH hybH hStrict1 hStrict2
  obtain ⟨cap,sum,hCut,hCap,hSum,hStrict,_⟩ := ConstructionProbeCostSupremum.canonical_uniform hM hw hQ hR
    (hWC.2 i D Ci hx.1 hD hCi) ((hR _).mp (hHL.2 a _ ha)) hU
  exact ⟨cap,sum,hCut,
    cap_limit hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hWC hLC hCostGraph hSup hx.1 hD hm he hCi hf hFG hfx hfy hCap,
    hSum,hStrict,
    missed_bound_limit hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hWC hLC hCostGraph hSup hx.1 hD hm hCi hf hFG hfx hfy hCap⟩

/-- The complete real HeightCost contract and every old weighted stage map. -/
def Laws (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top J Domains Muls Heights Costs L projection G HL LC : M.Carrier .set) : Prop :=
  MapsTo L R HL ∧ ConstructionDirectedWeights.Graph J Domains Heights projection HL ∧
    MapsTo L R LC ∧ ConstructionDirectedWeights.Graph J Domains Costs projection LC ∧
    ConstructionCutWeights.RangeBound top HL ∧ ConstructionProbeGateCap.Bounds top LC ∧
    UniformMargins hM w Q L G HL LC ∧ ExactMargins hM w Q L G HL LC ∧
    ∀ i D mul Hi Ci f, (Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
      PureKuratowski.PairMember M i Hi Heights → PureKuratowski.PairMember M i Ci Costs →
      MapsTo D L f →
      (∀ v z, PureKuratowski.PairMember M v z f ↔ (Project.FirstOrderSemantics.reduct M).mem v D ∧ Product projection i v z) →
      (∀ x fx r, PureKuratowski.PairMember M x fx f →
        (PureKuratowski.PairMember M fx r HL ↔ PureKuratowski.PairMember M x r Hi)) ∧
      (∀ x fx r, PureKuratowski.PairMember M x fx f →
        (PureKuratowski.PairMember M fx r LC ↔ PureKuratowski.PairMember M x r Ci)) ∧
      OldSuprema hM w Q D L mul G Ci LC f

theorem exists_weights (hM : FirstOrder.Theory.Models M nativeZF)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G) (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : UnitImage J Domains Units projection unit)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hWH : WeightFamily J Domains R Heights) (hWC : WeightFamily J Domains R Costs)
    (hStableH : Stable J E Domains F Heights) (hStableC : Stable J E Domains F Costs)
    (hHB : HeightBounds J Heights top) (hCB : CostBounds J Costs top)
    (hUniform : UniformFamily hM w Q J Domains Muls Heights Costs)
    (hSup : SupremumLaws J E Domains F Muls Costs) :
    ∃ HL LC, Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC := by
  obtain ⟨HL,hHL,hHG⟩ := ConstructionDirectedWeights.exists_graph hM hWH hStableH hC hL hP hEq
  obtain ⟨LC,hLC,hCG⟩ := ConstructionDirectedWeights.exists_graph hM hWC hStableC hC hL hP hEq
  have hExact := exact_margins hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hWC hLC hCG hSup hw hQ hR hWH hHL hHG hUniform
  have hU : UniformMargins hM w Q L G HL LC := by
    intro x y hx hy hxh hyh hxy hyx
    obtain ⟨cap,sum,hCut,_,hSum,hStrict,hMiss⟩ := hExact x y hx hy hxh hyh hxy hyx
    exact ⟨cap,sum,hCut,hSum,hStrict,hMiss⟩
  refine ⟨HL,LC,hHL,hHG,hLC,hCG,ConstructionDirectedWeights.height_bounds hHB hHG,
    ConstructionDirectedWeights.cost_bounds hCB hCG,hU,hExact,?_⟩
  intro i D mul Hi Ci f hi hD hm hHi hCi hf hFG
  obtain ⟨_,_,e,_,_,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hi
  refine ⟨?_,?_,old_suprema hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hWC hLC hCG hSup hR hTop hCB hi hD hm he hCi hf hFG⟩
  · intro x fx r hfx
    exact ConstructionDirectedWeights.projection_equation hWH hHL hHG hi hD hHi ((hFG x fx).mp hfx).1 ((hFG x fx).mp hfx).2
  · intro x fx r hfx
    exact ConstructionDirectedWeights.projection_equation hWC hLC hCG hi hD hCi ((hFG x fx).mp hfx).1 ((hFG x fx).mp hfx).2

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units w Q R top Heights Costs : M.Carrier .set)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hFam : Family J Domains Muls Units) (hHom : HomLaws J E Domains F Muls Units)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hWH : WeightFamily J Domains R Heights) (hWC : WeightFamily J Domains R Costs)
    (hStableH : Stable J E Domains F Heights) (hStableC : Stable J E Domains F Costs)
    (hHB : HeightBounds J Heights top) (hCB : CostBounds J Costs top)
    (hUniform : UniformFamily hM w Q J Domains Muls Heights Costs)
    (hSup : SupremumLaws J E Domains F Muls Costs) :
    ∃ C L projection B G unit, Representatives J Domains C ∧ MapsTo C L projection ∧ Carrier J E Domains F C L ∧
      Projection J E Domains F C projection ∧ EqualityLaw J E Domains F projection ∧
      ConstructionProbeLetters.Representatives L L B ∧ MapsTo B L G ∧ ConstructionDirectedProduct.Graph J Domains Muls projection G ∧
      (Project.FirstOrderSemantics.reduct M).mem unit L ∧ UnitImage J Domains Units projection unit ∧
      LeftCancelMonoid L G unit ∧ (ConicalFamily J Domains Muls Units → Conical L G unit) ∧
      (JoinsFamily J Domains Muls Units → ConstructionProbeSharedIntersections.ConditionalJoins L G) ∧
      (∀ i D mul e, (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains →
        PureKuratowski.PairMember M i mul Muls → PureKuratowski.PairMember M i e Units →
        ∃ f, MapsTo D L f ∧ (∀ x z, PureKuratowski.PairMember M x z f ↔
          (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) ∧
          ConstructionProbeLiftHom.PreservesProducts mul G f ∧ PureKuratowski.PairMember M e unit f ∧
          ConstructionProbeConservative.Conservative D L mul G f ∧ ConstructionDirectedProfiles.ProfileTransport J E Domains F Muls i D L G f) ∧
      ∃ HL LC, Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC := by
  obtain ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hCon,hJoins,hStages⟩ :=
    ConstructionDirectedProfiles.exists_system hM J E Domains F Muls Units hne hE hT hFam hHom hCons
  obtain ⟨HL,LC,hWeights⟩ := exists_weights hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup
  exact ⟨C,L,projection,B,G,unit,hC,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hCon,hJoins,hStages,HL,LC,hWeights⟩


def exactMargins {m : Nat} (w Q D mul H C : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ (3
  : Fin (m+4)) (2 : Fin (m+4)))) (.imp (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ mul.succ.succ.succ.succ (2 : Fin (m+4)) (3 : Fin (m+4))))) (.existsE (.existsE
  (.conj (ConstructionRealCuts.cut w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+6))) (.conj (ConstructionProbeCostSupremum.cap D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ (3 : Fin (m+4)).succ.succ (2 : Fin
  (m+4)).succ.succ (1 : Fin (m+6))) (.conj (ConstructionCutAddition.sumCut w.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ.succ (1 : Fin (m+6)) (0 : Fin (m+6))) (.conj (.conj
  (Project.Formula.subset (.bound (0 : Fin (m+6))) (.bound (0 : Fin (m+4)).succ.succ)) (.neg
  (Project.Formula.subset (.bound (0 : Fin (m+4)).succ.succ) (.bound (0 : Fin (m+6))))))
  (ConstructionProbeIntervalsSyntax.missedBound D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ (3 : Fin (m+4)).succ.succ (2 : Fin
  (m+4)).succ.succ (1 : Fin (m+6)))))))))))))))))

theorem exactMargins_freeClosed {m : Nat} (w Q D mul H C : Fin m) :
    (exactMargins w Q D mul H C).FreeClosed := by
  simp -implicitDefEqProofs [exactMargins,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionProbeCostSupremum.cap_freeClosed,ConstructionCutAddition.sumCut_freeClosed,ConstructionProbeIntervalsSyntax.missedBound_freeClosed]

theorem exactMargins_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D mul H C : Fin m) :
    Project.Formula.satisfies env (exactMargins w Q D mul H C) ↔ ExactMargins hM (env.bound w) (env.bound Q) (env.bound D) (env.bound mul) (env.bound H) (env.bound C) := by
  simp only [exactMargins,ExactMargins,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRealCuts.cut_semantics hM,ConstructionProbeCostSupremum.cap_semantics hM,ConstructionCutAddition.sumCut_semantics hM,ConstructionProbeIntervalsSyntax.missedBound_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M),Project.Formula.satisfies_subset_iff]
  rfl


def oldSuprema {m : Nat} (w Q D L mul G Ci LC f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin (m+4)))) (.existsE (.existsE
  (.existsE (.conj (ConstructionProbeCostSupremum.family D.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ Ci.succ.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+4)).succ.succ.succ (2 : Fin (m+4)).succ.succ.succ (2 : Fin (m+7))) (.conj
  (ConstructionProbeCostSupremum.family L.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ LC.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ.succ.succ
  (0 : Fin (m+4)).succ.succ.succ (1 : Fin (m+7))) (.conj (ConstructionRealCuts.cut
  w.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+7))) (.conj
  (ConstructionProbeCostSupremum.cap D.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ Ci.succ.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+4)).succ.succ.succ (2 : Fin (m+4)).succ.succ.succ (0 : Fin (m+7))) (.conj
  (ConstructionProbeCostSupremum.cap L.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ LC.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ.succ.succ
  (0 : Fin (m+4)).succ.succ.succ (0 : Fin (m+7))) (.forallE (.forallE (.imp
  (ConstructionProbeCostSupremum.cap D.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ Ci.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+4)).succ.succ.succ.succ.succ (2 : Fin (m+4)).succ.succ.succ.succ.succ (1 : Fin (m+9))) (.imp
  (ConstructionProbeCostSupremum.cap L.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ LC.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+4)).succ.succ.succ.succ.succ (0 : Fin (m+4)).succ.succ.succ.succ.succ (0 : Fin (m+9)))
  (Project.Formula.extensionalEq (.bound (1 : Fin (m+9))) (.bound (0 : Fin (m+9))))))))))))))))))))))

theorem oldSuprema_freeClosed {m : Nat} (w Q D L mul G Ci LC f : Fin m) :
    (oldSuprema w Q D L mul G Ci LC f).FreeClosed := by
  simp -implicitDefEqProofs [oldSuprema,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionProbeCostSupremum.family_freeClosed,ConstructionProbeCostSupremum.cap_freeClosed,Project.Formula.extensionalEq]

theorem oldSuprema_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D L mul G Ci LC f : Fin m) :
    Project.Formula.satisfies env (oldSuprema w Q D L mul G Ci LC f) ↔ OldSuprema hM (env.bound w) (env.bound Q) (env.bound D) (env.bound L) (env.bound mul) (env.bound G) (env.bound Ci) (env.bound LC) (env.bound f) := by
  simp only [oldSuprema,OldSuprema,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRealCuts.cut_semantics hM,ConstructionProbeCostSupremum.family_semantics hM,ConstructionProbeCostSupremum.cap_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def laws {m : Nat} (w Q R top J Domains Muls Heights Costs L projection G HL LC : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo HL L R)) (.conj
  (ConstructionDirectedWeights.graph J Domains Heights projection HL) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo LC L R)) (.conj (ConstructionDirectedWeights.graph J Domains Costs projection
  LC) (.conj (ConstructionCutWeights.rangeBound top HL) (.conj (ConstructionProbeGateCap.bounds top LC)
  (.conj (ConstructionProbeIntervalsSyntax.uniformMargins w Q L G HL LC) (.conj (exactMargins w Q L G HL LC)
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (5 : Fin (m+6))) (.bound
  J.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Heights.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2
  : Fin (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Costs.succ.succ.succ.succ.succ.succ
  (5 : Fin (m+6)) (1 : Fin (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin
  (m+6)) (4 : Fin (m+6)) L.succ.succ.succ.succ.succ.succ)) (.imp (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+6)).succ.succ (1 : Fin (m+8)) (0 : Fin
  (m+8)))) (.conj (.mem (.bound (1 : Fin (m+8))) (.bound (4 : Fin (m+6)).succ.succ)) (ProjectSyntax.encode
  id (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
  (m+6)).succ.succ (1 : Fin (m+8)) (0 : Fin (m+8)))))))) (.conj (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+6)).succ.succ.succ (2 : Fin (m+9)) (1 : Fin
  (m+9)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
  HL.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+9)) (0 : Fin (m+9)))) (ProjectSyntax.encode id
  (Source.SetLanguage.edge (2 : Fin (m+6)).succ.succ.succ (2 : Fin (m+9)) (0 : Fin (m+9))))))))) (.conj
  (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
  (m+6)).succ.succ.succ (2 : Fin (m+9)) (1 : Fin (m+9)))) (.iff (ProjectSyntax.encode id
  (Source.SetLanguage.edge LC.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+9)) (0 : Fin (m+9))))
  (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin (m+6)).succ.succ.succ (2 : Fin (m+9)) (0 : Fin
  (m+9))))))))) (oldSuprema w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ (4 : Fin (m+6))
  L.succ.succ.succ.succ.succ.succ (3 : Fin (m+6)) G.succ.succ.succ.succ.succ.succ (1 : Fin (m+6))
  LC.succ.succ.succ.succ.succ.succ (0 : Fin (m+6))))))))))))))))))))))))))

theorem laws_freeClosed {m : Nat} (w Q R top J Domains Muls Heights Costs L projection G HL LC : Fin m) :
    (laws w Q R top J Domains Muls Heights Costs L projection G HL LC).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeights.graph_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,exactMargins_freeClosed,oldSuprema_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top J Domains Muls Heights Costs L projection G HL LC : Fin m) :
    Project.Formula.satisfies env (laws w Q R top J Domains Muls Heights Costs L projection G HL LC) ↔ Laws hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Heights) (env.bound Costs) (env.bound L) (env.bound projection) (env.bound G) (env.bound HL) (env.bound LC) := by
  simp only [laws,Laws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ConstructionDirectedWeights.graph_semantics hM,ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,exactMargins_semantics hM,oldSuprema_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedHeightCost
