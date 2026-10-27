/- Pinned MonoidTowers.DirectedColimit.liftFun/liftMonoidHom/lift_conservative/
lift/isColimit:96-168. Reuse the SAME actual quotient and the accepted
arbitrary-target descent constructor; no choice of representatives. -/
import PPAC.Migration.ConstructionDirectedObject

namespace PPAC.Migration.ConstructionDirectedLift
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family)
open ConstructionDirectedConservativeData (ConservativeTransitions)
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeCostSupremum (Cap)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Evaluation form of cocone factorization, for every internal stage/input/output. -/
def Fac (J Domains K projection lift : M.Carrier .set) : Prop :=
  ∀ i D ki x a y, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i ki K →
    (Project.FirstOrderSemantics.reduct M).mem x D → Product projection i x a →
    (PureKuratowski.PairMember M a y lift ↔ PureKuratowski.PairMember M x y ki)

/-- Original cocone leg Hom fields; MapsTo and naturality are the existing
WeightFamily/Stable predicates, whose target may be any internal set. -/
def Legs (J Domains Muls Units K N GN uN : M.Carrier .set) : Prop :=
  ∀ i D mul e ki, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
    PureKuratowski.PairMember M i e Units → PureKuratowski.PairMember M i ki K →
    PreservesProducts mul GN ki ∧ PureKuratowski.PairMember M e uN ki ∧ Conservative D N mul GN ki

def WeightedLegs (J Domains Muls Heights Costs K HN CN N GN : M.Carrier .set) : Prop :=
  ∀ i D mul Hi Ci ki, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
    PureKuratowski.PairMember M i Hi Heights → PureKuratowski.PairMember M i Ci Costs →
    PureKuratowski.PairMember M i ki K →
    (∀ x fx r, PureKuratowski.PairMember M x fx ki →
      (PureKuratowski.PairMember M x r Hi ↔ PureKuratowski.PairMember M fx r HN)) ∧
    (∀ x fx r, PureKuratowski.PairMember M x fx ki →
      (PureKuratowski.PairMember M x r Ci ↔ PureKuratowski.PairMember M fx r CN)) ∧
    ∀ x y fx fy cap, PureKuratowski.PairMember M x fx ki → PureKuratowski.PairMember M y fy ki →
      Cap D mul Ci x y cap → Cap N GN CN fx fy cap

def MarkLegs (J Marks K mN : M.Carrier .set) : Prop :=
  ∀ i a ki, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i a Marks → PureKuratowski.PairMember M i ki K →
    PureKuratowski.PairMember M a mN ki

theorem factorization {J Domains K N L projection lift : M.Carrier .set}
    (hK : WeightFamily J Domains N K) (hf : MapsTo L N lift)
    (hGraph : ConstructionDirectedWeights.Graph J Domains K projection lift) :
    Fac J Domains K projection lift := by
  intro i D ki x a y hi hD hki hx hpx
  exact ConstructionDirectedWeights.projection_equation hK hf hGraph hi hD hki hx hpx

/-- Equality of the actual internal graphs, using the native relation-extensionality theorem. -/
theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F K N C L projection lift other : M.Carrier .set}
    (hC : Representatives J Domains C) (hL : Carrier J E Domains F C L)
    (hP : Projection J E Domains F C projection)
    (hK : WeightFamily J Domains N K) (hf : MapsTo L N lift) (hg : MapsTo L N other)
    (hFac : Fac J Domains K projection lift) (hOther : Fac J Domains K projection other) : other = lift := by
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM L N other).mp hg).1.1
    ((ForcingSupportSize.native_mapsTo hM L N lift).mp hf).1.1
  intro a y
  constructor
  · intro hay
    obtain ⟨i,x,hx,hpx⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP (function_input hg.1 hay)
    obtain ⟨D,hD,hxD⟩ := hx.2
    obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
    exact (hFac i D ki x a y hx.1 hD hki hxD hpx).mpr ((hOther i D ki x a y hx.1 hD hki hxD hpx).mp hay)
  · intro hay
    obtain ⟨i,x,hx,hpx⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP (function_input hf.1 hay)
    obtain ⟨D,hD,hxD⟩ := hx.2
    obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
    exact (hOther i D ki x a y hx.1 hD hki hxD hpx).mpr ((hFac i D ki x a y hx.1 hD hki hxD hpx).mp hay)

theorem products {J Domains Muls Units K N GN uN projection G lift : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hK : WeightFamily J Domains N K)
    (hLegs : Legs J Domains Muls Units K N GN uN)
    (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hFac : Fac J Domains K projection lift) : PreservesProducts G GN lift := by
  intro a b c fa fb fc hab hfa hfb hfc
  obtain ⟨i,x,y,z,hxyz,hxa,hyb,hzc⟩ := (hGraph a b c).mp hab
  obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hxyz.1.1
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hxyz.1.1
  obtain ⟨hx,hy,hz,hprod⟩ := ConstructionDirectedMonoidData.product_data hFam hD hm hxyz
  exact (hLegs i D mul e ki hxyz.1.1 hD hm he hki).1 x y z fa fb fc hprod
    ((hFac i D ki x a fa hxyz.1.1 hD hki hx hxa).mp hfa)
    ((hFac i D ki y b fb hxyz.1.1 hD hki hy hyb).mp hfb)
    ((hFac i D ki z c fc hxyz.1.1 hD hki hz hzc).mp hfc)

theorem unit {J Domains Muls Units K N GN uN projection unit lift : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : Family J Domains Muls Units) (hK : WeightFamily J Domains N K)
    (hLegs : Legs J Domains Muls Units K N GN uN)
    (hImage : ConstructionDirectedMonoid.UnitImage J Domains Units projection unit)
    (hFac : Fac J Domains K projection lift) : PureKuratowski.PairMember M unit uN lift := by
  obtain ⟨i,hi⟩ := hne
  obtain ⟨D,mul,e,hD,hm,he,hMon⟩ := ConstructionDirectedMonoidData.family_at hFam hi
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hi
  exact (hFac i D ki e unit uN hi hD hki hMon.1.1 (hImage i e ⟨⟨hi,D,hD,hMon.1.1⟩,he⟩)).mpr
    (hLegs i D mul e ki hi hD hm he hki).2.1

/-- The specified arbitrary target factor, not just existential divisibility. -/
theorem factors (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units K N GN uN C L projection lift : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hK : WeightFamily J Domains N K)
    (hLegs : Legs J Domains Muls Units K N GN uN) (hf : MapsTo L N lift)
    (hFac : Fac J Domains K projection lift) : ConstructionProbeAlphabetMap.FactorConservation N GN lift := by
  intro a b z fa fb hfa hfb hz hprod
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq
    (function_input hf.1 hfa) (function_input hf.1 hfb)
  obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
  have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
  have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD hy
  obtain ⟨t,ht⟩ := (hLegs i D mul e ki hx.1 hD hm he hki).2.2.2.1 x y z fa fb
    ((hFac i D ki x a fa hx.1 hD hki hxD hxa).mp hfa)
    ((hFac i D ki y b fb hx.1 hD hki hyD hyb).mp hfb) hz hprod
  have htD := function_input (hK.2 i D ki hx.1 hD hki).1 ht
  obtain ⟨c,_,htc⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp ⟨hx.1,D,hD,htD⟩
  exact ⟨c,(hFac i D ki t c z hx.1 hD hki htD htc).mpr ht⟩

theorem injective (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units K N GN uN C L projection lift : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hK : WeightFamily J Domains N K)
    (hLegs : Legs J Domains Muls Units K N GN uN) (hf : MapsTo L N lift)
    (hFac : Fac J Domains K projection lift) : Injection L N lift := by
  refine ⟨hf,?_⟩
  intro a b z haz hbz
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq
    (function_input hf.1 haz) (function_input hf.1 hbz)
  obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
  have heq := (hLegs i D mul e ki hx.1 hD hm he hki).2.2.1.2 x y z
    ((hFac i D ki x a z hx.1 hD hki (ConstructionDirectedMonoidData.domain_mem hFam hD hx) hxa).mp haz)
    ((hFac i D ki y b z hx.1 hD hki (ConstructionDirectedMonoidData.domain_mem hFam hD hy) hyb).mp hbz)
  subst y
  exact ConstructionProbeHomEvaluation.product_unique hM hp hxa hyb

theorem conservative (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units K N GN uN C L projection B G unit lift : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G)
    (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : ConstructionDirectedMonoid.UnitImage J Domains Units projection unit)
    (hK : WeightFamily J Domains N K) (hLegs : Legs J Domains Muls Units K N GN uN)
    (hf : MapsTo L N lift) (hFac : Fac J Domains K projection lift) : Conservative L N G GN lift := by
  refine ⟨injective hM hFam hE hT hC hp hL hP hEq hK hLegs hf hFac,
    factors hM hFam hE hT hC hp hL hP hEq hK hLegs hf hFac,?_,?_⟩
  · intro a b c fa fb fc hfa hfb hfc hJoin
    obtain ⟨i,x,y,z,hx,hy,hz,hxa,hyb,hzc⟩ := ConstructionDirectedLimitCarrier.common_stage_three hM hC hp hE hT hL hP hEq
      (function_input hf.1 hfa) (function_input hf.1 hfb) (function_input hf.1 hfc)
    obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
    obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
    obtain ⟨f,hf0,hFG,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hx.1 hD
    have hd := (ConstructionDirectedFactors.stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hx.1 hD hm he hf0 hFG).2.2
    have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
    have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD hy
    have hzD := ConstructionDirectedMonoidData.domain_mem hFam hD hz
    have hfx := (hFG x a).mpr ⟨hxD,hxa⟩
    have hfy := (hFG y b).mpr ⟨hyD,hyb⟩
    have hfz := (hFG z c).mpr ⟨hzD,hzc⟩
    have hj : ConstructionProbeCones.JoinProperty D mul x y z := by
      intro t ht
      obtain ⟨v,hv,htv⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp ⟨hx.1,D,hD,ht⟩
      have hft := (hFG t v).mpr ⟨ht,htv⟩
      exact (and_congr (hd x t a v hfx hft).symm (hd y t b v hfy hft).symm).trans
        ((hJoin v hv).trans (hd z t c v hfz hft))
    exact (hLegs i D mul e ki hx.1 hD hm he hki).2.2.2.2.1 x y z fa fb fc
      ((hFac i D ki x a fa hx.1 hD hki hxD hxa).mp hfa)
      ((hFac i D ki y b fb hx.1 hD hki hyD hyb).mp hfb)
      ((hFac i D ki z c fc hx.1 hD hki hzD hzc).mp hfc) hj
  · intro a b fa fb hfa hfb hCommon
    obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq
      (function_input hf.1 hfa) (function_input hf.1 hfb)
    obtain ⟨D,mul,e,hD,hm,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
    obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
    have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
    have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD hy
    obtain ⟨t,ht,hxt,hyt⟩ := (hLegs i D mul e ki hx.1 hD hm he hki).2.2.2.2.2 x y fa fb
      ((hFac i D ki x a fa hx.1 hD hki hxD hxa).mp hfa)
      ((hFac i D ki y b fb hx.1 hD hki hyD hyb).mp hfb) hCommon
    obtain ⟨v,hv,htv⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp ⟨hx.1,D,hD,ht⟩
    obtain ⟨f,hf0,hFG,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hx.1 hD
    have hd := (ConstructionDirectedFactors.stage_core hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hx.1 hD hm he hf0 hFG).2.2
    have hft := (hFG t v).mpr ⟨ht,htv⟩
    exact ⟨v,hv,(hd x t a v ((hFG x a).mpr ⟨hxD,hxa⟩) hft).mpr hxt,
      (hd y t b v ((hFG y b).mpr ⟨hyD,hyb⟩) hft).mpr hyt⟩

theorem mark {J Domains Units Marks K N projection mark mN lift : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hDomains : ForcingConditionGraphs.FunctionOn J Domains)
    (hUnits : ForcingConditionGraphs.FunctionOn J Units)
    (hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks)
    (hK : WeightFamily J Domains N K) (hLegs : MarkLegs J Marks K mN)
    (hImage : ConstructionDirectedMarks.MarkImage J Marks projection mark)
    (hFac : Fac J Domains K projection lift) : PureKuratowski.PairMember M mark mN lift := by
  obtain ⟨i,hi⟩ := hne
  obtain ⟨D,hD,_⟩ := hDomains.2 i hi
  obtain ⟨e,he,_⟩ := hUnits.2 i hi
  obtain ⟨a,ha,_⟩ := hMarks.1.2 i hi
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hi
  exact (hFac i D ki a mark mN hi hD hki (hMarks.2 i D e a hi hD he ha).1
    (hImage i a hi ha)).mpr (hLegs i a ki hi ha hki)

/-- Transport both actual graphs and the same least upper bound, following
source lift.supremum through the already accepted old-supremum equations. -/
theorem weights (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top J E Domains F Muls Units Heights Costs K N GN C L projection HL LC HN CN G lift : M.Carrier .set}
    (hFam : Family J Domains Muls Units)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hWH : WeightFamily J Domains R Heights) (hWC : WeightFamily J Domains R Costs)
    (hWeights : ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC)
    (hK : WeightFamily J Domains N K) (hLegs : WeightedLegs J Domains Muls Heights Costs K HN CN N GN)
    (hf : MapsTo L N lift) (hFac : Fac J Domains K projection lift) :
    (∀ a fa r, PureKuratowski.PairMember M a fa lift →
      (PureKuratowski.PairMember M a r HL ↔ PureKuratowski.PairMember M fa r HN)) ∧
    (∀ a fa r, PureKuratowski.PairMember M a fa lift →
      (PureKuratowski.PairMember M a r LC ↔ PureKuratowski.PairMember M fa r CN)) ∧
    ∀ a b fa fb cap, PureKuratowski.PairMember M a fa lift → PureKuratowski.PairMember M b fb lift →
      Cap L G LC a b cap → Cap N GN CN fa fb cap := by
  obtain ⟨hHL,hHG,hLC,hCG,_,_,_,_,hOld⟩ := hWeights
  have hPoint : ∀ a fa r, PureKuratowski.PairMember M a fa lift →
      (PureKuratowski.PairMember M a r HL ↔ PureKuratowski.PairMember M fa r HN) ∧
      (PureKuratowski.PairMember M a r LC ↔ PureKuratowski.PairMember M fa r CN) := by
    intro a fa r haf
    obtain ⟨i,x,hx,hpx⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP (function_input hf.1 haf)
    obtain ⟨D,mul,e,hD,hm,_,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
    obtain ⟨Hi,hHi,_⟩ := hWH.1.2 i hx.1
    obtain ⟨Ci,hCi,_⟩ := hWC.1.2 i hx.1
    obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
    have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
    have hkx := (hFac i D ki x a fa hx.1 hD hki hxD hpx).mp haf
    have hWL := hLegs i D mul Hi Ci ki hx.1 hD hm hHi hCi hki
    exact ⟨(ConstructionDirectedWeights.projection_equation hWH hHL hHG hx.1 hD hHi hxD hpx).trans (hWL.1 x fa r hkx),
      (ConstructionDirectedWeights.projection_equation hWC hLC hCG hx.1 hD hCi hxD hpx).trans (hWL.2.1 x fa r hkx)⟩
  refine ⟨fun a fa r haf => (hPoint a fa r haf).1,fun a fa r haf => (hPoint a fa r haf).2,?_⟩
  intro a b fa fb cap haf hbf hCap
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq
    (function_input hf.1 haf) (function_input hf.1 hbf)
  obtain ⟨D,mul,e,hD,hm,_,_⟩ := ConstructionDirectedMonoidData.family_at hFam hx.1
  obtain ⟨Hi,hHi,_⟩ := hWH.1.2 i hx.1
  obtain ⟨Ci,hCi,_⟩ := hWC.1.2 i hx.1
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hx.1
  obtain ⟨f,hf0,hFG,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hx.1 hD
  have hxD := ConstructionDirectedMonoidData.domain_mem hFam hD hx
  have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD hy
  obtain ⟨_,_,cap0,_,_,_,hCap0,hCapL,_⟩ := (hOld i D mul Hi Ci f hx.1 hD hm hHi hCi hf0 hFG).2.2 x y a b
    ((hFG x a).mpr ⟨hxD,hxa⟩) ((hFG y b).mpr ⟨hyD,hyb⟩)
  have hcc := ConstructionProbeCostSupremum.cap_unique hM hCapL hCap
  subst cap
  exact (hLegs i D mul Hi Ci ki hx.1 hD hm hHi hCi hki).2.2 x y fa fb cap0
    ((hFac i D ki x a fa hx.1 hD hki hxD hxa).mp haf)
    ((hFac i D ki y b fb hx.1 hD hki hyD hyb).mp hbf) hCap0

/-- Full source Hom and IsColimit.fac/uniq on the same actual graph. -/
def LiftLaws (J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift : M.Carrier .set) : Prop :=
  MapsTo L N lift ∧ ConstructionDirectedWeights.Graph J Domains K projection lift ∧
    Fac J Domains K projection lift ∧ PreservesProducts G GN lift ∧
    PureKuratowski.PairMember M unit uN lift ∧ Conservative L N G GN lift ∧
    PureKuratowski.PairMember M mark mN lift ∧
    (∀ a fa r, PureKuratowski.PairMember M a fa lift →
      (PureKuratowski.PairMember M a r HL ↔ PureKuratowski.PairMember M fa r HN)) ∧
    (∀ a fa r, PureKuratowski.PairMember M a fa lift →
      (PureKuratowski.PairMember M a r LC ↔ PureKuratowski.PairMember M fa r CN)) ∧
    (∀ a b fa fb cap, PureKuratowski.PairMember M a fa lift → PureKuratowski.PairMember M b fb lift →
      Cap L G LC a b cap → Cap N GN CN fa fb cap) ∧
    ∀ other, MapsTo L N other → Fac J Domains K projection other → other = lift

theorem exists_lift (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top J E Domains F Muls Units Heights Costs Marks K N GN uN mN C L projection B G unit mark HL LC HN CN : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G)
    (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : ConstructionDirectedMonoid.UnitImage J Domains Units projection unit)
    (hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks)
    (hMarkImage : ConstructionDirectedMarks.MarkImage J Marks projection mark)
    (hWH : WeightFamily J Domains R Heights) (hWC : WeightFamily J Domains R Costs)
    (hWeights : ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC)
    (hK : WeightFamily J Domains N K) (hStable : Stable J E Domains F K)
    (hLegs : Legs J Domains Muls Units K N GN uN)
    (hWeighted : WeightedLegs J Domains Muls Heights Costs K HN CN N GN)
    (hMarkLegs : MarkLegs J Marks K mN) :
    ∃ lift, LiftLaws J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift := by
  obtain ⟨lift,hf,hFG⟩ := ConstructionDirectedWeights.exists_graph hM hK hStable hC hL hP hEq
  have hFac := factorization hK hf hFG
  obtain ⟨hHeight,hCost,hCap⟩ := weights hM hFam hC hp hL hP hEq hE hT hWH hWC hWeights hK hWeighted hf hFac
  exact ⟨lift,hf,hFG,hFac,products hFam hK hLegs hGraph hFac,ConstructionDirectedLift.unit hne hFam hK hLegs hImage hFac,
    conservative hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hK hLegs hf hFac,
    ConstructionDirectedLift.mark hne hFam.1 hFam.2.2.1 hMarks hK hMarkLegs hMarkImage hFac,
    hHeight,hCost,hCap,fun _ hg hOther => unique hM hC hL hP hK hf hg hFac hOther⟩

def Universal (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : M.Carrier .set) : Prop :=
  ∀ K N GN uN mN HN CN, WeightFamily J Domains N K → Stable J E Domains F K →
    Legs J Domains Muls Units K N GN uN → WeightedLegs J Domains Muls Heights Costs K HN CN N GN →
    MarkLegs J Marks K mN → ∃ lift, LiftLaws J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift

theorem universal (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top J E Domains F Muls Units Heights Costs Marks C L projection B G unit mark HL LC : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G)
    (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : LeftCancelMonoid L G unit) (hImage : ConstructionDirectedMonoid.UnitImage J Domains Units projection unit)
    (hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks)
    (hMarkImage : ConstructionDirectedMarks.MarkImage J Marks projection mark)
    (hWH : WeightFamily J Domains R Heights) (hWC : WeightFamily J Domains R Costs)
    (hWeights : ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC)
    : Universal J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC := by
  intro K N GN uN mN HN CN hK hStable hLegs hWeighted hMarkLegs
  exact exists_lift hM hne hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hMarks hMarkImage hWH hWC hWeights hK hStable hLegs hWeighted hMarkLegs

end PPAC.Migration.ConstructionDirectedLift
