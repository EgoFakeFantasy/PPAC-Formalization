/- Pinned MonoidRounds Under M limits/fromBase_naturality and
DirectedColimit.profile. Consume the ALREADY COMPLETE weighted colimit;
construct its actual fromBase map and ALL commuting triangles. No new
colimit/choice/recursion backend or restricted rank/model is introduced. -/
import PPAC.Migration.ConstructionDirectedColimitSyntax
import PPAC.Migration.ConstructionTowerSuccessor

namespace PPAC.Migration.ConstructionTowerLimit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingDiagramOrder (Product)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionRoundFields
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family HomLaws ConicalFamily)
open ConstructionDirectedConservativeData (ConservativeTransitions JoinsFamily)
open ConstructionDirectedWeightData (WeightFamily Stable HeightBounds CostBounds UniformFamily SupremumLaws)
open ConstructionRealCuts (CutCarrier Cut)
open ConstructionTowerSuccessor (FullLegs ProfileLegs BaseNatural)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def OriginLegs (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C : M.Carrier .set) : Prop :=
  FunctionOn J Origins ∧ ∀ i N mulN eN markN HN CN fi,
    (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i N Domains → PureKuratowski.PairMember M i mulN Muls →
    PureKuratowski.PairMember M i eN Units → PureKuratowski.PairMember M i markN Marks →
    PureKuratowski.PairMember M i HN Heights → PureKuratowski.PairMember M i CN Costs →
    PureKuratowski.PairMember M i fi Origins →
    MapFields hM w Q D N mul mulN e eN mark markN H C HN CN fi

def OriginProfiles (w J Domains Muls Origins D mul : M.Carrier .set) : Prop :=
  ∀ i N mulN fi, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i N Domains → PureKuratowski.PairMember M i mulN Muls →
    PureKuratowski.PairMember M i fi Origins → Profiles w D N mul mulN fi

def OriginNatural (J E F Origins : M.Carrier .set) : Prop :=
  ∀ i j fi fj t, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → PureKuratowski.PairMember M i j E →
    PureKuratowski.PairMember M i fi Origins → PureKuratowski.PairMember M j fj Origins →
    Product F i j t → NodeMap fi t fj

def ProfileTransitions (w J E Domains F Muls : M.Carrier .set) : Prop :=
  ∀ i j D N mul mulN t, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → PureKuratowski.PairMember M i j E →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M j N Domains →
    PureKuratowski.PairMember M i mul Muls → PureKuratowski.PairMember M j mulN Muls →
    Product F i j t → Profiles w D N mul mulN t

/-- Typed transition persistence discharges the ACTUAL source hP.
The MapsTo guard on supplied mapped graphs is essential here. -/
theorem persistent_of_transitions (hM : FirstOrder.Theory.Models M nativeZF)
    {w J E Domains F Muls i D mul a b d p node : M.Carrier .set}
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hProfiles : ProfileTransitions w J E Domains F Muls)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hm : PureKuratowski.PairMember M i mul Muls)
    (hp : ConstructionPersistentProfiles.ProbeProfile w D mul a b d p node) :
    ConstructionDirectedProfiles.PersistentProfile J E Domains F Muls w i a b d p node := by
  intro j N mulN t mapped aa bb dd pp hj hij hN hmulN ht hMapped hNode ha hb hd hpp
  have hCv := hCons i j D N mul mulN t hi hj hij hD hN hm hmulN ht
  obtain ⟨mapped',aa',bb',dd',pp',hNode',ha',hb',hd',hpp',hProfile⟩ :=
    hProfiles i j D N mul mulN t hi hj hij hD hN hm hmulN ht a b d p node hp
  have heNode := ConstructionRequestMaps.node_map_unique hM hProfile.2.2.2.2.1 hMapped hNode' hNode
  have hea := function_unique hCv.1.1.1 ha' ha
  have heb := function_unique hCv.1.1.1 hb' hb
  have hed := function_unique hCv.1.1.1 hd' hd
  have hep := function_unique hCv.1.1.1 hpp' hpp
  simpa only [heNode,hea,heb,hed,hep] using hProfile

theorem origin_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C i : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hMarks : FunctionOn J Marks)
    (hH : FunctionOn J Heights) (hC : FunctionOn J Costs)
    (hOrigins : OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
    ∃ N mulN eN markN HN CN fi, PureKuratowski.PairMember M i N Domains ∧
      PureKuratowski.PairMember M i mulN Muls ∧ PureKuratowski.PairMember M i eN Units ∧
      PureKuratowski.PairMember M i markN Marks ∧ PureKuratowski.PairMember M i HN Heights ∧
      PureKuratowski.PairMember M i CN Costs ∧ PureKuratowski.PairMember M i fi Origins ∧
      ForcingDiagramPoset.LeftCancelMonoid N mulN eN ∧
      MapFields hM w Q D N mul mulN e eN mark markN H C HN CN fi := by
  obtain ⟨N,mulN,eN,hN,hm,he,hMon⟩ := ConstructionDirectedMonoidData.family_at hFam hi
  obtain ⟨markN,ha,_⟩ := hMarks.2 i hi
  obtain ⟨HN,hh,_⟩ := hH.2 i hi
  obtain ⟨CN,hc,_⟩ := hC.2 i hi
  obtain ⟨fi,hfi,_⟩ := hOrigins.1.2 i hi
  exact ⟨N,mulN,eN,markN,HN,CN,fi,hN,hm,he,ha,hh,hc,hfi,hMon,
    hOrigins.2 i N mulN eN markN HN CN fi hi hN hm he ha hh hc hfi⟩

theorem full_legs (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top J E Domains F Muls Units Marks Heights Costs L projection G unit mark HL LC K : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hMarks : FunctionOn J Marks)
    (hWH : FunctionOn J Heights) (hWC : FunctionOn J Costs)
    (hK : ConstructionDirectedCocone.Cocone J E Domains F L projection K)
    (hLegs : ConstructionDirectedLift.Legs J Domains Muls Units K L G unit)
    (hMarkLegs : ConstructionDirectedLift.MarkLegs J Marks K mark)
    (hWeights : ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC) :
    FullLegs hM w Q J Domains Muls Units Marks Heights Costs K L G unit mark HL LC := by
  obtain ⟨_,_,_,_,_,_,_,_,hOld⟩ := hWeights
  refine ⟨hFam.1,hFam.2.1,hFam.2.2.1,hMarks,hWH,hWC,?_⟩
  intro i D mul e a H C ki hi hD hm he ha hH hC hki
  have hBasic := hLegs i D mul e ki hi hD hm he hki
  have hW := hOld i D mul H C ki hi hD hm hH hC (hK.1.2 i D ki hi hD hki)
    (hK.2.2 i D ki hi hD hki)
  exact ⟨hBasic.2.2,hBasic.1,hBasic.2.1,hMarkLegs i a ki hi ha hki,hW⟩

theorem profile_legs (hM : FirstOrder.Theory.Models M nativeZF)
    {w J E Domains F Muls Units C L projection B G unit K : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : ConstructionDirectedLimitCarrier.Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : ConstructionDirectedLimitCarrier.Carrier J E Domains F C L)
    (hP : ConstructionDirectedLimitCarrier.Projection J E Domains F C projection)
    (hEq : ConstructionDirectedLimitCarrier.EqualityLaw J E Domains F projection) (hG : MapsTo B L G)
    (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : ForcingDiagramPoset.LeftCancelMonoid L G unit)
    (hImage : ConstructionDirectedMonoid.UnitImage J Domains Units projection unit)
    (hK : ConstructionDirectedCocone.Cocone J E Domains F L projection K)
    (hProfiles : ProfileTransitions w J E Domains F Muls) :
    ProfileLegs w J Domains Muls K L G := by
  intro i D mul ki hi hD hm hki a b d p node hProfile
  obtain ⟨e,he,_⟩ := hFam.2.2.1.2 i hi
  have hTransport := ConstructionDirectedProfiles.profile_transport hM hFam hE hT hCons
    hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he
    (hK.1.2 i D ki hi hD hki) (hK.2.2 i D ki hi hD hki)
  exact hTransport w a b d p node hProfile.1 hProfile.2.1 hProfile.2.2.1 hProfile.2.2.2.1
    hProfile.2.2.2.2.1 (persistent_of_transitions hM hCons hProfiles hi hD hm hProfile)

/-- Directedness and existing naturality make every old-stage image of a
base element have the SAME limit value. No choice of a stage per element. -/
theorem origin_images_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q J E Domains F Muls Units Marks Heights Costs Origins D mul e mark H C
      K L i j fi fj ki kj x xi xj zi zj : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hMarks : FunctionOn J Marks) (hWH : FunctionOn J Heights) (hWC : FunctionOn J Costs)
    (hOrigins : OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C)
    (hNat : OriginNatural J E F Origins) (hK : WeightFamily J Domains L K)
    (hStable : Stable J E Domains F K)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hfi : PureKuratowski.PairMember M i fi Origins) (hfj : PureKuratowski.PairMember M j fj Origins)
    (hki : PureKuratowski.PairMember M i ki K) (hkj : PureKuratowski.PairMember M j kj K)
    (hxi : PureKuratowski.PairMember M x xi fi) (hxj : PureKuratowski.PairMember M x xj fj)
    (hzi : PureKuratowski.PairMember M xi zi ki) (hzj : PureKuratowski.PairMember M xj zj kj) : zi = zj := by
  obtain ⟨Di,mi,ei,ai,Hi,Ci,fi',hDi,hmi,hei,hai,hHi,hCi,hfi',hMonI,hMapI⟩ :=
    origin_at hM hFam hMarks hWH hWC hOrigins hi
  obtain ⟨Dj,mj,ej,aj,Hj,Cj,fj',hDj,hmj,hej,haj,hHj,hCj,hfj',hMonJ,hMapJ⟩ :=
    origin_at hM hFam hMarks hWH hWC hOrigins hj
  have hfiEq := function_unique hOrigins.1 hfi' hfi
  have hfjEq := function_unique hOrigins.1 hfj' hfj
  subst fi'; subst fj'
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hj
  obtain ⟨Dk,mk,ek,ak,Hk,Ck,fk,hDk,hmk,hek,hak,hHk,hCk,hfk,_,hMapK⟩ :=
    origin_at hM hFam hMarks hWH hWC hOrigins hk
  obtain ⟨kk,hkk,_⟩ := hK.1.2 k hk
  obtain ⟨_,hti⟩ := hT.1 i k ei ⟨hi,Di,hDi,hMonI.1.1⟩ hk hik
  obtain ⟨ti,hFti,_⟩ := hti.2.2
  obtain ⟨_,htj⟩ := hT.1 j k ej ⟨hj,Dj,hDj,hMonJ.1.1⟩ hk hjk
  obtain ⟨tj,hFtj,_⟩ := htj.2.2
  have hTi := (hCons i k Di Dk mi mk ti hi hk hik hDi hDk hmi hmk hFti).1.1
  have hTj := (hCons j k Dj Dk mj mk tj hj hk hjk hDj hDk hmj hmk hFtj).1.1
  have hxiD := hMapI.1.1.1.2 x xi hxi
  have hxjD := hMapJ.1.1.1.2 x xj hxj
  obtain ⟨yi,hyi,_⟩ := hTi.1.2 xi hxiD
  obtain ⟨yj,hyj,_⟩ := hTj.1.2 xj hxjD
  have hFki := ((hNat i k fi fk ti hi hk hik hfi hfk hFti) x yi).mpr ⟨xi,hxi,hyi⟩
  have hFkj := ((hNat j k fj fk tj hj hk hjk hfj hfk hFtj) x yj).mpr ⟨xj,hxj,hyj⟩
  have hEqY := function_unique hMapK.1.1.1.1 hFki hFkj
  have hsi := hStable i k xi yi zi ki kk hik
    ⟨⟨hi,Di,hDi,hxiD⟩,⟨hk,Dk,hDk,hTi.2 xi yi hyi⟩,ti,hFti,hyi⟩ hki hkk hzi
  have hsj := hStable j k xj yj zj kj kk hjk
    ⟨⟨hj,Dj,hDj,hxjD⟩,⟨hk,Dk,hDk,hTj.2 xj yj hyj⟩,tj,hFtj,hyj⟩ hkj hkk hzj
  exact function_unique (hK.2 k Dk kk hk hDk hkk).1 hsi (hEqY.symm ▸ hsj)

theorem exists_base (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q J E Domains F Muls Units Marks Heights Costs Origins D mul e mark H C
      K L G unit markL HL LC : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hOrigins : OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C)
    (hNat : OriginNatural J E F Origins)
    (hK : WeightFamily J Domains L K) (hStable : Stable J E Domains F K)
    (hFull : FullLegs hM w Q J Domains Muls Units Marks Heights Costs K L G unit markL HL LC)
    (hMon : ForcingDiagramPoset.LeftCancelMonoid L G unit) :
    ∃ base, MapFields hM w Q D L mul G e unit mark markL H C HL LC base ∧
      BaseNatural J Origins K base ∧
      (OriginProfiles w J Domains Muls Origins D mul → ProfileLegs w J Domains Muls K L G →
        Profiles w D L mul G base) ∧
      ∀ other, MapsTo D L other → BaseNatural J Origins K other → other = base := by
  obtain ⟨i0,hi0⟩ := hne
  obtain ⟨N,mulN,eN,markN,HN,CN,f0,hN,hm,he,ha,hH,hC,hf0,hMonN,hMap0⟩ :=
    origin_at hM hFam hFull.2.2.2.1 hFull.2.2.2.2.1 hFull.2.2.2.2.2.1 hOrigins hi0
  obtain ⟨k0,hk0,_⟩ := hK.1.2 i0 hi0
  have hMapK := hFull.2.2.2.2.2.2 i0 N mulN eN markN HN CN k0 hi0 hN hm he ha hH hC hk0
  obtain ⟨base,hBase,hComp,hFields⟩ := exists_fromBase hM hMonN hMon hMap0 hMapK
  have hNatural : BaseNatural J Origins K base := by
    intro i fi ki hi hfi hki x z
    constructor
    · intro hxz
      obtain ⟨x0,hx0,hx0z⟩ := (hComp x z).mp hxz
      obtain ⟨Ni,mi,ei,ai,Hi,Ci,fi',hNi,hmi,hei,hai,hHi,hCi,hfi',_,hMi⟩ :=
        origin_at hM hFam hFull.2.2.2.1 hFull.2.2.2.2.1 hFull.2.2.2.2.2.1 hOrigins hi
      have hefi := function_unique hOrigins.1 hfi' hfi
      subst fi'
      obtain ⟨xi,hxi,_⟩ := hMi.1.1.1.1.2 x (ForcingConditionGraphs.function_input hBase.1 hxz)
      obtain ⟨zi,hzi,_⟩ := (hK.2 i Ni ki hi hNi hki).1.2 xi (hMi.1.1.1.2 x xi hxi)
      have heq := origin_images_eq hM hFam hE hT hCons hFull.2.2.2.1 hFull.2.2.2.2.1 hFull.2.2.2.2.2.1
        hOrigins hNat hK hStable hi0 hi hf0 hfi hk0 hki hx0 hxi hx0z hzi
      exact ⟨xi,hxi,heq.symm ▸ hzi⟩
    · rintro ⟨xi,hxi,hxiz⟩
      obtain ⟨Ni,mi,ei,ai,Hi,Ci,fi',hNi,hmi,hei,hai,hHi,hCi,hfi',_,hMi⟩ :=
        origin_at hM hFam hFull.2.2.2.1 hFull.2.2.2.2.1 hFull.2.2.2.2.2.1 hOrigins hi
      have hefi := function_unique hOrigins.1 hfi' hfi
      subst fi'
      obtain ⟨x0,hx0,_⟩ := hMap0.1.1.1.1.2 x (ForcingConditionGraphs.function_input hMi.1.1.1.1 hxi)
      obtain ⟨z0,hz0,_⟩ := (hK.2 i0 N k0 hi0 hN hk0).1.2 x0 (hMap0.1.1.1.2 x x0 hx0)
      have heq := origin_images_eq hM hFam hE hT hCons hFull.2.2.2.1 hFull.2.2.2.2.1 hFull.2.2.2.2.2.1
        hOrigins hNat hK hStable hi0 hi hf0 hfi hk0 hki hx0 hxi hz0 hxiz
      exact heq ▸ (hComp x z0).mpr ⟨x0,hx0,hz0⟩
  refine ⟨base,hFields,hNatural,?_,?_⟩
  · intro hOP hKP
    exact profiles_comp hComp (hOP i0 N mulN f0 hi0 hN hm hf0) (hKP i0 N mulN k0 hi0 hN hm hk0)
  · intro other hOther hNatOther
    exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
      ((ForcingSupportSize.native_mapsTo hM D L other).mp hOther).1.1
      ((ForcingSupportSize.native_mapsTo hM D L base).mp hBase).1.1
      (fun x z => (hNatOther i0 f0 k0 hi0 hf0 hk0 x z).trans (hComp x z).symm)


/-- Actual complete UNDER-base limit. The canonical quotient/projection and
weighted universal colimit are retained alongside every new tower field. -/
def Result (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C
      L G unit markL HL LC K base : M.Carrier .set) : Prop :=
  ∃ rep projection B, ConstructionDirectedLimitCarrier.Representatives J Domains rep ∧
    MapsTo rep L projection ∧ ConstructionDirectedLimitCarrier.Carrier J E Domains F rep L ∧
    ConstructionDirectedLimitCarrier.Projection J E Domains F rep projection ∧
    ConstructionProbeLetters.Representatives L L B ∧ MapsTo B L G ∧
    ConstructionDirectedProduct.Graph J Domains Muls projection G ∧
    ConstructionDirectedMonoid.UnitImage J Domains Units projection unit ∧
    ConstructionDirectedMarks.MarkImage J Marks projection markL ∧
    ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC ∧
    ObjectFields hM w Q R top L G unit markL HL LC ∧
    ConstructionDirectedCocone.Cocone J E Domains F L projection K ∧
    FullLegs hM w Q J Domains Muls Units Marks Heights Costs K L G unit markL HL LC ∧
    ProfileLegs w J Domains Muls K L G ∧
    MapFields hM w Q D L mul G e unit mark markL H C HL LC base ∧
    BaseNatural J Origins K base ∧ Profiles w D L mul G base ∧
    ConstructionDirectedColimit.Colimit J E Domains F Muls Units Heights Costs Marks L projection G unit markL HL LC ∧
    ConstructionDirectedCardinality.Bound hM J Domains L ∧
    ∀ other, MapsTo D L other → BaseNatural J Origins K other → other = base
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C : M.Carrier .set)
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
    (hSup : SupremumLaws J E Domains F Muls Costs)
    (hCon : ConicalFamily J Domains Muls Units) (hJoins : JoinsFamily J Domains Muls Units)
    (hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks)
    (hMarkStable : ConstructionDirectedMarks.Stable J E Domains F Marks)
    (hProfiles : ProfileTransitions w J E Domains F Muls)
    (hOrigins : OriginLegs hM w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C)
    (hNat : OriginNatural J E F Origins) (hOP : OriginProfiles w J Domains Muls Origins D mul) :

    ∃ L G unit markL HL LC K base,
      Result hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C
        L G unit markL HL LC K base := by
  obtain ⟨rep,L,projection,B,G,unit,markL,hRep,hp,hL,hP,hEq,hB,hG,hGraph,hu,hImage,hMon,hConL,hJoinsL,
      hmark,hneMark,hMarkImage,_,HL,LC,hWeights,hCard,K,hKC,hLegs,hMarkLegs,hWeighted,hUniversal⟩ :=
    ConstructionDirectedColimit.exists_system hM J E Domains F Muls Units w Q R top Heights Costs Marks
      hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable
  have hFull := full_legs hM hFam hMarks.1 hWH.1 hWC.1 hKC hLegs hMarkLegs hWeights
  have hProfilesL := profile_legs hM hFam hE hT hCons hRep hp hL hP hEq hG hGraph hMon hImage hKC hProfiles
  obtain ⟨base,hBase,hNatural,hBaseProfiles,hUnique⟩ := exists_base hM hne hFam hE hT hCons
    hOrigins hNat hKC.1 hKC.2.1 hFull hMon
  have hObject : ObjectFields hM w Q R top L G unit markL HL LC := by
    have hwts := hWeights
    obtain ⟨hHL,_,hLC,_,hHeight,hCost,hUniformL,hExact,_⟩ := hwts
    exact ⟨hMon,hConL,hJoinsL,hmark,hneMark,hHL,hHeight,hLC,hCost,hUniformL,hExact,B,hB,hG⟩
  exact ⟨L,G,unit,markL,HL,LC,K,base,rep,projection,B,hRep,hp,hL,hP,hB,hG,hGraph,hImage,hMarkImage,
    hWeights,hObject,hKC,hFull,hProfilesL,hBase,hNatural,hBaseProfiles hOP hProfilesL,
    ⟨K,hKC,hLegs,hMarkLegs,hWeighted,hUniversal⟩,hCard,hUnique⟩


def originLegs {m : Nat} (w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Origins J)) (.forallE (.forallE (.forallE
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (7 : Fin (m+8))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+8)) (5 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Units.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (4 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Marks.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+8)) (3 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Heights.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (2 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Costs.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+8)) (1 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Origins.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (0 : Fin (m+8))))
  (ConstructionRoundStepSyntax.mapFields w.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8))
  mul.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8)) e.succ.succ.succ.succ.succ.succ.succ.succ (4 :
  Fin (m+8)) mark.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+8))
  H.succ.succ.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+8)) (1 :
  Fin (m+8)) (0 : Fin (m+8))))))))))))))))))))

theorem originLegs_freeClosed {m : Nat} (w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C : Fin m) :
    (originLegs w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C).FreeClosed := by
  simp -implicitDefEqProofs [originLegs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed]

theorem originLegs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C : Fin m) :
    Project.Formula.satisfies env (originLegs w Q J Domains Muls Units Marks Heights Costs Origins D mul e mark H C) ↔ OriginLegs hM (env.bound w) (env.bound Q) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound Marks) (env.bound Heights) (env.bound Costs) (env.bound Origins) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) := by
  simp only [originLegs,OriginLegs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionRoundStepSyntax.mapFields_semantics hM]
  rfl


def originProfiles {m : Nat} (w J Domains Muls Origins D mul : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound J.succ.succ.succ.succ))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ (3 : Fin (m+4)) (2 :
  Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ (3 : Fin
  (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Origins.succ.succ.succ.succ (3 : Fin (m+4)) (0 : Fin (m+4)))) (ConstructionRoundStepSyntax.profiles
  w.succ.succ.succ.succ D.succ.succ.succ.succ (2 : Fin (m+4)) mul.succ.succ.succ.succ (1 : Fin (m+4)) (0 :
  Fin (m+4)))))))))))

theorem originProfiles_freeClosed {m : Nat} (w J Domains Muls Origins D mul : Fin m) :
    (originProfiles w J Domains Muls Origins D mul).FreeClosed := by
  simp -implicitDefEqProofs [originProfiles,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed]

theorem originProfiles_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w J Domains Muls Origins D mul : Fin m) :
    Project.Formula.satisfies env (originProfiles w J Domains Muls Origins D mul) ↔ OriginProfiles (env.bound w) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Origins) (env.bound D) (env.bound mul) := by
  simp only [originProfiles,OriginProfiles,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRoundStepSyntax.profiles_semantics hM]
  rfl


def originNatural {m : Nat} (J E F Origins : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (4 : Fin (m+5))) (.bound
  J.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (3 : Fin (m+5))) (.bound J.succ.succ.succ.succ.succ))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 :
  Fin (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Origins.succ.succ.succ.succ.succ (4 :
  Fin (m+5)) (2 : Fin (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Origins.succ.succ.succ.succ.succ (3 : Fin (m+5)) (1 : Fin (m+5)))) (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product F.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 : Fin (m+5)) (0 : Fin (m+5))))
  (ConstructionProbeMappedPathSyntax.nodeMap (2 : Fin (m+5)) (0 : Fin (m+5)) (1 : Fin (m+5))))))))))))))

theorem originNatural_freeClosed {m : Nat} (J E F Origins : Fin m) :
    (originNatural J E F Origins).FreeClosed := by
  simp -implicitDefEqProofs [originNatural,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem originNatural_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E F Origins : Fin m) :
    Project.Formula.satisfies env (originNatural J E F Origins) ↔ OriginNatural (env.bound J) (env.bound E) (env.bound F) (env.bound Origins) := by
  simp only [originNatural,OriginNatural,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def profileTransitions {m : Nat} (w J E Domains F Muls : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (6 : Fin (m+7)))
  (.bound J.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (5 : Fin (m+7))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  E.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (5 : Fin (m+7)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (4 : Fin (m+7))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+7)) (3 : Fin (m+7)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Muls.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (2 : Fin (m+7)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+7)) (1 : Fin (m+7)))) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product F.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7))
  (5 : Fin (m+7)) (0 : Fin (m+7)))) (ConstructionRoundStepSyntax.profiles
  w.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+7)) (3 : Fin (m+7)) (2 : Fin (m+7)) (1 : Fin (m+7)) (0 :
  Fin (m+7))))))))))))))))))

theorem profileTransitions_freeClosed {m : Nat} (w J E Domains F Muls : Fin m) :
    (profileTransitions w J E Domains F Muls).FreeClosed := by
  simp -implicitDefEqProofs [profileTransitions,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed]

theorem profileTransitions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w J E Domains F Muls : Fin m) :
    Project.Formula.satisfies env (profileTransitions w J E Domains F Muls) ↔ ProfileTransitions (env.bound w) (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) := by
  simp only [profileTransitions,ProfileTransitions,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),ConstructionRoundStepSyntax.profiles_semantics hM]
  rfl


def result {m : Nat} (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ConstructionDirectedLimitCarrier.representatives J.succ.succ.succ
  Domains.succ.succ.succ (2 : Fin (m+3))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 :
  Fin (m+3)) (2 : Fin (m+3)) L.succ.succ.succ)) (.conj (ConstructionDirectedLimitCarrier.carrier
  J.succ.succ.succ E.succ.succ.succ Domains.succ.succ.succ F.succ.succ.succ (2 : Fin (m+3))
  L.succ.succ.succ) (.conj (ConstructionDirectedLimitCarrier.projectionGraph J.succ.succ.succ
  E.succ.succ.succ Domains.succ.succ.succ F.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))) (.conj
  (ConstructionProbeLetters.representatives L.succ.succ.succ L.succ.succ.succ (0 : Fin (m+3))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo G.succ.succ.succ (0 : Fin (m+3)) L.succ.succ.succ))
  (.conj (ConstructionDirectedProduct.graph J.succ.succ.succ Domains.succ.succ.succ Muls.succ.succ.succ (1 :
  Fin (m+3)) G.succ.succ.succ) (.conj (ConstructionDirectedMonoid.unitImage J.succ.succ.succ
  Domains.succ.succ.succ Units.succ.succ.succ (1 : Fin (m+3)) unit.succ.succ.succ) (.conj
  (ConstructionDirectedMarks.markImage J.succ.succ.succ Marks.succ.succ.succ (1 : Fin (m+3))
  markL.succ.succ.succ) (.conj (ConstructionDirectedHeightCost.laws w.succ.succ.succ Q.succ.succ.succ
  R.succ.succ.succ top.succ.succ.succ J.succ.succ.succ Domains.succ.succ.succ Muls.succ.succ.succ
  Heights.succ.succ.succ Costs.succ.succ.succ L.succ.succ.succ (1 : Fin (m+3)) G.succ.succ.succ
  HL.succ.succ.succ LC.succ.succ.succ) (.conj (ConstructionRoundStepSyntax.objectFields w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ L.succ.succ.succ G.succ.succ.succ unit.succ.succ.succ
  markL.succ.succ.succ HL.succ.succ.succ LC.succ.succ.succ) (.conj (ConstructionDirectedCocone.cocone
  J.succ.succ.succ E.succ.succ.succ Domains.succ.succ.succ F.succ.succ.succ L.succ.succ.succ (1 : Fin (m+3))
  K.succ.succ.succ) (.conj (ConstructionTowerSuccessor.fullLegs w.succ.succ.succ Q.succ.succ.succ
  J.succ.succ.succ Domains.succ.succ.succ Muls.succ.succ.succ Units.succ.succ.succ Marks.succ.succ.succ
  Heights.succ.succ.succ Costs.succ.succ.succ K.succ.succ.succ L.succ.succ.succ G.succ.succ.succ
  unit.succ.succ.succ markL.succ.succ.succ HL.succ.succ.succ LC.succ.succ.succ) (.conj
  (ConstructionTowerSuccessor.profileLegs w.succ.succ.succ J.succ.succ.succ Domains.succ.succ.succ
  Muls.succ.succ.succ K.succ.succ.succ L.succ.succ.succ G.succ.succ.succ) (.conj
  (ConstructionRoundStepSyntax.mapFields w.succ.succ.succ Q.succ.succ.succ D.succ.succ.succ L.succ.succ.succ
  mul.succ.succ.succ G.succ.succ.succ e.succ.succ.succ unit.succ.succ.succ mark.succ.succ.succ
  markL.succ.succ.succ H.succ.succ.succ C.succ.succ.succ HL.succ.succ.succ LC.succ.succ.succ
  base.succ.succ.succ) (.conj (ConstructionTowerSuccessor.baseNatural J.succ.succ.succ
  Origins.succ.succ.succ K.succ.succ.succ base.succ.succ.succ) (.conj (ConstructionRoundStepSyntax.profiles
  w.succ.succ.succ D.succ.succ.succ L.succ.succ.succ mul.succ.succ.succ G.succ.succ.succ
  base.succ.succ.succ) (.conj (ConstructionDirectedColimit.colimit J.succ.succ.succ E.succ.succ.succ
  Domains.succ.succ.succ F.succ.succ.succ Muls.succ.succ.succ Units.succ.succ.succ Heights.succ.succ.succ
  Costs.succ.succ.succ Marks.succ.succ.succ L.succ.succ.succ (1 : Fin (m+3)) G.succ.succ.succ
  unit.succ.succ.succ markL.succ.succ.succ HL.succ.succ.succ LC.succ.succ.succ) (.conj
  (ConstructionDirectedCardinality.boundProperty J.succ.succ.succ Domains.succ.succ.succ L.succ.succ.succ)
  (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+4)) D.succ.succ.succ.succ
  L.succ.succ.succ.succ)) (.imp (ConstructionTowerSuccessor.baseNatural J.succ.succ.succ.succ
  Origins.succ.succ.succ.succ K.succ.succ.succ.succ (0 : Fin (m+4))) (Project.Formula.extensionalEq (.bound
  (0 : Fin (m+4))) (.bound base.succ.succ.succ.succ)))))))))))))))))))))))))))

theorem result_freeClosed {m : Nat} (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base : Fin m) :
    (result J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionDirectedProduct.graph_freeClosed,ConstructionDirectedMonoid.unitImage_freeClosed,ConstructionDirectedMarks.markImage_freeClosed,ConstructionDirectedHeightCost.laws_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionDirectedCocone.cocone_freeClosed,ConstructionTowerSuccessor.fullLegs_freeClosed,ConstructionTowerSuccessor.profileLegs_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionTowerSuccessor.baseNatural_freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed,ConstructionDirectedColimit.colimit_freeClosed,ConstructionDirectedCardinality.boundProperty_freeClosed,Project.Formula.extensionalEq]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base : Fin m) :
    Project.Formula.satisfies env (result J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C L G unit markL HL LC K base) ↔ Result hM (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound Heights) (env.bound Costs) (env.bound Marks) (env.bound Origins) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound L) (env.bound G) (env.bound unit) (env.bound markL) (env.bound HL) (env.bound LC) (env.bound K) (env.bound base) := by
  simp only [result,Result,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionDirectedLimitCarrier.representatives_semantics hM,ConstructionDirectedLimitCarrier.carrier_semantics hM,ConstructionDirectedLimitCarrier.projectionGraph_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ConstructionDirectedProduct.graph_semantics hM,ConstructionDirectedMonoid.unitImage_semantics hM,ConstructionDirectedMarks.markImage_semantics hM,ConstructionDirectedHeightCost.laws_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionDirectedCocone.cocone_semantics hM,ConstructionTowerSuccessor.fullLegs_semantics hM,ConstructionTowerSuccessor.profileLegs_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionTowerSuccessor.baseNatural_semantics hM,ConstructionRoundStepSyntax.profiles_semantics hM,ConstructionDirectedColimit.colimit_semantics hM,ConstructionDirectedCardinality.boundProperty_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.imp (.existsE (.mem (.bound (0 : Fin 21)) (.bound (0 : Fin 20).succ)))
    (.imp (ConstructionDirectedSystem.indexLaws (0 : Fin 20) (1 : Fin 20)) (.imp
    (ConstructionDirectedSystem.transitionLaws (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20)) (.imp
    (ConstructionDirectedMonoidData.family (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20)) (.imp
    (ConstructionDirectedMonoidData.homLaws (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20)
    (5 : Fin 20)) (.imp (ConstructionDirectedConservativeData.conservativeTransitions (0 : Fin 20) (1 : Fin
    20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20)) (.imp (Project.Formula.isOmega (.bound (6 : Fin 20))) (.imp
    (ConstructionFractionOrder.carrier (6 : Fin 20) (7 : Fin 20)) (.imp (ConstructionRealCuts.cutCarrier (6
    : Fin 20) (7 : Fin 20) (8 : Fin 20)) (.imp (ConstructionRealCuts.cut (6 : Fin 20) (7 : Fin 20) (9 : Fin
    20)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 20) (2 : Fin 20) (8 : Fin 20) (10 : Fin
    20)) (.imp (ConstructionDirectedWeightData.weightFamily (0 : Fin 20) (2 : Fin 20) (8 : Fin 20) (11 : Fin
    20)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20)
    (10 : Fin 20)) (.imp (ConstructionDirectedWeightData.stable (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 :
    Fin 20) (11 : Fin 20)) (.imp (ConstructionDirectedWeightData.heightBounds (0 : Fin 20) (10 : Fin 20) (9
    : Fin 20)) (.imp (ConstructionDirectedWeightData.costBounds (0 : Fin 20) (11 : Fin 20) (9 : Fin 20))
    (.imp (ConstructionDirectedWeightData.uniformFamily (6 : Fin 20) (7 : Fin 20) (0 : Fin 20) (2 : Fin 20)
    (4 : Fin 20) (10 : Fin 20) (11 : Fin 20)) (.imp (ConstructionDirectedWeightData.supremumLaws (0 : Fin
    20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (11 : Fin 20)) (.imp
    (ConstructionDirectedMonoidData.conicalFamily (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20)) (.imp
    (ConstructionDirectedConservativeData.joinsFamily (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20))
    (.imp (ConstructionDirectedMarks.markFamily (0 : Fin 20) (2 : Fin 20) (5 : Fin 20) (12 : Fin 20)) (.imp
    (ConstructionDirectedMarks.stable (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (12 : Fin 20))
    (.imp (profileTransitions (6 : Fin 20) (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20))
    (.imp (originLegs (6 : Fin 20) (7 : Fin 20) (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (5 : Fin 20) (12 :
    Fin 20) (10 : Fin 20) (11 : Fin 20) (13 : Fin 20) (14 : Fin 20) (15 : Fin 20) (16 : Fin 20) (17 : Fin
    20) (18 : Fin 20) (19 : Fin 20)) (.imp (originNatural (0 : Fin 20) (1 : Fin 20) (3 : Fin 20) (13 : Fin
    20)) (.imp (originProfiles (6 : Fin 20) (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (13 : Fin 20) (14 : Fin
    20) (15 : Fin 20)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (result (0 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
    20).succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (3 :
    Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (5
    : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ
    (7 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin
    20).succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (10 :
    Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ
    (12 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (13 : Fin
    20).succ.succ.succ.succ.succ.succ.succ.succ (14 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (15 :
    Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (16 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ
    (17 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (18 : Fin
    20).succ.succ.succ.succ.succ.succ.succ.succ (19 : Fin 20).succ.succ.succ.succ.succ.succ.succ.succ (7 :
    Fin 28) (6 : Fin 28) (5 : Fin 28) (4 : Fin 28) (3 : Fin 28) (2 : Fin 28) (1 : Fin
    28) (0 : Fin 28)))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedMonoidData.homLaws_freeClosed,ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionDirectedWeightData.heightBounds_freeClosed,ConstructionDirectedWeightData.costBounds_freeClosed,ConstructionDirectedWeightData.uniformFamily_freeClosed,ConstructionDirectedWeightData.supremumLaws_freeClosed,ConstructionDirectedMonoidData.conicalFamily_freeClosed,ConstructionDirectedConservativeData.joinsFamily_freeClosed,ConstructionDirectedMarks.markFamily_freeClosed,ConstructionDirectedMarks.stable_freeClosed,profileTransitions_freeClosed,originLegs_freeClosed,originNatural_freeClosed,originProfiles_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,ConstructionDirectedMonoidData.family_semantics hM,ConstructionDirectedMonoidData.homLaws_semantics hM,ConstructionDirectedConservativeData.conservativeTransitions_semantics hM,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionDirectedWeightData.heightBounds_semantics hM,ConstructionDirectedWeightData.costBounds_semantics hM,ConstructionDirectedWeightData.uniformFamily_semantics hM,ConstructionDirectedWeightData.supremumLaws_semantics hM,ConstructionDirectedMonoidData.conicalFamily_semantics hM,ConstructionDirectedConservativeData.joinsFamily_semantics hM,ConstructionDirectedMarks.markFamily_semantics hM,ConstructionDirectedMarks.stable_semantics hM,profileTransitions_semantics hM,originLegs_semantics hM,originNatural_semantics hM,originProfiles_semantics hM,result_semantics hM]
  exact fun hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable hProfiles hOrigins hNat hOP =>
    exists_system hM (bound 0) (bound 1) (bound 2) (bound 3) (bound 4) (bound 5) (bound 6) (bound 7) (bound 8) (bound 9) (bound 10) (bound 11) (bound 12) (bound 13) (bound 14) (bound 15) (bound 16) (bound 17) (bound 18) (bound 19)
      hne hE hT hFam hHom hCons hw hQ hR hTop hWH hWC hStableH hStableC hHB hCB hUniform hSup hCon hJoins hMarks hMarkStable hProfiles hOrigins hNat hOP

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

/-- Regression endpoint: actual typed transitions give literal source hP. -/
def typedProfileSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 14 (.imp (ConstructionDirectedConservativeData.conservativeTransitions (1 :
    Fin 14) (2 : Fin 14) (3 : Fin 14) (4 : Fin 14) (5 : Fin 14)) (.imp (profileTransitions (0 : Fin 14) (1 :
    Fin 14) (2 : Fin 14) (3 : Fin 14) (4 : Fin 14) (5 : Fin 14)) (.imp (.mem (.bound (6 : Fin 14)) (.bound
    (1 : Fin 14))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin 14) (6 : Fin 14) (7 :
    Fin 14))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (5 : Fin 14) (6 : Fin 14) (8 : Fin
    14))) (.imp (ConstructionPersistentProfiles.probeProfile (0 : Fin 14) (7 : Fin 14) (8 : Fin 14) (9 : Fin
    14) (10 : Fin 14) (11 : Fin 14) (12 : Fin 14) (13 : Fin 14))
    (ConstructionDirectedProfiles.persistentProfile (1 : Fin 14) (2 : Fin 14) (3 : Fin 14) (4 : Fin 14) (5 :
    Fin 14) (0 : Fin 14) (6 : Fin 14) (9 : Fin 14) (10 : Fin 14) (11 : Fin 14) (12 : Fin 14) (13 : Fin
    14)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,profileTransitions_freeClosed,
      ConstructionPersistentProfiles.probeProfile_freeClosed,ConstructionDirectedProfiles.persistentProfile_freeClosed]

theorem typedProfile_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence typedProfileSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) typedProfileSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionDirectedConservativeData.conservativeTransitions_semantics hM,profileTransitions_semantics hM,
    ConstructionPersistentProfiles.probeProfile_semantics hM,ConstructionDirectedProfiles.persistentProfile_semantics hM]
  exact fun hc hp hi hD hm hProfile => persistent_of_transitions hM hc hp hi hD hm hProfile

theorem typedProfile_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence typedProfileSentence) := ModelTransfer.derives (fun _ hM => typedProfile_models hM)

end PPAC.Migration.ConstructionTowerLimit
