/- Pinned CellCuts.restrict_selected. Complete source Cell/Attachment witnesses
and typed conservative inclusion square on the SAME retained intersections.
The stage subobject fields are explicit; no merely injective hom is silently
promoted to a conservative ambient inclusion. -/
import PPAC.Migration.ConstructionRestrictedCellPushout

namespace PPAC.Migration.ConstructionCellRestriction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Matrix)
open ConstructionRoundFields (ObjectFields MapFields)
open ConstructionRoundSelection (Pack)
open ConstructionBlockBoundary (Realized)
open ConstructionProbePushout (Hom IsPushout)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionAttachmentCoefficients (OldFixed)
open ConstructionRealCuts (Subset)
open ForcingSupportSize (MapsTo Injection)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (IdentityGraph InverseGraph FunctionOn function_input function_unique)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact native representation of the two source Cell alternatives, retaining
all defining data and their full actual extension presentation. -/
def Cell (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero D mul e W G unit O : M.Carrier .set) : Prop :=
  (∃ a b d node factor terminal target L C projection I act E K P,
    b ≠ e ∧ d ≠ e ∧ ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O ∧
    ConstructionProbePath.TerminalTable w D mul node a terminal) ∨
  ∃ n P C L projection A T B roots, (Project.FirstOrderSemantics.reduct M).mem n w ∧
    ConstructionRequestCarrier.WellFormed n D P ∧ ConstructionMergerRelations.Valid n D mul P ∧
    ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots

/-- Source Attachment.cell/equiv/old, with both original-kernel hom graphs,
actual internal inverse, full old conservative inclusion and exact range. -/
def Attachment (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero D mul e T GT : M.Carrier .set) : Prop :=
  ∃ W G unit O F inv, Cell hM w zero D mul e W G unit O ∧ LeftCancelMonoid W G unit ∧
    Hom D W mul G e unit O ∧ Conservative D W mul G O ∧
    Hom W T G GT unit e F ∧ Hom T W GT G e unit inv ∧ InverseGraph F inv ∧ OldFixed O F ∧ Range W F T

theorem intersection_closed {V GV e A B C : M.Carrier .set}
    (ha : Closure V GV e A) (hb : Closure V GV e B)
    (hc : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z C ↔
      (Project.FirstOrderSemantics.reduct M).mem z A ∧ (Project.FirstOrderSemantics.reduct M).mem z B) : Closure V GV e C := by
  refine ⟨fun z hz => ha.1 z ((hc z).mp hz).1,(hc e).mpr ⟨ha.2.1,hb.2.1⟩,?_,?_,?_⟩
  · intro x y z hx hy hp
    exact (hc z).mpr ⟨ha.2.2.1 x y z ((hc x).mp hx).1 ((hc y).mp hy).1 hp,
      hb.2.2.1 x y z ((hc x).mp hx).2 ((hc y).mp hy).2 hp⟩
  · intro x y z hx hy hz hp
    exact (hc z).mpr ⟨ha.2.2.2.1 x y z ((hc x).mp hx).1 ((hc y).mp hy).1 hz hp,
      hb.2.2.2.1 x y z ((hc x).mp hx).2 ((hc y).mp hy).2 hz hp⟩
  · intro x y z hx hy hz hp
    exact (hc z).mpr ⟨ha.2.2.2.2 x y z ((hc x).mp hx).1 ((hc y).mp hy).1 hz hp,
      hb.2.2.2.2 x y z ((hc x).mp hx).2 ((hc y).mp hy).2 hz hp⟩

theorem product_comp {S D GV G GS : M.Carrier .set}
    (hs : ProductGraph S G GS) (hd : ProductGraph D GV G) (hSD : Subset S D) : ProductGraph S GV GS := by
  intro x y z
  exact ⟨fun h => ⟨((hs x y z).mp h).1,((hs x y z).mp h).2.1,
    ((hd x y z).mp ((hs x y z).mp h).2.2).2.2⟩,
    fun ⟨hx,hy,hp⟩ => (hs x y z).mpr ⟨hx,hy,(hd x y z).mpr ⟨hSD x hx,hSD y hy,hp⟩⟩⟩

theorem product_factor {S D GV G GS : M.Carrier .set}
    (hs : ProductGraph S GV GS) (hd : ProductGraph D GV G) (hSD : Subset S D) : ProductGraph S G GS := by
  intro x y z
  exact ⟨fun h => by
      obtain ⟨hx,hy,hp⟩ := (hs x y z).mp h
      exact ⟨hx,hy,(hd x y z).mpr ⟨hSD x hx,hSD y hy,hp⟩⟩,
    fun ⟨hx,hy,hp⟩ => (hs x y z).mpr ⟨hx,hy,((hd x y z).mp hp).2.2⟩⟩

/-- Reuse the existing conservative-hull inclusion proof at the SUPPLIED
identity graph. This preserves the original square's actual arrows. -/
theorem identity_inclusion {D mul e S G inc : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hJ : ConditionalJoins D mul)
    (hClosed : Closure D mul e S) (hG : ProductGraph S mul G)
    (hFn : FunctionOn S inc) (hId : IdentityGraph S inc) : Hom S D G mul e e inc ∧ Conservative S D G mul inc := by
  have hInj : Injection S D inc := by
    refine ⟨⟨hFn,?_⟩,?_⟩
    · intro x y hxy
      obtain ⟨hx,rfl⟩ := (hId x y).mp hxy
      exact hClosed.1 x hx
    · intro x y z hx hy
      exact ((hId x z).mp hx).2.trans ((hId y z).mp hy).2.symm
  refine ⟨⟨hInj.1,(hId e e).mpr ⟨hClosed.2.1,rfl⟩,?_⟩,hInj,?_,?_,?_⟩
  · intro x y z fx fy fz hp hx hy hz
    obtain ⟨_,rfl⟩ := (hId x fx).mp hx
    obtain ⟨_,rfl⟩ := (hId y fy).mp hy
    obtain ⟨_,rfl⟩ := (hId z fz).mp hz
    exact ((hG x y z).mp hp).2.2
  · intro x y z fx fy hx hy hz hp
    obtain ⟨hxS,rfl⟩ := (hId x fx).mp hx
    obtain ⟨hyS,rfl⟩ := (hId y fy).mp hy
    exact ⟨z,(hId z z).mpr ⟨hClosed.2.2.2.1 x y z hxS hyS hz hp,rfl⟩⟩
  · intro x y j fx fy fj hx hy hj hJoin
    obtain ⟨hxS,rfl⟩ := (hId x fx).mp hx
    obtain ⟨hyS,rfl⟩ := (hId y fy).mp hy
    obtain ⟨hjS,rfl⟩ := (hId j fj).mp hj
    exact ConstructionConservativeHull.join_preserve hm hc hJ hClosed hG hxS hyS hjS hJoin
  · intro x y fx fy hx hy hCommon
    obtain ⟨hxS,rfl⟩ := (hId x fx).mp hx
    obtain ⟨hyS,rfl⟩ := (hId y fy).mp hy
    exact ConstructionConservativeHull.common hm hJ hClosed hG hxS hyS hCommon

def Restricted (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion : M.Carrier .set) : Prop :=
  ConstructionSelectedCellRestriction.Base D mul e cut pairs cutMul inc ∧ ProductGraph D GV mul ∧
    Closure V GV e retained ∧ Closure V GV e cut ∧ Closure V GV e next ∧
    ProductGraph T GV GT ∧ ProductGraph next GV GNext ∧
    LeftCancelMonoid T GT e ∧ Conical T GT e ∧ ConditionalJoins T GT ∧
    LeftCancelMonoid next GNext e ∧ Conical next GNext e ∧ ConditionalJoins next GNext ∧
    IdentityGraph D old ∧ Hom D T mul GT e e old ∧ Conservative D T mul GT old ∧
    Hom cut next cutMul GNext e e inc ∧ Conservative cut next cutMul GNext inc ∧
    Hom next T GNext GT e e inclusion ∧ Conservative next T GNext GT inclusion ∧ IdentityGraph next inclusion ∧
    IsPushout D next T mul GNext GT e e e inc inc inclusion old ∧ Attachment hM w zero cut cutMul e next GNext ∧
    ConstructionStepCell.TypedProduct D mul ∧ ConstructionStepCell.TypedProduct T GT ∧
    ConstructionStepCell.TypedProduct next GNext

/-- Complete the typed conservative square and the literal Attachment after
the existing work theorem. Every inclusion uses its original identity graph. -/
theorem finish (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion
      W G unit F W0 G0 unit0 O0 H embedding pairsT invF pairsNext invEmbedding : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hD : Closure V GV e D) (hT : Closure V GV e T) (hRet : Closure V GV e retained)
    (hProduct : ProductGraph D GV mul) (hTypedD : ConstructionStepCell.TypedProduct D mul)
    (hDT : Subset D T)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D)
    (hNext : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z next ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z T)
    (hBase : ConstructionSelectedCellRestriction.Base D mul e cut pairs cutMul inc)
    (hOldMap : MapsTo D V old) (hOldId : IdentityGraph D old)
    (hCell : Cell hM w zero cut cutMul e W0 G0 unit0 O0) (hm0 : LeftCancelMonoid W0 G0 unit0)
    (hO0 : Hom cut W0 cutMul G0 e unit0 O0) (hCons0 : Conservative cut W0 cutMul G0 O0)
    (hWork : ConstructionRestrictedCellPushout.Result D mul e T next W G unit F W0 G0 unit0 O0 H V GV old inc
      embedding pairsT GT invF pairsNext GNext invEmbedding inclusion) :
    Restricted hM w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion := by
  have hBaseKeep := hBase
  obtain ⟨hCutD,_,_,hProductCut,_,_,hIdInc,hInc,_,_⟩ := hBase
  obtain ⟨hPairsT,hMapT,hProdT,hmT,_,_,_,hPairsNext,hMapNext,hProdNext,hmNext,hEmb,hInv,hInverse,_,_,_,hFixed,hRange,hIncl, hInclId,hPush⟩ := hWork
  have hCutV := intersection_closed hRet hD hCut
  have hNextV := intersection_closed hRet hT hNext
  have hcT := ConstructionConservativeHull.conical hc hT.1 hProdT
  have hJT := ConstructionConservativeHull.conditional_joins hJ hT hProdT
  have hcNext := ConstructionConservativeHull.conical hc hNextV.1 hProdNext
  have hJNext := ConstructionConservativeHull.conditional_joins hJ hNextV hProdNext
  have hCutNext : Subset cut next := fun x hx =>
    (hNext x).mpr ⟨((hCut x).mp hx).1,hDT x ((hCut x).mp hx).2⟩
  have hDInT := ConstructionSelectedCellRestriction.cut_closed hv hc hJ hT hProdT hD
    (fun x => ⟨fun hx => ⟨hx,hDT x hx⟩,And.left⟩)
  have hCutInNext := ConstructionSelectedCellRestriction.cut_closed hv hc hJ hNextV hProdNext hCutV
    (fun x => ⟨fun hx => ⟨hx,hCutNext x hx⟩,And.left⟩)
  have hNextInT := ConstructionSelectedCellRestriction.cut_closed hv hc hJ hT hProdT hRet hNext
  have hProdDT := product_factor hProduct hProdT hDT
  have hProdCutV := product_comp hProductCut hProduct hCutD.1
  have hProdCutNext := product_factor hProdCutV hProdNext hCutNext
  have hProdNextT := product_factor hProdNext hProdT (fun x hx => ((hNext x).mp hx).2)
  obtain ⟨hOldHom,hOldCons⟩ := identity_inclusion hmT hcT hJT hDInT hProdDT hOldMap.1 hOldId
  obtain ⟨hCutHom,hCutCons⟩ := identity_inclusion hmNext hcNext hJNext hCutInNext hProdCutNext hInc.1.1 hIdInc
  obtain ⟨_,hNextCons⟩ := identity_inclusion hmT hcT hJT hNextInT hProdNextT hIncl.1.1 hInclId
  exact ⟨hBaseKeep,hProduct,hRet,hCutV,hNextV,hProdT,hProdNext,hmT,hcT,hJT,hmNext,hcNext,hJNext,
    hOldId,hOldHom,hOldCons,hCutHom,hCutCons,hIncl,hNextCons,hInclId,hPush,
    ⟨W0,G0,unit0,O0,embedding,invEmbedding,hCell,hm0,hO0,hCons0,hEmb,hInv,hInverse,hFixed,hRange⟩,
    hTypedD,⟨pairsT,hPairsT,hMapT⟩,⟨pairsNext,hPairsNext,hMapNext⟩⟩

/-- Turn the existing pointwise generator equations into the SAME complete
composite graph. Totality comes from the actual two presentations. -/
theorem generator_map {I W WN P PN H : M.Carrier .set}
    (hP : MapsTo I W P) (hPN : MapsTo I WN PN) (hH : FunctionOn W H)
    (hValues : ∀ i x y, PureKuratowski.PairMember M i x P → PureKuratowski.PairMember M i y PN →
      PureKuratowski.PairMember M x y H) : NodeMap P H PN := by
  intro i y
  constructor
  · intro hiy
    obtain ⟨x,hix,_⟩ := hP.1.2 i (function_input hPN.1 hiy)
    exact ⟨x,hix,hValues i x y hix hiy⟩
  · rintro ⟨x,hix,hxy⟩
    obtain ⟨z,hiz,_⟩ := hPN.1.2 i (function_input hP.1 hix)
    exact (function_unique hH (hValues i x z hix hiz) hxy) ▸ hiz

/-- Both alternatives of the SAME fixed cell. No caller supplies an
attachment, simulation, inverse or pushout; all are outputs of the retained
source producers. The successor stage retains its source subobject field. -/
theorem restrict_cell (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e D T retained cut next cell : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hT : Closure V GV e T) (hRet : Closure V GV e retained)
    (hData : ConstructionStepCell.Data hM w zero one V GV e D T cell)
    (hSelected : ConstructionSelectedCellWords.Retained w zero V GV e D T cell retained cut)
    (hNext : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z next ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z T) :
    ∃ mul pairs cutMul inc GT GNext old inclusion,
      Restricted hM w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion := by
  have hRetSub : ConstructionCellGeneration.Submonoid V GV e retained := ⟨hRet.1,hRet.2.1,hRet.2.2.1⟩
  rcases hData with hData | hData
  · obtain ⟨mul,a,b,d,node,factor,terminal,target,L,C,projection,I,act,E,W,unit,G,K,P,O,F,
      p0,p1,presentation,parameters,old,generators,supports,deps,
      _,_,_,hmD,_,_,hA,hF,hFInj,hFixed,hRange,hParams,hResult,hPack,hbne,hdne,hTerminal,hOldCons,hD,hProduct,hTypedD⟩ := hData
    obtain ⟨_,_,hDT,hOldMap,hOldId,_,hGenMap,hGen,_⟩ := hResult.1
    obtain ⟨hParamsRet,hGensRet,hCut,hWords⟩ := ConstructionSelectedCellWords.read_retained hSelected hPack hGenMap
    obtain ⟨pairs,cutMul,inc,hBase⟩ := ConstructionSelectedCellRestriction.base hM hv hc hJ hD hProduct hRet hCut
    have hBaseKeep := hBase
    obtain ⟨_,_,_,_,hmCut,hcCut,hIncId,hInc,hCons,hJCut⟩ := hBase
    have hCovered := ConstructionSelectedCellWords.probe_covered hParams hResult.2.1 hParamsRet hCut hIncId
    obtain ⟨a0,b0,d0,node0,factor0,terminal0,target0,L0,C0,projection0,I0,act0,E0,W0,unit0,G0,K0,P0,O0,H,
      _,hb0,hd0,_,hA0,hTerminal0,hOld0Cons,hm0,hGenerated,hH,hConH,hEnd,hPush⟩ :=
      ConstructionRestrictedCellSimulation.probe hM hw hz hzw hmCut hcCut hJCut hA hTerminal hOldCons hbne hdne hInc hCons hCovered
    have hb0ne : b0 ≠ e := fun he => hbne (function_unique hInc.1.1 (he ▸ hb0) hInc.2.1)
    have hd0ne : d0 ≠ e := fun he => hdne (function_unique hInc.1.1 (he ▸ hd0) hInc.2.1)
    have hCell : Cell hM w zero cut cutMul e W0 G0 unit0 O0 := Or.inl
      ⟨a0,b0,d0,node0,factor0,terminal0,target0,L0,C0,projection0,I0,act0,E0,K0,P0,hb0ne,hd0ne,hA0,hTerminal0⟩
    have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmD hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication
    have hOld0 := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hmCut hA0.alphabet hA0.word hA0.b_mem hA0.old_unit hA0.multiplication hA0.old_graph
    have hO0 : Hom cut W0 cutMul G0 e unit0 O0 := ⟨hA0.old_map,hOld0.1,
      fun x y z fx fy fz hp hx hy hzv => hOld0.2.1 x y z fx fy fz hx hy hzv hp⟩
    have hGen0 := generator_map hA0.probes_map hA.probes_map hH.1.1 hEnd.2
    obtain ⟨embedding,pairsT,GT,invF,pairsNext,GNext,invEmbedding,inclusion,hWork⟩ :=
      ConstructionRestrictedCellPushout.work hM hmW hm0 hv hA.old_map hA0.old_map hA0.probes_map
        hF hFInj hRange hH hConH.1 hPush hFixed hOldId hIncId hGenerated hGen hGen0 hGensRet hRetSub hCut hNext hWords
    exact ⟨mul,pairs,cutMul,inc,GT,GNext,old,inclusion,
      finish hM hv hc hJ hD hT hRet hProduct hTypedD hDT hCut hNext hBaseKeep hOldMap hOldId hCell hm0 hO0 hOld0Cons hWork⟩
  · obtain ⟨mul,n,P,C,L,projection,A,W,TW,B,G,unit,O,roots,F,p0,presentation,parameters,old,generators,supports,deps,
      _,_,hn,_,_,_,hValid,hA,hF,hFInj,hFixed,hRange,hParams,hResult,hPack,hmW,_,hD,hProduct,hWell,hTypedD⟩ := hData
    obtain ⟨_,_,hDT,hOldMap,hOldId,_,hGenMap,hGen,_⟩ := hResult.1
    obtain ⟨hParamsRet,hGensRet,hCut,hWords⟩ := ConstructionSelectedCellWords.read_retained hSelected hPack hGenMap
    obtain ⟨pairs,cutMul,inc,hBase⟩ := ConstructionSelectedCellRestriction.base hM hv hc hJ hD hProduct hRet hCut
    have hBaseKeep := hBase
    obtain ⟨_,_,_,_,hmCut,hcCut,hIncId,hInc,hCons,hJCut⟩ := hBase
    have hCovered := ConstructionSelectedCellWords.merger_covered hParams hResult.2.1 hParamsRet hCut hIncId
    obtain ⟨P0,C0,L0,projection0,A0,W0,T0,B0,G0,unit0,O0,roots0,H,
      hWell0,hValid0,_,hA0,hm0,_,hGenerated,hH,hConH,_,hRoots,hPush⟩ :=
      ConstructionRestrictedCellSimulation.merger hM hw hz hzw hmCut hcCut hJCut hA hWell hValid hInc hCons hCovered
    have hCell : Cell hM w zero cut cutMul e W0 G0 unit0 O0 := Or.inr
      ⟨n,P0,C0,L0,projection0,A0,T0,B0,roots0,hn,hWell0,hValid0,hA0⟩
    have hOld0Inj : Injection cut W0 O0 := ⟨hA0.old_hom.1,fun x y q hx hy =>
      ConstructionProbeRaw.old_injective ((hA0.old_graph x q).mp hx) ((hA0.old_graph y q).mp hy)⟩
    have hOld0Cons := ConstructionMergerOldEmbedding.old_conservative hM hw hz hzw hA0.word
      hA0.product_representatives hA0.product_map hA0.word_action hA0.product hOld0Inj hA0.old_graph
    obtain ⟨embedding,pairsT,GT,invF,pairsNext,GNext,invEmbedding,inclusion,hWork⟩ :=
      ConstructionRestrictedCellPushout.work hM hmW hm0 hv hA.old_hom.1 hA0.old_hom.1 hA0.roots_map
        hF hFInj hRange hH hConH.1 hPush hFixed hOldId hIncId hGenerated hGen hRoots hGensRet hRetSub hCut hNext hWords
    exact ⟨mul,pairs,cutMul,inc,GT,GNext,old,inclusion,
      finish hM hv hc hJ hD hT hRet hProduct hTypedD hDT hCut hNext hBaseKeep hOldMap hOldId hCell hm0 hA0.old_hom hOld0Cons hWork⟩

/-- The source CellTower.stage values are conservative subobjects of V.
This field is explicit and must be supplied by the actual tower constructor. -/
def Stages (V GV e S : M.Carrier .set) : Prop := ∀ i D,
  PureKuratowski.PairMember M i D S → Closure V GV e D

theorem trace_stages (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code after
      V GV unitV markV HV CV J Domains E F L Out Images : M.Carrier .set}
    (ht : ConstructionBlockTraces.Trace hM w Q R top D mul e mark H C zero one K mu Requests W G unitW markW HW CW O code)
    (hd : ConstructionActualBlocks.Data code W after V J Domains E F L Out Images)
    (hV : ObjectFields hM w Q R top V GV unitV markV HV CV)
    (ha : MapFields hM w Q W V G GV unitW unitV markW markV HW CW HV CV after) :
    Stages V GV unitV Images := by
  obtain ⟨Schedule,last,history,EventsSet,Events,Roots,hpack,hchart,_,_,_,hresult,_,_⟩ := hd
  obtain ⟨u,A,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    history',P,F',EventsSet',Events',Roots',L',hpack',hctx,hschedule,_,hrec,hF,_,_,_,hrow,_⟩ := ht
  obtain ⟨eJ,eS,el,eh,eF,eSteps,eEvents,eRoots,eL⟩ := ConstructionRoundSelection.pack_injective hpack hpack'
  subst J' Schedule' last' history' F' EventsSet' Events' Roots' L'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hends,_⟩ := hschedule
  have hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last := by
    intro x
    constructor
    · intro hx
      rcases (hends x).mp hx with h | h
      · exact Or.inl h
      · subst x
        exact Or.inr (fun _ => Iff.rfl)
    · rintro (h | h)
      · exact (hends x).mpr (Or.inl h)
      · exact (hends x).mpr (Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members x last h))
  have hv := ConstructionTowerIterationValidity.recursive_valid hM hctx hrec (fun _ h => h)
  have hl := hs.predecessor_mem
  have hLast := hv.2.1 last hl W G unitW markW HW CW L O hrow
  obtain ⟨next,identity,hNext,hFn,_,_⟩ := hLast.2.2.2
  have en : next = J := (ModelTransfer.extensionality hM).eq_of_same_members next J
    (fun x => (hNext x).trans (hs x).symm)
  subst next
  intro i A0 hA0
  have hi := function_input hresult.2.2.2.2.1.1 hA0
  obtain ⟨N,mN,eN,aN,HN,CN,KN,bN,hRow⟩ := hv.1.2 i hi
  have hObj := (hv.2.1 i hi N mN eN aN HN CN KN bN hRow).1
  have hDi := (hchart.2 i N).mpr ⟨hi,ConstructionTowerValidity.row_field 0 hRow⟩
  obtain ⟨li,hli,_⟩ := hFn.2 i hi
  have hMi := (hv.2.2.1 i last N mN eN aN HN CN KN bN W G unitW markW HW CW L O li
    hi hl (ConstructionActualBlocks.before_last hM hs hi) hRow hrow hli).1
  obtain ⟨leg,hleg,_⟩ := hresult.2.1.1.2 i hi
  have hMap := ConstructionRoundFields.map_comp hM hLast.1.1 hV.1 hMi ha
    (hresult.2.1.2 i N leg hi hDi hleg) (hresult.2.2.1 i li leg hi hli hleg)
  have hRange := ConstructionBlockStages.range_at hchart.1 hresult.2.1.1 hresult.2.2.2.2.1 hDi hleg hA0
  exact ConstructionBlockStages.range_closed hObj.1 hObj.2.2.1 hV.1 hV.2.1
    ⟨hMap.1.1.1,hMap.2.2.1,hMap.2.1⟩ hMap.1 hRange

theorem realized_stages (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV i code next N W fromBase after
      J Domains E F L Out Images : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.At hM w Q R top zero one K mu history outerF i code)
    (hd : Realized history outerF kappa V zero i code next N W fromBase after J Domains E F L Out Images) :
    Stages V GV unitV Images := by
  obtain ⟨next',raw,Requests,N',mulN,eN,markN,HN,CN,L0,f,W',G,unitW,markW,HW,CW,NewOut,baseW,O,
    hsucc,_,hrj,_,_,_,_,_,htrace⟩ := ht
  have en : next' = next := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun x => (hsucc x).trans (hd.1 x).symm)
  subst next'
  have eW : W' = W := ConstructionTowerHistory.field_unique 0 hv.1.1 (row_field 0 hrj) hd.2.2.1
  subst W'
  have hj : (Project.FirstOrderSemantics.reduct M).mem next B := by
    obtain ⟨raw,hraw,_⟩ := hrj
    exact function_input hv.1.1 hraw
  have hk := hs.predecessor_mem
  have hbefore := ConstructionActualBlocks.before_last hM hs hj
  have hAfter := (ConstructionTowerTransitions.matrix_at hv.1 hf hj hk hbefore (row_field 6 hr)).mp hd.2.2.2.2.1
  have ha := (hv.2.2.1 next kappa W G unitW markW HW CW NewOut baseW
    V GV unitV markV HV CV terminalLegs baseV after hj hk hbefore hrj hr hAfter).1
  have hV := (hv.2.1 kappa hk V GV unitV markV HV CV terminalLegs baseV hr).1
  exact trace_stages hM htrace hd.2.2.2.2.2.1 hV ha

/-- Every range of the actual flattened tower is a conservative subobject.
This consumes the SAME saved trace, outer Matrix and terminal row. -/
theorem actual_stages (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one K mu B history P outerF kappa
      V GV unitV markV HV CV terminalLegs baseV traces I S : M.Carrier .set}
    (hv : Valid hM w Q R top D mul e mark H C B history)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hf : Matrix B history zero P outerF)
    (hr : Row history kappa V GV unitV markV HV CV terminalLegs baseV kappa)
    (ht : ConstructionBlockTraces.Family hM w Q R top zero one K mu history outerF kappa traces)
    (hg : ConstructionFlatStages.Graph history outerF kappa V zero traces I S) : Stages V GV unitV S := by
  have hV := (hv.2.1 kappa hs.predecessor_mem V GV unitV markV HV CV terminalLegs baseV hr).1
  intro c A hA
  rcases ((hg.2 c A).mp hA).2 with ⟨_,rfl⟩ | ⟨i,j,_,hValue⟩
  · refine ⟨fun _ h => h,hV.1.1.1,?_,fun _ _ _ _ _ hz _ => hz,fun _ _ _ _ _ hz _ => hz⟩
    intro x y z hx hy hp
    obtain ⟨z0,hz0,hp0⟩ := (hV.1.2.1 x hx).1 y hy
    exact ((hV.1.2.1 x hx).2.1 y z0 z hy hp0 hp) ▸ hz0
  · obtain ⟨code,next,N,W,fromBase,after,J,Domains,E,F,L,Out,Images,hcode,hReal,hImage⟩ := hValue
    exact realized_stages hM hv hs hf hr ((ht.2 i code).mp hcode).2.1 hReal j A hImage

theorem selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained i x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hTimeline : ConstructionFirstAppearance.Timeline hM V I R bottom S)
    (hIndex : ConstructionFirstAppearance.Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x retained) (hi : ConstructionFirstAppearance.NewAt I R S i x) :
    ∃ cell j D T cut next mul pairs cutMul inc GT GNext old inclusion,
      PureKuratowski.PairMember M i cell cells ∧ ConstructionFirstAppearance.Cover I R i j ∧
      PureKuratowski.PairMember M i D S ∧ PureKuratowski.PairMember M j T S ∧
      ConstructionStepCell.Data hM w zero one V GV e D T cell ∧
      ConstructionSelectedCellWords.Retained w zero V GV e D T cell retained cut ∧
      (∀ z, (Project.FirstOrderSemantics.reduct M).mem z next ↔
        (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z T) ∧
      Restricted hM w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion := by
  obtain ⟨cell,j,D,T,cut,hCell,hCover,hD,hT,hData,hSelected⟩ :=
    ConstructionSelectedCellWords.selected hM hTimeline hIndex hCells hNew hGlobal hClosed hx hi
  obtain ⟨next,hNext⟩ := KP.intersection_exists_d (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) retained T
  obtain ⟨mul,pairs,cutMul,inc,GT,GNext,old,inclusion,hResult⟩ :=
    restrict_cell hM hw hz hzw hv hc hJ (hStages j T hT) hRet hData hSelected hNext
  exact ⟨cell,j,D,T,cut,next,mul,pairs,cutMul,inc,GT,GNext,old,inclusion,
    hCell,hCover,hD,hT,hData,hSelected,hNext,hResult⟩

def cellFormula {m : Nat} (w zero D mul e W G unit O : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.neg (Project.Formula.extensionalEq (.bound 13) (.bound e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) (.conj (.neg (Project.Formula.extensionalEq (.bound 12) (.bound e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))) (.conj (ConstructionProbePushoutSyntax.presentation w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14 13 12 11 10 9 8 7 6 5 4 3 2 W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 0 O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (ConstructionProbePath.terminalTable w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 14 9)))))))))))))))))))
 (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 8) (.bound w.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ConstructionRequestCarrier.wellFormed 8 D.succ.succ.succ.succ.succ.succ.succ.succ.succ 7) (.conj (ConstructionMergerRelations.valid 8 D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ 7) (ConstructionMergerPushout.presentation w.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 zero.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5 4 3 W.succ.succ.succ.succ.succ.succ.succ.succ.succ 2 1 G.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ.succ.succ 0))))))))))))))

theorem cellFormula_freeClosed {m : Nat} (w zero D mul e W G unit O : Fin m) :
    (cellFormula w zero D mul e W G unit O).FreeClosed := by
  simp -implicitDefEqProofs [cellFormula,ConstructionProbePath.terminalTable_freeClosed,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ConstructionProbePushoutSyntax.presentation_freeClosed,ConstructionRequestCarrier.wellFormed_freeClosed,ConstructionMergerRelations.valid_freeClosed,ConstructionMergerPushout.presentation_freeClosed]

theorem cellFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul e W G unit O : Fin m) :
    Project.Formula.satisfies env (cellFormula w zero D mul e W G unit O) ↔ Cell hM (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) := by
  simp only [cellFormula,Cell,ConstructionProbePath.terminalTable_semantics hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,ConstructionProbePushoutSyntax.presentation_semantics hM,ConstructionRequestCarrier.wellFormed_semantics hM,ConstructionMergerRelations.valid_semantics hM,ConstructionMergerPushout.presentation_semantics hM]
  rfl

def attachmentFormula {m : Nat} (w zero D mul e T GT : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (cellFormula w.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ 5 4 3 2) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid 5 4 3)) (.conj (ConstructionProbePushoutSyntax.hom D.succ.succ.succ.succ.succ.succ 5 mul.succ.succ.succ.succ.succ.succ 4 e.succ.succ.succ.succ.succ.succ 3 2) (.conj (ConstructionProbeConservativeSyntax.conservative D.succ.succ.succ.succ.succ.succ 5 mul.succ.succ.succ.succ.succ.succ 4 2) (.conj (ConstructionProbePushoutSyntax.hom 5 T.succ.succ.succ.succ.succ.succ 4 GT.succ.succ.succ.succ.succ.succ 3 e.succ.succ.succ.succ.succ.succ 1) (.conj (ConstructionProbePushoutSyntax.hom T.succ.succ.succ.succ.succ.succ 5 GT.succ.succ.succ.succ.succ.succ 4 e.succ.succ.succ.succ.succ.succ 3 0) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph 1 0)) (.conj (ConstructionAttachmentCoefficients.oldFixed 2 1) (ProjectSyntax.encode id (ForcingSupportedNames.range 5 1 T.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem attachmentFormula_freeClosed {m : Nat} (w zero D mul e T GT : Fin m) :
    (attachmentFormula w zero D mul e T GT).FreeClosed := by
  simp -implicitDefEqProofs [attachmentFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,cellFormula_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed]

theorem attachmentFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul e T GT : Fin m) :
    Project.Formula.satisfies env (attachmentFormula w zero D mul e T GT) ↔ Attachment hM (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound T) (env.bound GT) := by
  simp only [attachmentFormula,Attachment,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingConditionGraphs.inverseGraph_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),cellFormula_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM]
  rfl

def restricted {m : Nat} (w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSelectedCellRestriction.baseFormula D mul e cut pairs cutMul inc) (.conj (ConstructionConservativeHull.productGraph D GV mul) (.conj (ConstructionConservativeHull.closure V GV e retained) (.conj (ConstructionConservativeHull.closure V GV e cut) (.conj (ConstructionConservativeHull.closure V GV e next) (.conj (ConstructionConservativeHull.productGraph T GV GT) (.conj (ConstructionConservativeHull.productGraph next GV GNext) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid T GT e)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical T GT e)) (.conj (ConstructionProbeSharedIntersections.conditionalJoins T GT) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid next GNext e)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical next GNext e)) (.conj (ConstructionProbeSharedIntersections.conditionalJoins next GNext) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D old)) (.conj (ConstructionProbePushoutSyntax.hom D T mul GT e e old) (.conj (ConstructionProbeConservativeSyntax.conservative D T mul GT old) (.conj (ConstructionProbePushoutSyntax.hom cut next cutMul GNext e e inc) (.conj (ConstructionProbeConservativeSyntax.conservative cut next cutMul GNext inc) (.conj (ConstructionProbePushoutSyntax.hom next T GNext GT e e inclusion) (.conj (ConstructionProbeConservativeSyntax.conservative next T GNext GT inclusion) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph next inclusion)) (.conj (ConstructionProbePushoutSyntax.isPushout D next T mul GNext GT e e e inc inc inclusion old) (.conj (attachmentFormula w zero cut cutMul e next GNext) (.conj (ConstructionStepCell.typedProduct D mul) (.conj (ConstructionStepCell.typedProduct T GT) (ConstructionStepCell.typedProduct next GNext))))))))))))))))))))))))))

theorem restricted_freeClosed {m : Nat} (w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion : Fin m) :
    (restricted w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion).FreeClosed := by
  simp -implicitDefEqProofs [restricted,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed,attachmentFormula_freeClosed,ConstructionStepCell.typedProduct_freeClosed]

theorem restricted_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion : Fin m) :
    Project.Formula.satisfies env (restricted w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion) ↔ Restricted hM (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound e) (env.bound D) (env.bound T) (env.bound retained) (env.bound cut) (env.bound next) (env.bound mul) (env.bound pairs) (env.bound cutMul) (env.bound inc) (env.bound GT) (env.bound GNext) (env.bound old) (env.bound inclusion) := by
  simp only [restricted,Restricted,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbePushoutSyntax.isPushout_semantics hM,attachmentFormula_semantics hM,ConstructionStepCell.typedProduct_semantics hM]
  rfl

def stages {m : Nat} (V GV e S : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ 1 0)) (ConstructionConservativeHull.closure V.succ.succ GV.succ.succ e.succ.succ 0))))

theorem stages_freeClosed {m : Nat} (V GV e S : Fin m) :
    (stages V GV e S).FreeClosed := by
  simp -implicitDefEqProofs [stages,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionConservativeHull.closure_freeClosed]

theorem stages_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV e S : Fin m) :
    Project.Formula.satisfies env (stages V GV e S) ↔ Stages (env.bound V) (env.bound GV) (env.bound e) (env.bound S) := by
  simp only [stages,Stages,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionConservativeHull.closure_semantics hM]
  rfl

def restrictCellSentence {m : Nat} (w zero one V GV e D T retained cut next cell : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionConservativeHull.closure V GV e T) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionStepCell.data w zero one V GV e D T cell) (.imp (ConstructionSelectedCellWords.retainedFormula w zero V GV e D T cell retained cut) (.imp (ConstructionAttachmentCoefficients.intersection next retained T) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (restricted w.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ T.succ.succ.succ.succ.succ.succ.succ.succ retained.succ.succ.succ.succ.succ.succ.succ.succ cut.succ.succ.succ.succ.succ.succ.succ.succ next.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5 4 3 2 1 0))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionStepCell.data_freeClosed,ConstructionSelectedCellWords.retainedFormula_freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed,restricted_freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty]

theorem restrictCell_models {m : Nat} (w zero one V GV e D T retained cut next cell : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (restrictCellSentence w zero one V GV e D T retained cut next cell)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (restrictCellSentence w zero one V GV e D T retained cut next cell)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionStepCell.data_semantics hM,ConstructionSelectedCellWords.retainedFormula_semantics hM,ConstructionAttachmentCoefficients.intersection_semantics (M := M),restricted_semantics hM,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff]
  exact restrict_cell hM

theorem restrictCell_kernel_certificate {m : Nat} (w zero one V GV e D T retained cut next cell : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (restrictCellSentence w zero one V GV e D T retained cut next cell)) :=
  ModelTransfer.derives (fun _ hM => restrictCell_models w zero one V GV e D T retained cut next cell hM)

def selectedSentence {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (.mem (.bound x) (.bound retained)) (.imp (ConstructionFirstAppearance.newAt I R S i x) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge cells.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13)) (.conj (ConstructionFirstAppearance.cover I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 10)) (.conj (ConstructionStepCell.data w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 13) (.conj (ConstructionSelectedCellWords.retainedFormula w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 13 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9) (.conj (ConstructionAttachmentCoefficients.intersection 8 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10) (restricted w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7 6 5 4 3 2 1 0))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionStepCell.data_freeClosed,ConstructionSelectedCellWords.retainedFormula_freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed,restricted_freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty]

theorem selected_models {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i x : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w zero one V GV e I R bottom S index cells deps retained i x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedSentence w zero one V GV e I R bottom S index cells deps retained i x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),KuratowskiZF.source_edge,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionStepCell.data_semantics hM,ConstructionSelectedCellWords.retainedFormula_semantics hM,ConstructionAttachmentCoefficients.intersection_semantics (M := M),restricted_semantics hM,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff]
  exact selected hM

theorem selected_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i x : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedSentence w zero one V GV e I R bottom S index cells deps retained i x)) :=
  ModelTransfer.derives (fun _ hM => selected_models w zero one V GV e I R bottom S index cells deps retained i x hM)

def actualStagesSentence {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerValidity.valid w Q R top D mul e mark H C B history) (.imp (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.imp (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V GV unitV markV HV CV terminalLegs baseV kappa) (.imp (ConstructionBlockTraces.family w Q R top zero one K mu history outerF kappa traces) (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (stages V GV unitV S)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionTowerValidity.valid_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionFlatStages.graph_freeClosed,stages_freeClosed,Project.Formula.isSuccessor]

theorem actualStages_models {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (actualStagesSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (actualStagesSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,ConstructionTowerValidity.valid_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionFlatStages.graph_semantics hM,stages_semantics hM,Project.Formula.satisfies_isSuccessor_iff]
  exact actual_stages hM

theorem actualStages_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (actualStagesSentence w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S)) :=
  ModelTransfer.derives (fun _ hM => actualStages_models w Q R top D mul e mark H C zero one K mu B history P outerF kappa V GV unitV markV HV CV terminalLegs baseV traces I S hM)

theorem selected_actual (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hValid : Valid hM w Q values top baseN baseMul baseUnit mark H C B history)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B kappa)
    (hMatrix : Matrix B history zero P outerF)
    (hRow : Row history kappa V GV e markV HV CV terminalLegs baseV kappa)
    (hFamily : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hGraph : ConstructionFlatStages.Graph history outerF kappa V zero traces I S) (hRet : Closure V GV e retained)
    (hTimeline : ConstructionFirstAppearance.Timeline hM V I R bottom S)
    (hIndex : ConstructionFirstAppearance.Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x retained) (hi : ConstructionFirstAppearance.NewAt I R S i x) :
    ∃ cell j D T cut next mul pairs cutMul inc GT GNext old inclusion,
      PureKuratowski.PairMember M i cell cells ∧ ConstructionFirstAppearance.Cover I R i j ∧
      PureKuratowski.PairMember M i D S ∧ PureKuratowski.PairMember M j T S ∧
      ConstructionStepCell.Data hM w zero one V GV e D T cell ∧
      ConstructionSelectedCellWords.Retained w zero V GV e D T cell retained cut ∧
      (∀ z, (Project.FirstOrderSemantics.reduct M).mem z next ↔
        (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z T) ∧
      Restricted hM w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion := by
  exact selected hM hw hz hzw hv hc hJ (actual_stages hM hValid hB hMatrix hRow hFamily hGraph)
    hRet hTimeline hIndex hCells hNew hGlobal hClosed hx hi

def selectedActualSentence {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionTowerValidity.valid w Q values top baseN baseMul baseUnit mark H C B history) (.imp (Project.Formula.isSuccessor (.bound B) (.bound kappa)) (.imp (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V GV e markV HV CV terminalLegs baseV kappa) (.imp (ConstructionBlockTraces.family w Q values top zero one K mu history outerF kappa traces) (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (.mem (.bound x) (.bound retained)) (.imp (ConstructionFirstAppearance.newAt I R S i x) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge cells.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13)) (.conj (ConstructionFirstAppearance.cover I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 10)) (.conj (ConstructionStepCell.data w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 13) (.conj (ConstructionSelectedCellWords.retainedFormula w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 13 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9) (.conj (ConstructionAttachmentCoefficients.intersection 8 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10) (restricted w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionTowerValidity.valid_freeClosed,Project.Formula.isSuccessor,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionBlockTraces.family_freeClosed,ConstructionFlatStages.graph_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionStepCell.data_freeClosed,ConstructionSelectedCellWords.retainedFormula_freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed,restricted_freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty]

theorem selectedActual_models {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedActualSentence w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedActualSentence w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),KuratowskiZF.source_edge,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionTowerValidity.valid_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionBlockTraces.family_semantics hM,ConstructionFlatStages.graph_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionStepCell.data_semantics hM,ConstructionSelectedCellWords.retainedFormula_semantics hM,ConstructionAttachmentCoefficients.intersection_semantics (M := M),restricted_semantics hM,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff]
  exact selected_actual hM

theorem selectedActual_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedActualSentence w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces)) :=
  ModelTransfer.derives (fun _ hM => selectedActual_models w zero one V GV e I R bottom S index cells deps retained i x Q values top baseN baseMul baseUnit mark H C K mu B history P outerF kappa markV HV CV terminalLegs baseV traces hM)

end PPAC.Migration.ConstructionCellRestriction
