/- Pinned CompleteRounds.Saturation.step / succIso / map_succ.
Read the actual current row, execute the SAME selected complete round,
compose ALL old incoming legs and the original base inclusion, and append
the new actual row using the existing full Valid-preservation theorem. -/
import PPAC.Migration.ConstructionSaturationStep

namespace PPAC.Migration.ConstructionSaturationSuccessor
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Field Chart Charts)
open ConstructionTowerValidity (Valid row_field)
open ConstructionRoundFields (ObjectFields MapFields Profiles)
open ConstructionTowerSuccessor (Graph SelfExtension)
open ConstructionDirectedWeightData (WeightFamily)
open ConstructionProbeMappedPath (NodeMap)
open ForcingConditionGraphs (FunctionOn)
open ForcingSupportSize (MapsTo Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu J S prev output : M.Carrier .set) : Prop :=
  ∃ Domains N mulN eN markN HN CN L f next raw Requests W G unitW markW HW CW O Out baseW identity NewDomains NewOut,
    Chart 0 J S Domains ∧ Row S prev N mulN eN markN HN CN L f prev ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev ∧
    (Project.FirstOrderSemantics.reduct M).SuccessorOf next J ∧
    ConstructionSaturationStep.Picked hM w Q R top N mulN eN markN HN CN zero one K mu raw ∧
    ConstructionSaturationStep.Candidate hM w Q R top N mulN eN markN HN CN zero one K mu raw ∧
    ConstructionRoundSelection.Pack W G unitW markW HW CW O Requests zero raw ∧
    Graph J Domains L O W Out ∧ WeightFamily J Domains W Out ∧ ConstructionTowerSuccessor.SuccessorEquation J L N O Out ∧ NodeMap f O baseW ∧
    MapFields hM w Q D W mul G e unitW mark markW H C HW CW baseW ∧
    SelfExtension J next Domains Out W identity NewDomains NewOut ∧
    ConstructionRoundSelection.Pack W G unitW markW HW CW NewOut baseW J output

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top D mul e mark H C zero one K mu J S prev x y : M.Carrier .set}
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hx : Value hM w Q R top D mul e mark H C zero one K mu J S prev x)
    (hy : Value hM w Q R top D mul e mark H C zero one K mu J S prev y) : x = y := by
  obtain ⟨Domains,N,mulN,eN,markN,HN,CN,L,f,next,raw,Requests,W,G,unitW,markW,HW,CW,O,Out,baseW,
    identity,NewDomains,NewOut,hChart,hRow,hSucc,hNext,hPicked,_,hRaw,hGraph,hOut,_,hBase,hMap,hSelf,hPack⟩ := hx
  obtain ⟨Domains',N',mulN',eN',markN',HN',CN',L',f',next',raw',Requests',W',G',unitW',markW',HW',CW',O',Out',baseW',
    identity',NewDomains',NewOut',hChart',hRow',_,hNext',hPicked',_,hRaw',hGraph',hOut',_,hBase',hMap',hSelf',hPack'⟩ := hy
  have eq := ConstructionTowerHistory.chart_unique hM 0 hChart' hChart
  subst Domains'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionTowerHistory.row_unique hV.1.1 hRow hRow'
  have eq := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun z => (hNext' z).trans (hNext z).symm)
  subst next'
  have eq := ConstructionSaturationStep.picked_unique hM hOrder hPicked' hPicked
  subst raw'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_⟩ := ConstructionRoundSelection.pack_injective hRaw hRaw'
  have hp : (Project.FirstOrderSemantics.reduct M).mem prev J := by
    obtain ⟨code,hcode,_⟩ := hRow
    exact ForcingConditionGraphs.function_input hV.1.1 hcode
  obtain ⟨_,_,_,domain,id,hDomain,hL,_,_⟩ := hV.2.1 prev hp N mulN eN markN HN CN L f hRow
  have eqDomain := (ModelTransfer.extensionality hM).eq_of_same_members domain J
    (fun z => (hDomain z).trans (hSucc z).symm)
  subst domain
  have rel {A} (hA : FunctionOn J A) :
      (Project.FirstOrderSemantics.reduct M).IsSetRelation (KuratowskiZF.interpretation hM) A := by
    intro p hp
    obtain ⟨i,v,_,hc⟩ := hA.1 p hp
    exact ⟨i,v,hc⟩
  have eqOut : Out = Out' := by
    apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM) (rel hOut.1) (rel hOut'.1)
    intro i z
    constructor
    · intro hz
      obtain ⟨z',hz',_⟩ := hOut'.1.2 i ((hGraph i z).mp hz).1
      have eq := ConstructionTowerSuccessor.value_unique hM hChart.1 hL ((hGraph i z).mp hz).2 ((hGraph' i z').mp hz').2
      exact eq.symm ▸ hz'
    · intro hz
      obtain ⟨z',hz',_⟩ := hOut.1.2 i ((hGraph' i z).mp hz).1
      have eq := ConstructionTowerSuccessor.value_unique hM hChart.1 hL ((hGraph' i z).mp hz).2 ((hGraph i z').mp hz').2
      exact eq.symm ▸ hz'
  subst Out'
  have eqBase : baseW = baseW' :=
    Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
      ((ForcingSupportSize.native_mapsTo hM D W baseW).mp hMap.1.1.1).1.1
      ((ForcingSupportSize.native_mapsTo hM D W baseW').mp hMap'.1.1.1).1.1
      (fun a b => (hBase a b).trans (hBase' a b).symm)
  subst baseW'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionTowerCanonicalLimit.self_unique hM hSelf hSelf'
  exact ConstructionTowerCanonicalLimit.packet_unique hM hPack hPack'

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu J S prev : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hKSmall : Small K mu)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf J prev)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hSmall : ConstructionTowerCardinality.AllSmall J S mu) :
    ∃ output, Value hM w Q R top D mul e mark H C zero one K mu J S prev output ∧
      (∀ other, Value hM w Q R top D mul e mark H C zero one K mu J S prev other → other = output) ∧
      ∃ next S', ConstructionTowerAppend.Append J S output next S' ∧
        Valid hM w Q R top D mul e mark H C next S' ∧
        ConstructionTowerCardinality.AllSmall next S' mu := by
  have hp := hSucc.predecessor_mem
  obtain ⟨N,mulN,eN,markN,HN,CN,L,f,hRow⟩ := hV.1.2 prev hp
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,_⟩ :=
    ConstructionTowerDiagram.exists_data hM zero hJ hV
  obtain ⟨hObjN,hBase,hBaseProfiles,hL,hStable,hFull,hProfiles,hNatural,_⟩ :=
    ConstructionTowerHistorySuccessor.parents hM hV hSucc hCharts hE hF hRow
  have hNsize := hSmall prev hp N (row_field 0 hRow)
  obtain ⟨raw,hPicked,hCandidate,_⟩ := ConstructionSaturationStep.exists_step hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObjN hz hzw hK hmu hpow hNsize hKSmall
  have hCandidateCopy := hCandidate
  obtain ⟨Requests,W,G,unitW,markW,HW,CW,O,hRaw,hCarrier,hObjW,hO,hOProfiles,hWsize,hProbes,hMergers⟩ := hCandidateCopy
  obtain ⟨baseW,hBaseMap,hBaseGraph⟩ := ConstructionProbeMappedPath.exists_node_map hM hBase.1.1.1 hO.1.1.1
  have hBaseFields := ConstructionRoundFields.map_comp hM hObjN.1 hObjW.1 hBase hO hBaseMap hBaseGraph
  have hBaseProfilesW := ConstructionRoundFields.profiles_comp hBaseGraph hBaseProfiles hOProfiles
  obtain ⟨Out,hGraph,hOut,hComp,_⟩ := ConstructionTowerSuccessor.exists_family hM hCharts.1.1 hL hO.1.1.1
  have hStableW := ConstructionTowerSuccessor.stable_comp hL hStable hComp
  have hFullW := ConstructionTowerSuccessor.full_legs_comp hM hObjN.1 hObjW.1 hL hOut hComp hFull hO
  have hProfilesW := ConstructionTowerSuccessor.profile_legs_comp hL hComp hProfiles hOProfiles
  have hNaturalW := ConstructionTowerSuccessor.base_natural_comp hL.1 hComp hNatural hBaseGraph
  obtain ⟨next,hNext⟩ := KP.exists_successor (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) J
  have hNextOrd := KP.successor_isOrdinal (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) hJ hNext
  obtain ⟨identity,NewDomains,NewOut,hSelf⟩ :=
    ConstructionTowerSuccessor.exists_self_extension hM hJ hNextOrd hNext hCharts.1.1 hOut
  obtain ⟨output,hPack⟩ := ConstructionRoundSelection.pack_exists hM W G unitW markW HW CW NewOut baseW J
  have hValue : Value hM w Q R top D mul e mark H C zero one K mu J S prev output :=
    ⟨Domains,N,mulN,eN,markN,HN,CN,L,f,next,raw,Requests,W,G,unitW,markW,HW,CW,O,Out,baseW,
      identity,NewDomains,NewOut,hCharts.1,hRow,hSucc,hNext,hPicked,hCandidate,hRaw,hGraph,hOut,ConstructionTowerSuccessor.successor_equation hM hCharts.1.1 hOut hComp hO.1.1.1,hBaseGraph,hBaseFields,hSelf,hPack⟩
  obtain ⟨next',S',hAppend⟩ := ConstructionTowerAppend.exists_append hM hJ hV.1.1 output
  have eq := (ModelTransfer.extensionality hM).eq_of_same_members next' next
    (fun z => (hAppend.1 z).trans (hNext z).symm)
  subst next'
  have hValid := ConstructionTowerAppend.preserves hM hJ hV hR (ConstructionRealCuts.principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hCoordinates⟩) hTop)
    hCharts hE hF hObjW hBaseFields hBaseProfilesW hOut hStableW hFullW hProfilesW hNaturalW hSelf hPack hAppend
  have hSmall' : ConstructionTowerCardinality.AllSmall next S' mu := by
    intro i _ A hA
    obtain ⟨A',m,v,a,V,T,L',f',time,⟨code,hCode,hRowPack⟩,he⟩ := hA
    change A = A' at he
    subst A'
    rcases (hAppend.2.2 i code).mp hCode with hOld | ⟨rfl,rfl⟩
    · have hiJ := ForcingConditionGraphs.function_input hV.1.1 hOld
      exact hSmall i hiJ A ⟨A,m,v,a,V,T,L',f',time,⟨code,hOld,hRowPack⟩,rfl⟩
    · obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := ConstructionRoundSelection.pack_injective hPack hRowPack
      exact hWsize
  exact ⟨output,hValue,fun other hOther => value_unique hM hOrder hV hOther hValue,
    next,S',hAppend,hValid,hSmall'⟩

def value {m : Nat} (w Q R top D mul e mark H C zero one K mu J S prev output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionTowerHistory.chart 0
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (23 : Fin (m+24))) (.conj (ConstructionTowerHistory.row
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  prev.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (22 : Fin (m+24)) (21 : Fin (m+24)) (20 : Fin (m+24)) (19 : Fin (m+24)) (18 : Fin (m+24)) (17 : Fin
  (m+24)) (16 : Fin (m+24)) (15 : Fin (m+24))
  prev.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (Project.Formula.isSuccessor (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.bound
  prev.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (Project.Formula.isSuccessor (.bound (14 : Fin (m+24))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ConstructionSaturationStep.picked
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (22 : Fin (m+24)) (21 : Fin (m+24)) (20 : Fin (m+24)) (19 : Fin (m+24)) (18 : Fin (m+24)) (17 : Fin
  (m+24))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (13 : Fin (m+24))) (.conj (ConstructionSaturationStep.candidate
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (22 : Fin (m+24)) (21 : Fin (m+24)) (20 : Fin (m+24)) (19 : Fin (m+24)) (18 : Fin (m+24)) (17 : Fin
  (m+24))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (13 : Fin (m+24))) (.conj (ConstructionRoundSelection.pack (11 : Fin (m+24)) (10 : Fin (m+24)) (9 : Fin
  (m+24)) (8 : Fin (m+24)) (7 : Fin (m+24)) (6 : Fin (m+24)) (5 : Fin (m+24)) (12 : Fin (m+24))
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (13 : Fin (m+24))) (.conj (ConstructionTowerSuccessor.graph
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (23 : Fin (m+24)) (16 : Fin (m+24)) (5 : Fin (m+24)) (11 : Fin (m+24)) (4 : Fin (m+24))) (.conj
  (ConstructionDirectedWeightData.weightFamily
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (23 : Fin (m+24)) (11 : Fin (m+24)) (4 : Fin (m+24))) (.conj (ConstructionTowerSuccessor.successorEquation
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (16 : Fin (m+24)) (22 : Fin (m+24)) (5 : Fin (m+24)) (4 : Fin (m+24))) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap (15 : Fin (m+24)) (5 : Fin (m+24)) (3 : Fin (m+24))) (.conj
  (ConstructionRoundStepSyntax.mapFields
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (11 : Fin (m+24))
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (10 : Fin (m+24))
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (9 : Fin (m+24))
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (8 : Fin (m+24))
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (7 : Fin (m+24)) (6 : Fin (m+24)) (3 : Fin (m+24))) (.conj (ConstructionTowerSuccessor.selfExtension
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (14 : Fin (m+24)) (23 : Fin (m+24)) (4 : Fin (m+24)) (11 : Fin (m+24)) (2 : Fin (m+24)) (1 : Fin (m+24))
  (0 : Fin (m+24))) (ConstructionRoundSelection.pack (11 : Fin (m+24)) (10 : Fin (m+24)) (9 : Fin (m+24)) (8
  : Fin (m+24)) (7 : Fin (m+24)) (6 : Fin (m+24)) (0 : Fin (m+24)) (3 : Fin (m+24))
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  output.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))))))))))

theorem value_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu J S prev output : Fin m) :
    (value w Q R top D mul e mark H C zero one K mu J S prev output).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerHistory.row_freeClosed,Project.Formula.isSuccessor,ConstructionSaturationStep.picked_freeClosed,ConstructionSaturationStep.candidate_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionTowerSuccessor.graph_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionTowerSuccessor.successorEquation_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionTowerSuccessor.selfExtension_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu J S prev output : Fin m) :
    Project.Formula.satisfies env (value w Q R top D mul e mark H C zero one K mu J S prev output) ↔ Value hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound J) (env.bound S) (env.bound prev) (env.bound output) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    ConstructionTowerHistory.chart_semantics hM 0,ConstructionTowerHistory.row_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ConstructionSaturationStep.picked_semantics hM,ConstructionSaturationStep.candidate_semantics hM,ConstructionRoundSelection.pack_semantics hM,ConstructionTowerSuccessor.graph_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionTowerSuccessor.successorEquation_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionTowerSuccessor.selfExtension_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 18 (.imp (Project.Formula.isOmega (.bound (0 : Fin 18))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 18) (1 : Fin 18)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 18) (1 : Fin 18) (2 : Fin 18)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 18) (12 : Fin
    18) (11 : Fin 18) (11 : Fin 18)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 18))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 18) (1 : Fin 18) (12 : Fin 18) (3 : Fin 18)) (.imp
    (Project.Formula.isEmpty (.bound (10 : Fin 18))) (.imp (.mem (.bound (10 : Fin 18)) (.bound (0 : Fin
    18))) (.imp (.existsE (.mem (.bound (0 : Fin 19)) (.bound (13 : Fin 18).succ))) (.imp
    (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound (0 : Fin 18)) (.bound (14 :
    Fin 18))) (.imp (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 :
    Fin 18)) (.bound (14 : Fin 18)) (.bound (0 : Fin 18))) (.imp (ProjectSyntax.encode id
    (ForcingSupportSize.small (13 : Fin 18) (14 : Fin 18))) (.imp (Project.Formula.isOrdinal (.bound (15 :
    Fin 18))) (.imp (Project.Formula.isSuccessor (.bound (15 : Fin 18)) (.bound (17 : Fin 18))) (.imp
    (ConstructionTowerValidity.valid (0 : Fin 18) (1 : Fin 18) (2 : Fin 18) (3 : Fin 18) (4 : Fin 18) (5 :
    Fin 18) (6 : Fin 18) (7 : Fin 18) (8 : Fin 18) (9 : Fin 18) (15 : Fin 18) (16 : Fin 18)) (.imp
    (ConstructionTowerCardinality.allSmall (15 : Fin 18) (16 : Fin 18) (14 : Fin 18)) (.existsE (.conj
    (value (0 : Fin 18).succ (1 : Fin 18).succ (2 : Fin 18).succ (3 : Fin 18).succ (4 : Fin 18).succ (5 :
    Fin 18).succ (6 : Fin 18).succ (7 : Fin 18).succ (8 : Fin 18).succ (9 : Fin 18).succ (10 : Fin 18).succ
    (11 : Fin 18).succ (13 : Fin 18).succ (14 : Fin 18).succ (15 : Fin 18).succ (16 : Fin 18).succ (17 : Fin
    18).succ (0 : Fin 19)) (.conj (.forallE (.imp (value (0 : Fin 18).succ.succ (1 : Fin 18).succ.succ (2 :
    Fin 18).succ.succ (3 : Fin 18).succ.succ (4 : Fin 18).succ.succ (5 : Fin 18).succ.succ (6 : Fin
    18).succ.succ (7 : Fin 18).succ.succ (8 : Fin 18).succ.succ (9 : Fin 18).succ.succ (10 : Fin
    18).succ.succ (11 : Fin 18).succ.succ (13 : Fin 18).succ.succ (14 : Fin 18).succ.succ (15 : Fin
    18).succ.succ (16 : Fin 18).succ.succ (17 : Fin 18).succ.succ (0 : Fin 20))
    (Project.Formula.extensionalEq (.bound (0 : Fin 20)) (.bound (1 : Fin 20))))) (.existsE (.existsE (.conj
    (ConstructionTowerAppend.append (15 : Fin 18).succ.succ.succ (16 : Fin 18).succ.succ.succ (0 : Fin
    19).succ.succ (1 : Fin 21) (0 : Fin 21)) (.conj (ConstructionTowerValidity.valid (0 : Fin
    18).succ.succ.succ (1 : Fin 18).succ.succ.succ (2 : Fin 18).succ.succ.succ (3 : Fin 18).succ.succ.succ
    (4 : Fin 18).succ.succ.succ (5 : Fin 18).succ.succ.succ (6 : Fin 18).succ.succ.succ (7 : Fin
    18).succ.succ.succ (8 : Fin 18).succ.succ.succ (9 : Fin 18).succ.succ.succ (1 : Fin 21) (0 : Fin 21))
    (ConstructionTowerCardinality.allSmall (1 : Fin 21) (0 : Fin 21) (14 : Fin
    18).succ.succ.succ)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      Project.Formula.isOrdinal,Project.Formula.isSuccessor,ConstructionTowerValidity.valid_freeClosed,
      ConstructionTowerCardinality.allSmall_freeClosed,value_freeClosed,Project.Formula.extensionalEq,
      ConstructionTowerAppend.append_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isSuccessor_iff,
    ConstructionTowerValidity.valid_semantics hM,ConstructionTowerCardinality.allSmall_semantics hM,
    value_semantics hM,ConstructionTowerAppend.append_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hz hzw hK hmu hpow hKSmall hJ hSucc hV hSmall =>
    exists_value hM hOrder hChoice hw hQ hR hCoordinates hone hTop hz hzw hK hmu hpow hKSmall hJ hSucc hV hSmall

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)



end PPAC.Migration.ConstructionSaturationSuccessor
