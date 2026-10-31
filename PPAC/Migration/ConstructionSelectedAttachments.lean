/- Pinned request_rangeAttachment and blockStage_step: consume the SAME
SelectedAt record and the actual terminal incoming/composite/range families.
No new tower, selected raw, or final legs are assumed or constructed elsewhere. -/
import PPAC.Migration.ConstructionMappedProbe
import PPAC.Migration.ConstructionMappedMerger
import PPAC.Migration.ConstructionActualBlocks

namespace PPAC.Migration.ConstructionSelectedAttachments
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Chart)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionTowerMapSucc (SelectedAt)
open ConstructionRoundFields (ObjectFields MapFields)
open ConstructionProbePushout (Hom)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionRequestSchedule (ProbeCode MergerCode)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (FunctionOn)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ProbeAt (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero D mul e a b d node W unit G O gen V GV unitV f g S R : M.Carrier .set) : Prop :=
  ∃ basePairs mulN inc baseInv fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding,
      ConstructionRangeObject.Data w zero D V mul GV e unitV f S basePairs mulN inc baseInv ∧
      ConstructionMappedProbe.Data hM w zero a b d node W unit G O gen S mulN unitV f V GV unitV g R
        fa fb fd mapped factorN terminalN targetN SN CN projectionN IN actN EN WN unitN GN KN PN ON genN H inv embedding

def MergerAt (w n zero D mul e P W G unit O roots V GV unitV f g S R : M.Carrier .set) : Prop :=
  ∃ basePairs mulN inc baseInv PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding,
      ConstructionRangeObject.Data w zero D V mul GV e unitV f S basePairs mulN inc baseInv ∧
      ConstructionMappedMerger.Data w n zero P W G unit O roots S mulN unitV f V GV unitV g R
        PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding

/-- Preserve the actual original request map and branch; add the constructed
range attachment without erasing the source request or raw root field. -/
def Attached (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R : M.Carrier .set) : Prop :=
  (∃ a b node fa fb mapped, ProbeCode zero a b node request ∧
    PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧ NodeMap node f mapped ∧
    ProbeAt hM w zero N mulN eN fa fb markN mapped W unit G O roots V GV unitV leg nextLeg S R) ∨
  ∃ n P PN, MergerCode one n P request ∧ ConstructionMergerPrescriptionMap.Graph P f PN ∧
    MergerAt w n zero N mulN eN PN W G unit O roots V GV unitV leg nextLeg S R

theorem from_provenance (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one request D mul N mulN eN markN f W G unit markW O base roots V GV unitV leg nextLeg S R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hne : zero ≠ one)
    (hm : LeftCancelMonoid N mulN eN) (hJ : ConditionalJoins N mulN)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem markN N) (hmarkne : markN ≠ eN)
    (hmW : LeftCancelMonoid W G unit) (hO : MapsTo N W O)
    (hDone : ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots)
    (hSource : ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unit O roots)
    (hv : LeftCancelMonoid V GV unitV) (hc : Conical V GV unitV) (hJV : ConditionalJoins V GV)
    (hf : Hom N V mulN GV eN unitV leg) (hCons : Conservative N V mulN GV leg) (hRange : Range N leg S)
    (hg : Hom W V G GV unit unitV nextLeg) (hInj : Injection W V nextLeg)
    (hOld : NodeMap O nextLeg leg) (hTerminalRange : Range W nextLeg R) :
    Attached hM w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R := by
  rcases hSource with ⟨a,b,node,fa,fb,mapped,hCode,hfa,hfb,hMap,hSource⟩ | ⟨n,P,PN,hCode,hMap,hSource⟩
  · exact Or.inl ⟨a,b,node,fa,fb,mapped,hCode,hfa,hfb,hMap,
      ConstructionMappedProbe.construction hM hw hz hzw hm hJ hmark hmarkne hO hSource hv hc hJV hf hCons hRange hg hInj hOld hTerminalRange⟩
  · rcases hDone with ⟨a,b,node,hProbe,_⟩ | ⟨n',P',hCode',hDone,_⟩
    · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hProbe hCode)
    · obtain ⟨en,ep⟩ := ConstructionRequestSchedule.merger_code_injective hCode hCode'
      subst n'; subst P'
      have hValid := hSource.2.1
      obtain ⟨C,L,projection,A,T,B,hA⟩ := ConstructionExecutedCellPresentation.merger hM hw hz hzw hm hO hDone.1 hSource
      exact Or.inr ⟨n,P,PN,hCode,hMap,
        ConstructionMappedMerger.construction hM hw hz hzw hA hValid hmW hJ hv hc hJV hf hCons hRange hg hInj hOld hTerminalRange⟩

/-- Every original SelectedAt field remains unchanged. The two additional
legs are taken from the SAME already constructed Out family. -/
def At (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1 : M.Carrier .set) : Prop :=
  ∃ request N mulN eN markN HN CN K f W G unitW markW HL LC NewOut base O roots leg nextLeg,
    PureKuratowski.PairMember M i request Schedule ∧
    Row history i N mulN eN markN HN CN K f i ∧
    Row history j W G unitW markW HL LC NewOut base j ∧
    ConstructionRoundSelection.Picked hM w Q R top zero one D mul e mark H C
      N mulN eN markN HN CN f request raw ∧
    ConstructionRoundSelection.Pack W G unitW markW HL LC O base roots raw ∧
    ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f
      W G unitW markW HL LC O base ∧
    ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots ∧
    Product F i j O ∧ ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unitW O roots
    ∧ PureKuratowski.PairMember M i leg Out ∧ PureKuratowski.PairMember M j nextLeg Out ∧ Range N leg A0 ∧ Range W nextLeg A1 ∧
    Attached hM w zero one request N mulN eN markN f W G unitW O roots V GV unitV leg nextLeg A0 A1

theorem of_selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F E Domains
      last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1 : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hMatrix : ConstructionTowerTransitions.Matrix J history zero P F)
    (hChart : Chart 0 J history Domains)
    (hLast : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last)
    (hRowLast : Row history last T GT eT markT HT CT L baseT last)
    (hV : ObjectFields hM w Q R top V GV unitV markV HV CV)
    (hAfter : MapFields hM w Q T V GT GV eT unitV markT markV HT CT HV CV after)
    (hBlock : ConstructionBlockStages.Result J E Domains F L after V Out Images)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i)
    (hSelected : SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw)
    (hA0 : PureKuratowski.PairMember M i A0 Images) (hA1 : PureKuratowski.PairMember M j A1 Images) :
    At hM w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1 := by
  have hv := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  have hl := hLast.predecessor_mem
  have hStageLast := hv.2.1 last hl T GT eT markT HT CT L baseT hRowLast
  obtain ⟨next,identity,hNext,hFn,_,_⟩ := hStageLast.2.2.2
  have en : next = J := (ModelTransfer.extensionality hM).eq_of_same_members next J (fun x => (hNext x).trans (hLast x).symm)
  subst next
  obtain ⟨hw,_,_,_,hone,_,_,hz,hzw,_,_,_⟩ := hCtx
  obtain ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hRequest,hRowI,hRowJ,hPicked,hRaw,hStep,hDone,hProd,hSource⟩ := hSelected
  have hObj := (hv.2.1 i hi N mulN eN markN HN CN K f hRowI).1
  have hBefore : ConstructionTowerTransitions.Before i j := Or.inl hs.predecessor_mem
  have hDi := (hChart.2 i N).mpr ⟨hi,ConstructionTowerValidity.row_field 0 hRowI⟩
  have hDj := (hChart.2 j W).mpr ⟨hj,ConstructionTowerValidity.row_field 0 hRowJ⟩
  obtain ⟨li,hli,_⟩ := hFn.2 i hi
  obtain ⟨lj,hlj,_⟩ := hFn.2 j hj
  have hMi := (hv.2.2.1 i last N mulN eN markN HN CN K f T GT eT markT HT CT L baseT li hi hl
    (ConstructionActualBlocks.before_last hM hLast hi) hRowI hRowLast hli).1
  have hMj := (hv.2.2.1 j last W G unitW markW HL LC NewOut base T GT eT markT HT CT L baseT lj hj hl
    (ConstructionActualBlocks.before_last hM hLast hj) hRowJ hRowLast hlj).1
  have hWeights := hBlock.2.1
  have hComposites := hBlock.2.2.1
  have hRanges := hBlock.2.2.2.2.1
  obtain ⟨leg,hleg,_⟩ := hWeights.1.2 i hi
  obtain ⟨nextLeg,hnextLeg,_⟩ := hWeights.1.2 j hj
  have hCi := hComposites i li leg hi hli hleg
  have hCj := hComposites j lj nextLeg hj hlj hnextLeg
  have hMapi := ConstructionRoundFields.map_comp hM hStageLast.1.1 hV.1 hMi hAfter (hWeights.2 i N leg hi hDi hleg) hCi
  have hMapj := ConstructionRoundFields.map_comp hM hStageLast.1.1 hV.1 hMj hAfter (hWeights.2 j W nextLeg hj hDj hnextLeg) hCj
  have hOj := (ConstructionTowerTransitions.matrix_at hv.1 hMatrix hi hj hBefore (ConstructionTowerValidity.row_field 6 hRowJ)).mp hProd
  have hInner := hv.2.2.2.1 i j last NewOut L O lj li hi hj hl hBefore
    (ConstructionActualBlocks.before_last hM hLast hj) (ConstructionTowerValidity.row_field 6 hRowJ)
    (ConstructionTowerValidity.row_field 6 hRowLast) hOj hlj hli
  have hOld := ConstructionRoundFields.node_comp hCj hInner hCi
  have hR0 := ConstructionBlockStages.range_at hChart.1 hWeights.1 hRanges hDi hleg hA0
  have hR1 := ConstructionBlockStages.range_at hChart.1 hWeights.1 hRanges hDj hnextLeg hA1
  have hAttached := from_provenance hM hw hz hzw (ConstructionRequestSchedule.zero_ne_one hz hone)
    hObj.1 hObj.2.2.1 hObj.2.2.2.1 hObj.2.2.2.2.1 hStep.1.1.1 hStep.1.2.1.1.1.1 hDone hSource
    hV.1 hV.2.1 hV.2.2.1 ⟨hMapi.1.1.1,hMapi.2.2.1,hMapi.2.1⟩ hMapi.1 hR0
    ⟨hMapj.1.1.1,hMapj.2.2.1,hMapj.2.1⟩ hMapj.1.1 hOld hR1
  exact ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,leg,nextLeg,
    hRequest,hRowI,hRowJ,hPicked,hRaw,hStep,hDone,hProd,hSource,hleg,hnextLeg,hR0,hR1,hAttached⟩

theorem map_succ (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F E Domains
      last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1 : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hMatrix : ConstructionTowerTransitions.Matrix J history zero P F)
    (hChart : Chart 0 J history Domains)
    (hLast : (Project.FirstOrderSemantics.reduct M).SuccessorOf J last)
    (hRowLast : Row history last T GT eT markT HT CT L baseT last)
    (hV : ObjectFields hM w Q R top V GV unitV markV HV CV)
    (hAfter : MapFields hM w Q T V GT GV eT unitV markT markV HT CT HV CV after)
    (hBlock : ConstructionBlockStages.Result J E Domains F L after V Out Images)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i)
    (hA0 : PureKuratowski.PairMember M i A0 Images) (hA1 : PureKuratowski.PairMember M j A1 Images) :
    ∃ raw, SelectedAt hM w Q R top D mul e mark H C zero one Schedule history F i j raw ∧
      At hM w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1 := by
  obtain ⟨raw,hSelected⟩ := ConstructionTowerMapSucc.map_succ_selected hM hCtx hRec hMatrix hi hj hs
  exact ⟨raw,hSelected,of_selected hM hCtx hRec hMatrix hChart hLast hRowLast hV hAfter hBlock hi hj hs hSelected hA0 hA1⟩

def probeAt {m : Nat} (w zero D mul e a b d node W unit G O gen V GV unitV f g S R : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRangeObject.data
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  26 25 24 23) (ConstructionMappedProbe.data
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  b.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  d.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  node.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  gen.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  25
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  g.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))))))

theorem probeAt_freeClosed {m : Nat} (w zero D mul e a b d node W unit G O gen V GV unitV f g S R : Fin m) :
    (probeAt w zero D mul e a b d node W unit G O gen V GV unitV f g S R).FreeClosed := by
  simp -implicitDefEqProofs [probeAt,Definitional.Formula.FreeClosed,ConstructionRangeObject.data_freeClosed,ConstructionMappedProbe.data_freeClosed]

theorem probeAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul e a b d node W unit G O gen V GV unitV f g S R : Fin m) :
    Project.Formula.satisfies env (probeAt w zero D mul e a b d node W unit G O gen V GV unitV f g S R) ↔ ProbeAt hM (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound a) (env.bound b) (env.bound d) (env.bound node) (env.bound W) (env.bound unit) (env.bound G) (env.bound O) (env.bound gen) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound f) (env.bound g) (env.bound S) (env.bound R) := by
  simp only [probeAt,ProbeAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionRangeObject.data_semantics hM,ConstructionMappedProbe.data_semantics hM]
  rfl

def mergerAt {m : Nat} (w n zero D mul e P W G unit O roots V GV unitV f g S R : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ConstructionRangeObject.data
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 18 17 16 15)
  (ConstructionMappedMerger.data
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  roots.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 17
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  g.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14 13 12 11 10 9
  8 7 6 5 4 3 2 1 0)))))))))))))))))))))

theorem mergerAt_freeClosed {m : Nat} (w n zero D mul e P W G unit O roots V GV unitV f g S R : Fin m) :
    (mergerAt w n zero D mul e P W G unit O roots V GV unitV f g S R).FreeClosed := by
  simp -implicitDefEqProofs [mergerAt,Definitional.Formula.FreeClosed,ConstructionRangeObject.data_freeClosed,ConstructionMappedMerger.data_freeClosed]

theorem mergerAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n zero D mul e P W G unit O roots V GV unitV f g S R : Fin m) :
    Project.Formula.satisfies env (mergerAt w n zero D mul e P W G unit O roots V GV unitV f g S R) ↔ MergerAt (env.bound w) (env.bound n) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound P) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound f) (env.bound g) (env.bound S) (env.bound R) := by
  simp only [mergerAt,MergerAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ConstructionRangeObject.data_semantics hM,ConstructionMappedMerger.data_semantics hM]
  rfl

def attached {m : Nat} (w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRequestSchedule.probeCode
  zero.succ.succ.succ.succ.succ.succ 5 4 3 request.succ.succ.succ.succ.succ.succ) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 5 2)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 4 1)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap
  3 f.succ.succ.succ.succ.succ.succ 0) (probeAt w.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ eN.succ.succ.succ.succ.succ.succ 2 1
  markN.succ.succ.succ.succ.succ.succ 0 W.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ roots.succ.succ.succ.succ.succ.succ
  V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ
  leg.succ.succ.succ.succ.succ.succ nextLeg.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ))))))))))) (.existsE (.existsE (.existsE (.conj
  (ConstructionRequestSchedule.mergerCode one.succ.succ.succ 2 1 request.succ.succ.succ) (.conj
  (ConstructionMergerPrescriptionMapSyntax.graph 1 f.succ.succ.succ 0) (mergerAt w.succ.succ.succ 2
  zero.succ.succ.succ N.succ.succ.succ mulN.succ.succ.succ eN.succ.succ.succ 0 W.succ.succ.succ G.succ.succ.succ
  unit.succ.succ.succ O.succ.succ.succ roots.succ.succ.succ V.succ.succ.succ GV.succ.succ.succ unitV.succ.succ.succ
  leg.succ.succ.succ nextLeg.succ.succ.succ S.succ.succ.succ R.succ.succ.succ)))))))

theorem attached_freeClosed {m : Nat} (w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R : Fin m) :
    (attached w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R).FreeClosed := by
  simp -implicitDefEqProofs [attached,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,probeAt_freeClosed,mergerAt_freeClosed]

theorem attached_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R : Fin m) :
    Project.Formula.satisfies env (attached w zero one request N mulN eN markN f W G unit O roots V GV unitV leg nextLeg S R) ↔ Attached hM (env.bound w) (env.bound zero) (env.bound one) (env.bound request) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound f) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound leg) (env.bound nextLeg) (env.bound S) (env.bound R) := by
  simp only [attached,Attached,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRequestSchedule.probeCode_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,probeAt_semantics hM,mergerAt_semantics hM]
  rfl

def atFormula {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1 : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  Schedule.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 20))
  (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19 18
  17 16 15 14 13 12
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10
  9 8 7 6 5 4
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionRoundSelection.picked
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19 18
  17 16 15 14 12 20
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionRoundSelection.pack 11 10 9 8 7 6 3 4 2
  raw.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionRoundStepSyntax.step
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 19 18
  17 16 15 14 12 11 10 9 8 7 6 3 4) (.conj (ConstructionRoundSelection.done
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 20
  11 10 8 3 4 2) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3))
  (.conj (ConstructionRoundSource.provenance
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 20
  19 18 17 16 12 11 10 9 3 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Out.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Out.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0))
  (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range 19 1
  A0.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range 11 0
  A1.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))
  (attached
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 20
  19 18 17 16 12 11 10 9 3 2
  V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1
  0 A0.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  A1.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))))))))))))))))

theorem atFormula_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1 : Fin m) :
    (atFormula w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1).FreeClosed := by
  simp -implicitDefEqProofs [atFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundSelection.picked_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,ConstructionRoundSelection.done_freeClosed,ConstructionRoundSource.provenance_freeClosed,attached_freeClosed]

theorem atFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1 : Fin m) :
    Project.Formula.satisfies env (atFormula w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1) ↔ At hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound i) (env.bound j) (env.bound raw) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound Out) (env.bound A0) (env.bound A1) := by
  simp only [atFormula,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerHistory.row_semantics hM,ConstructionRoundSelection.picked_semantics hM,ConstructionRoundSelection.pack_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,ConstructionRoundSelection.done_semantics hM,ConstructionRoundSource.provenance_semantics hM,attached_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ForcingSupportedNames.range_semantics (M := M)]
  rfl

def selectedSentence {m : Nat} (w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1 : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerIterationCases.context w Q R top D mul e mark H C zero one u J Schedule)
    (.imp (ConstructionTowerIteration.recursive w Q R top D mul e mark H C zero one J Schedule J history)
    (.imp (ConstructionTowerTransitions.matrix J history zero P F)
    (.imp (ConstructionTowerHistory.chart 0 J history Domains)
    (.imp (Project.Formula.isSuccessor (.bound J) (.bound last))
    (.imp (ConstructionTowerHistory.row history last T GT eT markT HT CT L baseT last)
    (.imp (ConstructionRoundStepSyntax.objectFields w Q R top V GV unitV markV HV CV)
    (.imp (ConstructionRoundStepSyntax.mapFields w Q T V GT GV eT unitV markT markV HT CT HV CV after)
    (.imp (ConstructionBlockStages.result J E Domains F L after V Out Images)
    (.imp (.mem (.bound i) (.bound J))
    (.imp (.mem (.bound j) (.bound J))
    (.imp (Project.Formula.isSuccessor (.bound j) (.bound i))
    (.imp (ConstructionTowerMapSucc.selectedAt w Q R top D mul e mark H C zero one Schedule history F i j raw)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images i A0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images j A1))
    (atFormula w Q R top D mul e mark H C zero one Schedule history F i j raw V GV unitV Out A0 A1))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionBlockStages.result_freeClosed,ConstructionTowerMapSucc.selectedAt_freeClosed,atFormula_freeClosed]

theorem selected_models {m : Nat} (w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1 : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedSentence w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.chart_semantics hM 0,ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionBlockStages.result_semantics hM,ConstructionTowerMapSucc.selectedAt_semantics hM,atFormula_semantics hM]
  exact of_selected hM

theorem selected_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1 : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedSentence w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1)) :=
  ModelTransfer.derives (fun _ hM => selected_models w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j raw A0 A1 hM)

def mapSuccSentence {m : Nat} (w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1 : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionTowerIterationCases.context w Q R top D mul e mark H C zero one u J Schedule)
    (.imp (ConstructionTowerIteration.recursive w Q R top D mul e mark H C zero one J Schedule J history)
    (.imp (ConstructionTowerTransitions.matrix J history zero P F)
    (.imp (ConstructionTowerHistory.chart 0 J history Domains)
    (.imp (Project.Formula.isSuccessor (.bound J) (.bound last))
    (.imp (ConstructionTowerHistory.row history last T GT eT markT HT CT L baseT last)
    (.imp (ConstructionRoundStepSyntax.objectFields w Q R top V GV unitV markV HV CV)
    (.imp (ConstructionRoundStepSyntax.mapFields w Q T V GT GV eT unitV markT markV HT CT HV CV after)
    (.imp (ConstructionBlockStages.result J E Domains F L after V Out Images)
    (.imp (.mem (.bound i) (.bound J))
    (.imp (.mem (.bound j) (.bound J))
    (.imp (Project.Formula.isSuccessor (.bound j) (.bound i))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images i A0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images j A1))
    (.existsE (.conj (ConstructionTowerMapSucc.selectedAt w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ Schedule.succ history.succ F.succ i.succ j.succ 0) (atFormula w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ zero.succ one.succ Schedule.succ history.succ F.succ i.succ j.succ 0 V.succ GV.succ unitV.succ Out.succ A0.succ A1.succ)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isSuccessor,ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerHistory.chart_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionBlockStages.result_freeClosed,ConstructionTowerMapSucc.selectedAt_freeClosed,atFormula_freeClosed]

theorem mapSucc_models {m : Nat} (w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1 : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mapSuccSentence w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mapSuccSentence w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerHistory.chart_semantics hM 0,ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionBlockStages.result_semantics hM,ConstructionTowerMapSucc.selectedAt_semantics hM,atFormula_semantics hM]
  exact map_succ hM

theorem mapSucc_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1 : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mapSuccSentence w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1)) :=
  ModelTransfer.derives (fun _ hM => mapSucc_models w Q R top D mul e mark H C zero one u J Schedule history P F E Domains last T GT eT markT HT CT L baseT V GV unitV markV HV CV after Out Images i j A0 A1 hM)

end PPAC.Migration.ConstructionSelectedAttachments
