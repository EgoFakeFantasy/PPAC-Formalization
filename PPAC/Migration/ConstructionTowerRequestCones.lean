/- Pinned CompleteRounds.probe_independent / creates_merger on the ACTUAL tower.
Read map_succ, the saved later incoming leg, and actual fromBase naturality.
Return both original request conclusions at every later internal cut. -/
import PPAC.Migration.ConstructionConeTransport
import PPAC.Migration.ConstructionTowerMapSucc

namespace PPAC.Migration.ConstructionTowerRequestCones
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ConstructionTowerValidity (Valid row_field)
open ConstructionTowerTransitions (Before Matrix)
open ConstructionTowerIterationCases (Context)
open ConstructionTowerIteration (Recursive)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionRequestSchedule (ProbeCode MergerCode)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def At (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one Schedule history F i j k : M.Carrier .set) : Prop :=
  ∃ request N mulN eN markN HN CN K f W G unitW markW HL LC NewOut base O roots
      V GV unitV markV HV CV KV baseV leg,
    PureKuratowski.PairMember M i request Schedule ∧
    Row history i N mulN eN markN HN CN K f i ∧
    Row history j W G unitW markW HL LC NewOut base j ∧
    Row history k V GV unitV markV HV CV KV baseV k ∧
    ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f
      W G unitW markW HL LC O base ∧
    ConstructionRoundSelection.Done w D mul zero one request W G markW O base roots ∧
    Product F i j O ∧
    ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unitW O roots ∧
    Product F j k leg ∧
    (∀ a b node, ProbeCode zero a b node request →
      ∃ ON genV, ConstructionRoundFields.MapFields hM w Q N V mulN GV eN unitV markN markV HN CN HV CV ON ∧
        NodeMap O leg ON ∧ Product F i k ON ∧ PureKuratowski.PairMember M roots genV leg ∧
        ConstructionProbeIndependent.Realized N mulN markN f V GV ON genV a b node ∧
        ConstructionRoundFresh.ProbeWitness w V GV markV baseV a b node genV ∧
        ∀ x, ¬ PureKuratowski.PairMember M x genV ON) ∧
    (∀ n P, MergerCode one n P request →
      ∃ rootsV, MapsTo n V rootsV ∧ NodeMap roots leg rootsV ∧
        ConstructionMergerRootSystem.RootSystem n P V GV baseV rootsV)

/-- No supplied cut leg, conservative law, image graph or fromBase equation.
They are read from the same valid recursive tower, including the cut j itself. -/
theorem at_later (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C zero one u J Schedule history P F i j k : M.Carrier .set}
    (hCtx : Context hM w Q R top D mul e mark H C zero one u J Schedule)
    (hRec : Recursive hM w Q R top D mul e mark H C zero one J Schedule J history)
    (hF : Matrix J history zero P F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k J)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i) (hBefore : Before j k) :
    At hM w Q R top D mul e mark H C zero one Schedule history F i j k := by
  have hV := ConstructionTowerIterationValidity.recursive_valid hM hCtx hRec (fun _ h => h)
  obtain ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    hRequest,hRowI,hRowJ,hStep,hDone,hO,hSource⟩ :=
    ConstructionTowerMapSucc.map_succ hM hCtx hRec hF hi hj hSucc
  obtain ⟨V,GV,unitV,markV,HV,CV,KV,baseV,hRowK⟩ := hV.1.2 k hk
  obtain ⟨leg,hLeg⟩ := ConstructionTowerTransitions.leg_total (i := j) hV.1
    (ConstructionTowerValidity.incoming_rows hM hV) hk
  have hGlobal : Product F j k leg := (hF.2.2 j k leg).mpr ⟨hj,hk,hLeg⟩
  have hLegEdge := (ConstructionTowerTransitions.matrix_at hV.1 hF hj hk hBefore (row_field 6 hRowK)).mp hGlobal
  have hLegData := hV.2.2.1 j k W G unitW markW HL LC NewOut base V GV unitV markV HV CV KV baseV leg
    hj hk hBefore hRowJ hRowK hLegEdge
  have hLegMap := hLegData.1
  have hNatural := hV.2.2.2.2 j k base baseV KV leg hj hk hBefore
    (row_field 7 hRowJ) (row_field 7 hRowK) (row_field 6 hRowK) hLegEdge
  have hStageI := hV.2.1 i hi N mulN eN markN HN CN K f hRowI
  have hStageK := hV.2.1 k hk V GV unitV markV HV CV KV baseV hRowK
  obtain ⟨hw,_,_,_,hone,_,_,hz,hzw,hLength,_,hRequests⟩ := hCtx
  have hne := ConstructionRequestSchedule.zero_ne_one hz hone
  have hObjN := hStageI.1
  have hOrigin : MapsTo D N f := hStageI.2.1.1.1.1
  have hOMap : MapsTo N W O := hStep.1.2.1.1.1.1
  have hBeforeIK : Before i k := by
    rcases hBefore with hjk | he
    · exact Or.inl ((hLength.mem hk).transitive j hjk i hSucc.predecessor_mem)
    · subst k
      exact Or.inl hSucc.predecessor_mem
  obtain ⟨global,hGlobalLeg⟩ := ConstructionTowerTransitions.leg_total (i := i) hV.1
    (ConstructionTowerValidity.incoming_rows hM hV) hk
  have hGlobalIK : Product F i k global := (hF.2.2 i k global).mpr ⟨hi,hk,hGlobalLeg⟩
  have hGlobalEdge := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hk hBeforeIK (row_field 6 hRowK)).mp hGlobalIK
  have hOldEdge := (ConstructionTowerTransitions.matrix_at hV.1 hF hi hj (Or.inl hSucc.predecessor_mem) (row_field 6 hRowJ)).mp hO
  have hCompGlobal := hV.2.2.2.1 i j k NewOut KV O leg global hi hj hk
    (Or.inl hSucc.predecessor_mem) hBefore (row_field 6 hRowJ) (row_field 6 hRowK) hOldEdge hLegEdge hGlobalEdge
  have hGlobalMap := (hV.2.2.1 i k N mulN eN markN HN CN K f V GV unitV markV HV CV KV baseV global
    hi hk hBeforeIK hRowI hRowK hGlobalEdge).1
  refine ⟨request,N,mulN,eN,markN,HN,CN,K,f,W,G,unitW,markW,HL,LC,NewOut,base,O,roots,
    V,GV,unitV,markV,HV,CV,KV,baseV,leg,
    hRequest,hRowI,hRowJ,hRowK,hStep,hDone,hO,hSource,hGlobal,?_,?_⟩
  · intro a b node hCode
    obtain ⟨ON,genV,hON,hOC,hGenV,hRealized⟩ :=
      ConstructionConeTransport.probe_after hM hw hz hzw hObjN.1 hObjN.2.1 hObjN.2.2.2.1
        hne hCode hSource hOMap hLegMap.1
    have eqON := ConstructionRequestMaps.node_map_unique hM hON hGlobalMap.1.1.1 hOC hCompGlobal
    subst ON
    obtain ⟨hWitness,hFresh⟩ := ConstructionRoundFresh.probe_of_completed hne hCode hDone
    obtain ⟨oa,ob,mapped,ha,hb,hNode,hProfile⟩ := hWitness
    obtain ⟨mappedV,oaV,obV,markV',genV',hMapped,haV,hbV,hmV,hgV,hProfileV⟩ :=
      hLegData.2 oa ob markW roots mapped hProfile
    have eqMark := ForcingConditionGraphs.function_unique hLegMap.1.1.1.1 hmV hLegMap.2.2.2.1
    have eqGen := ForcingConditionGraphs.function_unique hLegMap.1.1.1.1 hgV hGenV
    subst markV'; subst genV'
    refine ⟨global,genV,hGlobalMap,hOC,hGlobalIK,hGenV,hRealized,?_,?_⟩
    · exact ⟨oaV,obV,mappedV,(hNatural a oaV).mpr ⟨oa,ha,haV⟩,
        (hNatural b obV).mpr ⟨ob,hb,hbV⟩,
        ConstructionRoundFields.node_comp hNatural hNode hMapped,hProfileV⟩
    · intro x hx
      obtain ⟨old,hOld,hImage⟩ := (hOC x genV).mp hx
      have he := hLegMap.1.1.2 old roots genV hImage hGenV
      exact hFresh x (he ▸ hOld)
  · intro n P hCode
    obtain ⟨hMerger,_⟩ := ConstructionRoundFresh.merger_of_completed hne hCode hDone
    have hPrescription : ConstructionMergerRelations.Prescription n D P := by
      rcases hRequests i request hRequest with ⟨a,b,node,hProbe,_⟩ | ⟨n',P',hCode',_,_,hP,_⟩
      · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hProbe hCode)
      · obtain ⟨en,ep⟩ := ConstructionRequestSchedule.merger_code_injective hCode hCode'
        subst n'; subst P'
        exact hP
    obtain ⟨ON,baseV',rootsV,hON,hBase',hRootsV,hOC,hRC,hBC,hFinal⟩ :=
      ConstructionConeTransport.merger_after hM hw hz hzw hObjN.1 hStep.1.1.1 hne hCode hSource
        hPrescription hOrigin hOMap hMerger.1 hLegMap.1 hLegMap.2.1
    have hActual : NodeMap f ON baseV := ConstructionRoundFields.node_comp hOC hStep.2.1 hNatural
    have eqBase := ConstructionRequestMaps.node_map_unique hM hBase' hStageK.2.1.1.1.1 hBC hActual
    subst baseV'
    exact ⟨rootsV,hRootsV,hRC,hFinal⟩



def conesAt {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j k : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  Schedule.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (27 : Fin (m+28)))) (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (26 : Fin (m+28)) (25 : Fin (m+28)) (24 : Fin (m+28)) (23 : Fin (m+28)) (22 : Fin (m+28)) (21 : Fin
  (m+28)) (20 : Fin (m+28)) (19 : Fin (m+28))
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (18 : Fin (m+28)) (17 : Fin (m+28)) (16 : Fin (m+28)) (15 : Fin (m+28)) (14 : Fin (m+28)) (13 : Fin
  (m+28)) (12 : Fin (m+28)) (11 : Fin (m+28))
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  k.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (8 : Fin (m+28)) (7 : Fin (m+28)) (6 : Fin (m+28)) (5 : Fin (m+28)) (4 : Fin (m+28)) (3 : Fin (m+28)) (2 :
  Fin (m+28)) (1 : Fin (m+28))
  k.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionRoundStepSyntax.step
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (26 : Fin (m+28)) (25 : Fin (m+28)) (24 : Fin (m+28)) (23 : Fin (m+28)) (22 : Fin (m+28)) (21 : Fin
  (m+28)) (19 : Fin (m+28)) (18 : Fin (m+28)) (17 : Fin (m+28)) (16 : Fin (m+28)) (15 : Fin (m+28)) (14 :
  Fin (m+28)) (13 : Fin (m+28)) (10 : Fin (m+28)) (11 : Fin (m+28))) (.conj (ConstructionRoundSelection.done
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (27 : Fin (m+28)) (18 : Fin (m+28)) (17 : Fin (m+28)) (15 : Fin (m+28)) (10 : Fin (m+28)) (11 : Fin
  (m+28)) (9 : Fin (m+28))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (10 : Fin (m+28)))) (.conj (ConstructionRoundSource.provenance
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (27 : Fin (m+28)) (26 : Fin (m+28)) (25 : Fin (m+28)) (24 : Fin (m+28)) (23 : Fin (m+28)) (19 : Fin
  (m+28)) (18 : Fin (m+28)) (17 : Fin (m+28)) (16 : Fin (m+28)) (10 : Fin (m+28)) (9 : Fin (m+28))) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  k.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (0 : Fin (m+28)))) (.conj (.forallE (.forallE (.forallE (.imp (ConstructionRequestSchedule.probeCode
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (2 : Fin (m+31)) (1 : Fin (m+31)) (0 : Fin (m+31)) (27 : Fin (m+28)).succ.succ.succ) (.existsE (.existsE
  (.conj (ConstructionRoundStepSyntax.mapFields
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (26 : Fin (m+28)).succ.succ.succ.succ.succ (8 : Fin (m+28)).succ.succ.succ.succ.succ (25 : Fin
  (m+28)).succ.succ.succ.succ.succ (7 : Fin (m+28)).succ.succ.succ.succ.succ (24 : Fin
  (m+28)).succ.succ.succ.succ.succ (6 : Fin (m+28)).succ.succ.succ.succ.succ (23 : Fin
  (m+28)).succ.succ.succ.succ.succ (5 : Fin (m+28)).succ.succ.succ.succ.succ (22 : Fin
  (m+28)).succ.succ.succ.succ.succ (21 : Fin (m+28)).succ.succ.succ.succ.succ (4 : Fin
  (m+28)).succ.succ.succ.succ.succ (3 : Fin (m+28)).succ.succ.succ.succ.succ (1 : Fin (m+33))) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap (10 : Fin (m+28)).succ.succ.succ.succ.succ (0 : Fin
  (m+28)).succ.succ.succ.succ.succ (1 : Fin (m+33))) (.conj (ProjectSyntax.encode id
  (ForcingDiagramOrder.product
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  k.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (1 : Fin (m+33)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
  (m+28)).succ.succ.succ.succ.succ (9 : Fin (m+28)).succ.succ.succ.succ.succ (0 : Fin (m+33)))) (.conj
  (ConstructionProbeIndependent.realized (26 : Fin (m+28)).succ.succ.succ.succ.succ (25 : Fin
  (m+28)).succ.succ.succ.succ.succ (23 : Fin (m+28)).succ.succ.succ.succ.succ (19 : Fin
  (m+28)).succ.succ.succ.succ.succ (8 : Fin (m+28)).succ.succ.succ.succ.succ (7 : Fin
  (m+28)).succ.succ.succ.succ.succ (1 : Fin (m+33)) (0 : Fin (m+33)) (2 : Fin (m+31)).succ.succ (1 : Fin
  (m+31)).succ.succ (0 : Fin (m+31)).succ.succ) (.conj (ConstructionRoundFresh.probeWitness
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (8 : Fin (m+28)).succ.succ.succ.succ.succ (7 : Fin (m+28)).succ.succ.succ.succ.succ (5 : Fin
  (m+28)).succ.succ.succ.succ.succ (1 : Fin (m+28)).succ.succ.succ.succ.succ (2 : Fin (m+31)).succ.succ (1 :
  Fin (m+31)).succ.succ (0 : Fin (m+31)).succ.succ (0 : Fin (m+33))) (.forallE (.neg (ProjectSyntax.encode
  id (Source.SetLanguage.edge (1 : Fin (m+33)).succ (0 : Fin (m+34)) (0 : Fin (m+33)).succ))))))))))))))))
  (.forallE (.forallE (.imp (ConstructionRequestSchedule.mergerCode
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (1 : Fin (m+30)) (0 : Fin (m+30)) (27 : Fin (m+28)).succ.succ) (.existsE (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo (0 : Fin (m+31)) (1 : Fin (m+30)).succ (8 : Fin (m+28)).succ.succ.succ)) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap (9 : Fin (m+28)).succ.succ.succ (0 : Fin (m+28)).succ.succ.succ
  (0 : Fin (m+31))) (ConstructionMergerRootSystem.rootSystem (1 : Fin (m+30)).succ (0 : Fin (m+30)).succ (8
  : Fin (m+28)).succ.succ.succ (7 : Fin (m+28)).succ.succ.succ (1 : Fin (m+28)).succ.succ.succ (0 : Fin
  (m+31)))))))))))))))))))))))))))))))))))))))))))))))

theorem conesAt_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one Schedule history F i j k : Fin m) :
    (conesAt w Q R top D mul e mark H C zero one Schedule history F i j k).FreeClosed := by
  simp -implicitDefEqProofs [conesAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionRoundFresh.probeWitness_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,ConstructionRoundSelection.done_freeClosed,ConstructionRoundSource.provenance_freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionProbeIndependent.realized_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionMergerRootSystem.rootSystem_freeClosed]

theorem conesAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one Schedule history F i j k : Fin m) :
    Project.Formula.satisfies env (conesAt w Q R top D mul e mark H C zero one Schedule history F i j k) ↔ At hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound Schedule) (env.bound history) (env.bound F) (env.bound i) (env.bound j) (env.bound k) := by
  simp only [conesAt,At,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRoundFresh.probeWitness_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,ConstructionRoundSelection.done_semantics hM,ConstructionRoundSource.provenance_semantics hM,ConstructionRequestSchedule.probeCode_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionProbeIndependent.realized_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionMergerRootSystem.rootSystem_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl


def cutSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 21 (.imp (ConstructionTowerIterationCases.context (0 : Fin 21) (1 : Fin 21)
    (2 : Fin 21) (3 : Fin 21) (4 : Fin 21) (5 : Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (9 : Fin 21)
    (10 : Fin 21) (11 : Fin 21) (12 : Fin 21) (13 : Fin 21) (14 : Fin 21)) (.imp
    (ConstructionTowerIteration.recursive (0 : Fin 21) (1 : Fin 21) (2 : Fin 21) (3 : Fin 21) (4 : Fin 21)
    (5 : Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (9 : Fin 21) (10 : Fin 21) (11 : Fin 21) (13 : Fin
    21) (14 : Fin 21) (13 : Fin 21) (15 : Fin 21)) (.imp (ConstructionTowerTransitions.matrix (13 : Fin 21)
    (15 : Fin 21) (10 : Fin 21) (16 : Fin 21) (17 : Fin 21)) (.imp (.mem (.bound (18 : Fin 21)) (.bound (13
    : Fin 21))) (.imp (.mem (.bound (19 : Fin 21)) (.bound (13 : Fin 21))) (.imp (.mem (.bound (20 : Fin
    21)) (.bound (13 : Fin 21))) (.imp (Project.Formula.isSuccessor (.bound (19 : Fin 21)) (.bound (18 : Fin
    21))) (.imp (ConstructionTowerTransitions.before (19 : Fin 21) (20 : Fin 21)) (conesAt (0 : Fin 21) (1 :
    Fin 21) (2 : Fin 21) (3 : Fin 21) (4 : Fin 21) (5 : Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (9 :
    Fin 21) (10 : Fin 21) (11 : Fin 21) (14 : Fin 21) (15 : Fin 21) (17 : Fin 21) (18 : Fin 21) (19 : Fin
    21) (20 : Fin 21)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerIterationCases.context_freeClosed,ConstructionTowerIteration.recursive_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,Project.Formula.isSuccessor,
      ConstructionTowerTransitions.before_freeClosed,conesAt_freeClosed]

theorem cut_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence cutSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) cutSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isSuccessor_iff,Project.Term.eval_bound,
    ConstructionTowerIterationCases.context_semantics hM,ConstructionTowerIteration.recursive_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerTransitions.before_semantics hM,conesAt_semantics hM]
  exact fun hCtx hRec hF hi hj hk hSucc hBefore => at_later hM hCtx hRec hF hi hj hk hSucc hBefore

theorem cut_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence cutSentence) := ModelTransfer.derives (fun _ hM => cut_models hM)

end PPAC.Migration.ConstructionTowerRequestCones
