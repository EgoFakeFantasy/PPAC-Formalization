/- WORK IN PROGRESS: only onto_from_records is implemented.
The actual GraphHolds surjectivity theorem and its object-level certificate
are not yet implemented or accepted.

Fixed AssignedGraphs.graphRelation_onto:218-249. Reuse the same whole-orbit
record and count assembly, actual local-class stabilization and assigned_onto.
No assumed graph surjectivity, stable ideal or chosen name replacement. -/
import PPAC.Migration.ForcingAssignedGraphTotal
import PPAC.Migration.ForcingForcedAvailabilityStable

namespace PPAC.Migration.ForcingAssignedGraphOnto
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingAssigned (Assigned Fields Functions Germs)
open ForcingSupportSize (MapsTo Injection)
open ForcingComponentFibers (VertexFiber)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingAtomicRelations (Forces)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

open ForcingAssignedGraphTotal (AllCounts allCounts allCounts_freeClosed allCounts_semantics)

private theorem onto_from_records (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 : Fin k) (families : Fin 16 → Fin k)
    (d vertex tau : M.Carrier .set)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hCommon : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hRecords : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q (env records))
    (hProjections : ForcingAssignedParameters.Projections (env high) (env Q) (env records) (env (families 0)) (env (families 1)) (env (families 2)) (env (families 3)) (env (families 4)) (env (families 5)) (env (families 6)) (env (families 7)) (env (families 8)) (env (families 9)) (env (families 10)) (env (families 11)) (env (families 12)) (env (families 13)) (env (families 14)) (env (families 15)))
    (hCounts : AllCounts hM env rho I mul q w top Q d0 families)
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) d)
    (hdd0 : ForcingPowerName.Subset (env d0) d)
    (hv : (Project.FirstOrderSemantics.reduct M).mem vertex (env vertices))
    (hStable : ForcingStableAt.StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) d vertex tau) :
    ∃ e label, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧ ForcingPowerName.Subset d e ∧
      (Project.FirstOrderSemantics.reduct M).mem label (env I) ∧
      Assigned hM env rho I G F mul q bound labels E w top K B zero Q families e vertex label tau := by
  obtain ⟨a,hClass⟩ := ForcingOrbitQuotient.exists_class hM (env (rho 0)) (env I) (env mul) (env q) (env vertices) vertex
  have ha := (hQuotient a).mpr ⟨vertex,hv,hClass⟩
  have hIndex := (hProjection vertex a).mpr ⟨hv,hClass⟩
  obtain ⟨output,hOutput,_⟩ := hRecords.1.2 a ha
  obtain ⟨root,chain,hRootEdge,hChainEdge,hRecord⟩ := hRecords.2 a output hOutput
  obtain ⟨r,rootIndex,rootU,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,nonidentity,detectorDomain,detector,detectorSites,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hRecordCode,hRoot,hRootFiber,hData,hResult⟩ := hRecord
  have hFields : Fields env families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity (env high) detector patternOrder :=
    ForcingAssignedParameters.fields_of_record hRecords.1 hOutput hProjections hA hB hC hRecordCode
  let other : Fin (k+32) → M.Carrier .set := Fin.cases a (Fin.cases root (Fin.cases chain (Fin.cases r (Fin.cases rootIndex (Fin.cases rootU (Fin.cases labelSet (Fin.cases codes (Fin.cases order (Fin.cases group (Fin.cases support (Fin.cases fixing (Fin.cases ranks (Fin.cases selection (Fin.cases rankBound (Fin.cases tab (Fin.cases germGroup (Fin.cases quotient (Fin.cases projection (Fin.cases reps (Fin.cases nonidentity (Fin.cases detectorDomain (Fin.cases detector (Fin.cases detectorSites (Fin.cases patternCarrier (Fin.cases patternOrder (Fin.cases selectorDomain (Fin.cases selector (Fin.cases tau (Fin.cases d (Fin.cases vertex (Fin.cases tau (env))))))))))))))))))))))))))))))))
  let upother : Fin k → Fin (k+32) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have heother (i : Fin k) : other (upother i) = env i := rfl
  obtain ⟨hCarrier,hOrder,hGroup,hRootA,hRootH,hIncl,_,_,_,_,hRanks,hSelection,hFamily,hType,hRank,hTable⟩ := hData
  let rankEnv : Fin (k+8) → M.Carrier .set := Fin.cases order (Fin.cases codes (Fin.cases labelSet (Fin.cases rootU (Fin.cases rootIndex (Fin.cases r (Fin.cases chain (Fin.cases root (env))))))))
  let rankMap : Fin (k+8) → Fin (k+32) := Fin.cases (8) (Fin.cases (7) (Fin.cases (6) (Fin.cases (5) (Fin.cases (4) (Fin.cases (3) (Fin.cases (2) (Fin.cases (1) (upother))))))))
  have heRank (i : Fin (k+8)) : other (rankMap i) = rankEnv i := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl ((fun _ => rfl))))))))) i
  let upRank : Fin k → Fin (k+8) := fun i : Fin k => i.succ.succ.succ.succ.succ.succ.succ.succ
  change ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0) id (upRank (rho 0)) (upRank I) (upRank (rho 2)) (upRank w)) rankEnv codes order (env (rho 6)) ranks at hRanks
  have hSelected (a d : M.Carrier .set) :
      ForcingCodeSelection.IsSelected other (fun j => upother (rho j)) (upother I) (upother G) (upother F) (upother mul) (upother q) (upother bound) (upother labels) (upother E) 1 (upother w) 2 7 8 a d ↔
      ForcingCodeSelection.IsSelected rankEnv (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0 a d :=
    ForcingCodeRanks.selected_reindex rankEnv other rankMap heRank (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0 a d
  have hOtherRanks : ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upother (rho j)) (upother I) (upother G) (upother F) (upother mul) (upother q) (upother bound) (upother labels) (upother E) 1 (upother w) 2 7 8) id (upother (rho 0)) (upother I) (upother (rho 2)) (upother w)) other codes order (env (rho 6)) ranks := by
    simpa only [ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,ForcingCodeSelection.mapRel_relation hM,id_eq,hSelected,heother,rankEnv,upRank,Fin.cases_succ] using hRanks
  change ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0) id (upRank (rho 0)) (upRank I) (upRank (rho 2)) (upRank w)) rankEnv codes ranks (env (rho 6)) selection at hSelection
  have hOtherSelection : ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upother (rho j)) (upother I) (upother G) (upother F) (upother mul) (upother q) (upother bound) (upother labels) (upother E) 1 (upother w) 2 7 8) id (upother (rho 0)) (upother I) (upother (rho 2)) (upother w)) other codes ranks (env (rho 6)) selection := by
    simpa only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,ForcingCodeSelection.mapRel_relation hM,id_eq,hSelected,heother,rankEnv,upRank,Fin.cases_succ] using hSelection
  have hCount := hCounts d a selection r labelSet hd hdd0 ha hFields.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.1
  let countEnv : Fin (k+5) → M.Carrier .set := Fin.cases labelSet (Fin.cases r (Fin.cases selection (Fin.cases a (Fin.cases d env))))
  let countMap : Fin (k+5) → Fin (k+32) := Fin.cases 6 (Fin.cases 3 (Fin.cases 13 (Fin.cases 0 (Fin.cases 29 upother))))
  have heCount (i : Fin (k+5)) : other (countMap i) = countEnv i :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))) i
  let upCount : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  have hOtherCount : ForcingOrbitCounts.RootCounts hM other (fun j => upother (rho j)) (upother I) (upother mul) (upother q) (upother w) (upother top) 13 3 6 d :=
    (ForcingOrbitCounts.rootCounts_reindex hM countEnv other countMap heCount (fun j => upCount (rho j)) (upCount I) (upCount mul) (upCount q) (upCount w) (upCount top) 2 1 0 d).mpr hCount
  obtain ⟨e,label,he,hde,hLabel,hAssigned⟩ := ForcingAssignedDensity.assigned_onto hM hChoice other (fun j => upother (rho j)) (upother w) (upother mu) (upother history) (upother kappa) (upother one) (upother mark) (upother H) (upother C) (upother incoming) (upother base) (upother I) (upother K) (upother B) (upother G) (upother F) (upother mul) (upother labelMap) (upother top) (upother bit) (upother labels) (upother bound) (upother E) (upother q) (upother A) (upother Hq) (upother zero) 1 (upother vertices) 2 (upother names) 30 7 8 12 13 9 3 4 5 10 11 14 6 15 31 29 16 17 18 19 20 21 22 23 (upother high) 24 25 26 27 (upother diagrams) (upother objImage) (upother objects) (upother arrows) (upother mapImage) (upother maps) (upother Q) (upother pr) 0 (fun j => upother (families j))
    hw hMu hI hSmallD hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hNames hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hOtherRanks hOtherSelection hFamily hType hRank hTable hd hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily (ForcingLabelSystem.system_of_families hObj hObjects hMapFamily) hCommon hRootFiber hOtherCount hQuotient hProjection hReps hIndex hChains hFields
    ((ForcingGermCorrectedStable.stable_reindex env other upother heother rho G F mul bound labels E d vertex tau).mpr hStable)
  exact ⟨e,label,he,hde,hLabel,(ForcingAssigned.assigned_reindex hM env other upother heother rho I G F mul q bound labels E w top K B zero Q families e vertex label tau).mp hAssigned⟩

end PPAC.Migration.ForcingAssignedGraphOnto
