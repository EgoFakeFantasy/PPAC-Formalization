/- Fixed AssignedGraphs.graphRelation_onto:218-249. Reuse the same whole-orbit
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

theorem holds_onto (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop : Fin k) (families : Fin 16 → Fin k)
    {p y : M.Carrier .set}
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
    (hQ : ConstructionFractionOrder.Carrier (env w) (env Qcuts))
    (hR : ConstructionRealCuts.CutCarrier hM (env w) (env Qcuts) (env Rcuts))
    (hTopCut : ConstructionRealCuts.Cut hM (env w) (env Qcuts) (env realTop))
    (hObjFields : ConstructionRoundFields.ObjectFields hM (env w) (env Qcuts) (env Rcuts) (env realTop) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d0))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d0) (env q))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env name))
    (hp0 : MapRel (orderFormula (rho 0) mul) env p (env z0))
    (hy : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env name) p) :
    ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env r p →
      ∃ s, (Project.FirstOrderSemantics.reduct M).mem s (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env s r ∧
        ∃ x, ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env labels) s ∧
          ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families s x y := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hpW := ForcingAtomicBasic.condition hM hy
  have hz0W := ForcingSupportingRoot.code_mem hp hd0 hq hz0
  have hSmall : ForcingSupportSize.Small (env w) (env mu) := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hLarge : ¬ ForcingSupportSize.Small (env I) (env mu) := by
    intro hsmall
    exact hI.not_cardinalLessOrEqual (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) ((ForcingSupportSize.native_small hM (env I) (env mu)).mp hsmall)
  intro r hr hrp
  obtain ⟨s,j,cls,hs,hsr,hjc,hyc⟩ := ((ForcingQuotientName.mem_quotient hM env rho G F mul I K labelMap top bit labels E hName hpre hpW).mp hy) r hr hrp
  obtain ⟨hj,hclsHS,xj,hxj,hcls⟩ := (ForcingRelationClassMove.family_semantics env rho G F mul I K labelMap top bit labels E j cls).mp hjc
  obtain ⟨d,root,c,hd,hRoot,hc,hcs⟩ := ForcingLabelDensity.exists_condition_below hM hp hm hq hs
  have hcW := ForcingSupportingRoot.code_mem hp hd hRoot hc
  have hcs' := (orderFormula_semantics env (rho 0) mul c s).mpr hcs
  have hcz0 := hpre.2 c s (env z0) hcW hs hz0W hcs' (hpre.2 s r (env z0) hs hr hz0W hsr (hpre.2 r p (env z0) hr hpW hz0W hrp hp0))
  have hBase := (ForcingSupportingRoot.code_le hc hz0).mp ((orderFormula_semantics env (rho 0) mul c (env z0)).mp hcz0)
  obtain ⟨single,hSingle⟩ := ForcingWithTopCarrier.exists_single hM j
  have hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset single (env I) := fun z hz => ((hSingle z).mp hz).symm ▸ hj
  have hJmu := ForcingLabelNames.singleton_small hM hw hSmall hSingle
  obtain ⟨t,ht,hSub,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard (hm.2.1 (env mark) hMark) hRoot hJI hJmu
  have htr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) t root := ⟨env mark,hMark,hSub⟩
  obtain ⟨index,hIndex,hSubq⟩ := ForcingDiagramPoset.le_trans hm htr hBase.2
  obtain ⟨objectsT,hObjectsT,_⟩ := hObj.1.2 t ((hDiagrams t).mpr ht)
  have hRangeT := ((hObjects t objectsT).mp hObjectsT).2
  have hjT := (hRangeT j).mpr (hCover j ((hSingle j).mpr rfl))
  obtain ⟨fixingT,hFixT⟩ := ForcingLabelPermutations.exists_fixing hM (env G) objectsT
  have hAqT : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z (env A) →
      (Project.FirstOrderSemantics.reduct M).mem z objectsT :=
    fun z hz => (hRangeT z).mpr (ConstructionDescentPlacement.range_antitone ⟨index,hIndex,hSubq⟩ ((hRange z).mp hz))
  have hET := ForcingSupportedNames.supported_mono hHq hFixT hAqT hE
  let classEnv : Fin (k+1) → M.Carrier .set := Fin.cases xj env
  have heClass (i : Fin k) : classEnv i.succ = env i := rfl
  obtain ⟨tau,hLocal,htauClass',hForce'⟩ := ForcingRelationClass.actual_labelClass hM classEnv
    (fun i => (rho i).succ) G.succ F.succ mul.succ labels.succ E.succ 0
    hw hMu hm hp hG hF hLabelMap hTop hLabels hxj hLabelBound
    (fun z hz => by obtain ⟨u,_,huz⟩ := (hRangeT z).mp hz; exact ht.1.2 u z huz)
    hFixT hjT hEHS hET
  have hRClass (u v : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (rho 0).succ mul.succ) classEnv u v ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env u v := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heClass]
  have hHClass (u : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun i => (rho i).succ) G.succ F.succ) classEnv u ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env u := by
    simp only [ForcingPairUnion.domain_semantics,heClass]
  have htauClass : ForcingRelationClass.Class (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (env (rho 6)) (env labels) (env E) xj tau := by
    intro child q
    exact (htauClass' child q).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (ForcingEquivariantMix.forces_order_congr hRClass false (env (rho 6)) child (env labels) q) (ForcingSeparation.force_congr hRClass hHClass _ _ _ _))))
  have hclsEq : cls = tau :=
    ForcingRelationClassMove.class_unique hM (ForcingHS.isName hclsHS) (ForcingHS.isName hLocal.1.1) hcls htauClass
  let vEnv : Fin (k+6) → M.Carrier .set :=
    Fin.cases objectsT (Fin.cases fixingT (Fin.cases t (Fin.cases index (Fin.cases tau (Fin.cases d env)))))
  let upV : Fin k → Fin (k+6) := fun i => i.succ.succ.succ.succ.succ.succ
  have heV (i : Fin k) : vEnv (upV i) = env i := rfl
  have hRV (u v : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (upV (rho 0)) (upV mul)) vEnv u v ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env u v := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heV]
  have hHV (u : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun i => upV (rho i)) (upV G) (upV F)) vEnv u ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env u := by
    simp only [ForcingPairUnion.domain_semantics,heV]
  have hForceV (z : M.Carrier .set) (hzW : (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6))) :
      ForcingFormula.Force (orderFormula (upV (rho 0)) (upV mul)) (ForcingPairUnion.domain (fun i => upV (rho i)) (upV G) (upV F)) vEnv
        (Source.SetLanguage.args3 (vEnv 4) (vEnv (upV labels)) (vEnv (upV E))) (vEnv (upV (rho 6))) z (ForcingEligibility.isClass 0 1 2) :=
    (ForcingSeparation.force_congr hRV hHV (ForcingEligibility.isClass 0 1 2)
      (Source.SetLanguage.args3 tau (env labels) (env E)) (env (rho 6)) z).mpr
      ((ForcingSeparation.force_congr hRClass hHClass (ForcingEligibility.isClass 0 1 2)
        (Source.SetLanguage.args3 tau (env labels) (env E)) (env (rho 6)) z).mp (hForce' z hzW))
  obtain ⟨d1,U,vertex,hd1,hdd1,hCode,hVertex,hEntry,hStableV⟩ :=
    ForcingForcedAvailabilityStable.class_dense_vertex hM hChoice vEnv (fun i => upV (rho i))
      (upV G) (upV F) (upV mul) (upV w) (upV mu) (upV history) (upV kappa) (upV one) (upV mark) (upV H) (upV C)
      (upV incoming) (upV base) (upV I) (upV K) (upV B) (upV labelMap) (upV top) (upV bit) (upV labels) (upV bound)
      (upV E) (upV q) (upV A) (upV Hq) 0 1 2 3 4 5 (upV Qcuts) (upV Rcuts) (upV realTop)
      hw hMu hI hSmallD hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hRange hHq hE hLabelBound
      hQ hR hTopCut hObjFields ht hRangeT hFixT hLocal hIndex hSubq ((hp.2.2.1 d).mpr hd) hForceV
  have hStable : ForcingStableAt.StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun i => env (rho i)) (env G) (env F) (env mul) (env bound) (env labels) (env E) d1 vertex tau :=
    (ForcingGermCorrectedStable.stable_reindex env vEnv upV heV rho G F mul bound labels E d1 vertex tau).mp hStableV
  have hd1C : ForcingCohenConditions.Condition (env (rho 2)) (env w) d1 := (hp.2.2.1 d1).mp hd1
  have hd0d1 : ForcingPowerName.Subset (env d0) d1 := fun u hu => hdd1 u (hBase.1 u hu)
  have hv : (Project.FirstOrderSemantics.reduct M).mem vertex (env vertices) := (hVertices vertex).mpr ⟨t,index,U,hCode,hVertex⟩
  obtain ⟨e,label,he,hd1e,hLabel,hAssigned⟩ := onto_from_records hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 families d1 vertex tau
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hd1C hd0d1 hv hStable
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM e t
  have hzW := ForcingSupportingRoot.code_mem hp he ht hz
  have hde : ForcingPowerName.Subset d e := fun u hu => hd1e u (hdd1 u hu)
  have hzc := (orderFormula_semantics env (rho 0) mul z c).mpr ((ForcingSupportingRoot.code_le hz hc).mpr ⟨hde,htr⟩)
  have hzs := hpre.2 z c s hzW hcW hs hzc hcs'
  obtain ⟨xk,hxk⟩ := ForcingLabelNames.exists_label hM hLabelMap (env (rho 6)) (env top) label (env bit)
  have hWitness : ForcingAssignedGraph.Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families z xk y :=
    ⟨e,vertex,label,tau,t,index,U,z,xk,(hp.2.2.1 e).mpr he,hCode,hVertex,hLabel,hEntry,hz,hpre.1 z hzW,hAssigned,hxk,ForcingAtomicBasic.eq_refl hM hpre xk z hzW,ForcingAtomicBasic.eq_mono hM hpre hzW hzs (hclsEq ▸ hyc)⟩
  have hBounds := ForcingAssignedGraphBounds.witness_bounds hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q A Hq zero vertices names Q high objects maps records families
    hw hMu hI hSmallD hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hRecords hProjections hChains hEHS hName hWitness
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hHS := ForcingLabelNames.label_HS hM (fun i => env (rho i)) hp hG hNormal hF hw hSmall hLabelMap hTop hLabel hxk
  exact ⟨z,hzW,hpre.2 z s r hzW hs hr hzs hsr,xk,hHS,hBounds.1,ForcingAssignedGraph.witness_holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp hWitness⟩

/-- Source dense surjectivity for the actual graph, with every input in HS. -/
def ontoSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingOrbitParameterFamily.family rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q id records)
    (.imp (ForcingAssignedParameters.projections high Q records (families 0) (families 1) (families 2) (families 3) (families 4) (families 5) (families 6) (families 7) (families 8) (families 9) (families 10) (families 11) (families 12) (families 13) (families 14) (families 15))
    (.imp (allCounts rho I mul q w top Q d0 families)
    (.imp (ConstructionFractionOrder.carrier w Qcuts)
    (.imp (ConstructionRealCuts.cutCarrier w Qcuts Rcuts)
    (.imp (ConstructionRealCuts.cut w Qcuts realTop)
    (.imp (ConstructionRoundStepSyntax.objectFields w Qcuts Rcuts realTop (rho 0) mul one mark H C)
    (.imp (.mem (.bound mark) (.bound (rho 0)))
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 q))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingQuotientName.quotient rho G F mul I K labelMap top bit labels E id name))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) id p z0))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) y name p))
    (.forallE (.imp (.mem (.bound 0) (.bound ((rho 6).succ)))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => i.succ) 0 p.succ))
      (.existsE (.conj (.mem (.bound 0) (.bound ((rho 6).succ.succ)))
        (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => i.succ.succ) 0 1))
          (.existsE (.conj (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula (fun j => (rho j).succ.succ.succ) G.succ.succ.succ (rho 6).succ.succ.succ F.succ.succ.succ 0))
            (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) (fun i => i.succ.succ.succ) (rho 6).succ.succ.succ 0 labels.succ.succ.succ 1))
              (ForcingAssignedGraph.holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun i => i.succ.succ.succ) 1 0 y.succ.succ.succ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,ForcingTailCodes.candidates_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingOrbitParameterFamily.family_freeClosed,ForcingAssignedParameters.projections_freeClosed,ForcingAssignedGraph.holds_freeClosed,allCounts_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed]

theorem onto_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (ontoSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),ForcingTailCodes.candidates_semantics hM,ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingOrbitParameterFamily.family_semantics hM,ForcingAssignedParameters.projections_semantics hM,ForcingAssignedGraph.holds_semantics hM,ForcingAtomicRelations.forces_semantics (M := M),allCounts_semantics hM,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),ForcingHS.hs_semantics (M := M),ForcingQuotientName.quotient_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,id_eq]
  exact holds_onto hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop families

theorem onto_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (ontoSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y families))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (ontoSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (ontoSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y families)).mp
      (onto_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop p y families hL hChoice)

end PPAC.Migration.ForcingAssignedGraphOnto
