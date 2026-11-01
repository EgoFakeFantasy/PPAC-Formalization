/- Fixed AssignedGraphs.graphRelation_one:109-132. Retrieve BOTH actual
orbit records, construct the common label vertex, and reuse the existing
OrbitAssignments.assigned_compatible_one:597-610 adapter. Actual dense graph
witnesses and label separation close single-valuedness in the SAME internal L. -/
import PPAC.Migration.ForcingAssignedCompatibility
import PPAC.Migration.ForcingAssignedParameters
import PPAC.Migration.ForcingAssignedGraph
import PPAC.Migration.ForcingLabelSeparation

namespace PPAC.Migration.ForcingAssignedGraphOne
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

private theorem label_in_extension {D mul diagrams objects maps v X oldRoot oldIndex oldIdeal commonRoot commonObjects label : M.Carrier .set}
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hFiber : VertexFiber D mul objects maps v X)
    (hCode : ConstructionComponentCarrier.Code v oldRoot oldIndex oldIdeal)
    (hTarget : PureKuratowski.PairMember M commonRoot commonObjects objects)
    (hExtension : ForcingDiagramOrder.Le D mul commonRoot oldRoot)
    (hj : (Project.FirstOrderSemantics.reduct M).mem label X) :
    (Project.FirstOrderSemantics.reduct M).mem label commonObjects := by
  obtain ⟨r,a,U,Or,hc,hr,hf⟩ := hFiber
  have er := (ConstructionComponentCarrier.code_injective hc hCode).1
  have hRange : ForcingSupportedNames.Range D oldRoot Or := er ▸ ((hObjects r Or).mp hr).2
  obtain ⟨n,_,hSub⟩ := hExtension
  obtain ⟨i,hi,_,hij⟩ := (ConstructionDiagramPlacements.sub_range hSub).mp ((hRange label).mp ((hf label).mp hj).1)
  exact (((hObjects commonRoot commonObjects).mp hTarget).2 label).mpr ⟨i,hi,hij⟩

private theorem compatible_one_from_records (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records : Fin k) (families : Fin 16 → Fin k)
    (d vertex label tau e vertexSecond sigma f commonRoot oldRoot oldIndex oldIdeal oldRootSecond oldIndexSecond oldIdealSecond : M.Carrier .set)
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
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
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
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hCommon : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (he : (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)))
    (hde : ForcingPowerName.Subset d f)
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hOldCode : ConstructionComponentCarrier.Code vertex oldRoot oldIndex oldIdeal)
    (hOldVertex : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) oldRoot oldIndex oldIdeal)
    (hExtension : ForcingDiagramOrder.Le (env (rho 0)) (env mul) commonRoot oldRoot)
    (hdeSecond : ForcingPowerName.Subset e f)
    (hSecond : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families e vertexSecond label sigma)
    (hOldCodeSecond : ConstructionComponentCarrier.Code vertexSecond oldRootSecond oldIndexSecond oldIdealSecond)
    (hOldVertexSecond : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) oldRootSecond oldIndexSecond oldIdealSecond)
    (hExtensionSecond : ForcingDiagramOrder.Le (env (rho 0)) (env mul) commonRoot oldRootSecond)
    (hRecords : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q (env records))
    (hProjections : ForcingAssignedParameters.Projections (env high) (env Q) (env records) (env (families 0)) (env (families 1)) (env (families 2)) (env (families 3)) (env (families 4)) (env (families 5)) (env (families 6)) (env (families 7)) (env (families 8)) (env (families 9)) (env (families 10)) (env (families 11)) (env (families 12)) (env (families 13)) (env (families 14)) (env (families 15)))
    (hStrong : ForcingSupportSize.Injection (env (rho 0)) (env I) commonRoot)
    (hEntrySecond : ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertexSecond sigma) :
    ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) f commonRoot tau sigma := by
  have hFunctions : Functions env families (env Q) := ForcingAssignedParameters.functions hProjections
  have hGerms := ForcingAssignedParameters.germs hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q hRecords hProjections
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  obtain ⟨hHS,hFixed⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hLabelMap hTop hLabels
  have hBound := ForcingLocalNameTransport.bound_supported hM hp hG hHS hFixed ((ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound)
  have hv := (hVertices vertex).mpr ⟨_,_,_,hOldCode,hOldVertex⟩
  obtain ⟨a,hClass⟩ := ForcingOrbitQuotient.exists_class hM (env (rho 0)) (env I) (env mul) (env q) (env vertices) vertex
  have ha := (hQuotient a).mpr ⟨vertex,hv,hClass⟩
  have hIndex := (hProjection vertex a).mpr ⟨hv,hClass⟩
  obtain ⟨output,hOutput,_⟩ := hRecords.1.2 a ha
  obtain ⟨root,chain,hRootEdge,hChainEdge,hRecord⟩ := hRecords.2 a output hOutput
  obtain ⟨r,rootIndex,rootU,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,nonidentity,detectorDomain,detector,detectorSites,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hRecordCode,hRoot,hRootFiber,hData,hResult⟩ := hRecord
  have hFields : Fields env families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity (env high) detector patternOrder :=
    ForcingAssignedParameters.fields_of_record hRecords.1 hOutput hProjections hA hB hC hRecordCode
  obtain ⟨root0,hRoot0,hChain⟩ := hChains.2 a chain hChainEdge
  have eroot := ForcingConditionGraphs.function_unique hFunctions.1 hRoot0 hRootEdge
  subst root0
  obtain ⟨vertexLabels,hVertexFiber⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj ⟨_,_,_,hOldCode,hOldVertex⟩
  have hvSecond := (hVertices vertexSecond).mpr ⟨_,_,_,hOldCodeSecond,hOldVertexSecond⟩
  obtain ⟨aSecond,hClassSecond⟩ := ForcingOrbitQuotient.exists_class hM (env (rho 0)) (env I) (env mul) (env q) (env vertices) vertexSecond
  have haSecond := (hQuotient aSecond).mpr ⟨vertexSecond,hvSecond,hClassSecond⟩
  have hIndexSecond := (hProjection vertexSecond aSecond).mpr ⟨hvSecond,hClassSecond⟩
  obtain ⟨outputSecond,hOutputSecond,_⟩ := hRecords.1.2 aSecond haSecond
  obtain ⟨rootSecond,chainSecond,hRootEdgeSecond,hChainEdgeSecond,hRecordSecond⟩ := hRecords.2 aSecond outputSecond hOutputSecond
  obtain ⟨rSecond,rootIndexSecond,rootUSecond,labelSetSecond,codesSecond,orderSecond,groupSecond,supportSecond,fixingSecond,ranksSecond,selectionSecond,rankBoundSecond,tabSecond,germGroupSecond,quotientSecond,projectionSecond,repsSecond,nonidentitySecond,detectorDomainSecond,detectorSecond,detectorSitesSecond,patternCarrierSecond,patternOrderSecond,selectorDomainSecond,selectorSecond,packASecond,packBSecond,packCSecond,hASecond,hBSecond,hCSecond,hRecordCodeSecond,hRootSecond,hRootFiberSecond,hDataSecond,hResultSecond⟩ := hRecordSecond
  have hFieldsSecond : Fields env families aSecond rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond (env high) detectorSecond patternOrderSecond :=
    ForcingAssignedParameters.fields_of_record hRecords.1 hOutputSecond hProjections hASecond hBSecond hCSecond hRecordCodeSecond
  obtain ⟨root0Second,hRoot0Second,hChainSecond⟩ := hChains.2 aSecond chainSecond hChainEdgeSecond
  have erootSecond := ForcingConditionGraphs.function_unique hFunctions.1 hRoot0Second hRootEdgeSecond
  subst root0Second
  obtain ⟨vertexLabelsSecond,hVertexFiberSecond⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj ⟨_,_,_,hOldCodeSecond,hOldVertexSecond⟩
  obtain ⟨commonObjects,hTargetObjects,_⟩ := hObj.1.2 commonRoot ((hDiagrams commonRoot).mpr hStrong)
  obtain ⟨commonIndex,hCommonIndex,hCommonSub⟩ := ForcingDiagramPoset.le_trans hm hExtension ⟨oldIndex,hOldVertex.2.2.2.1,hOldVertex.2.1⟩
  let labelEnv : Fin (k+75) → M.Carrier .set := Fin.cases a (Fin.cases root (Fin.cases chain (Fin.cases r (Fin.cases rootIndex (Fin.cases rootU (Fin.cases labelSet (Fin.cases codes (Fin.cases order (Fin.cases group (Fin.cases support (Fin.cases fixing (Fin.cases ranks (Fin.cases selection (Fin.cases rankBound (Fin.cases tab (Fin.cases germGroup (Fin.cases quotient (Fin.cases projection (Fin.cases reps (Fin.cases nonidentity (Fin.cases detectorDomain (Fin.cases detector (Fin.cases detectorSites (Fin.cases patternCarrier (Fin.cases patternOrder (Fin.cases selectorDomain (Fin.cases selector (Fin.cases vertexLabels (Fin.cases aSecond (Fin.cases rootSecond (Fin.cases chainSecond (Fin.cases rSecond (Fin.cases rootIndexSecond (Fin.cases rootUSecond (Fin.cases labelSetSecond (Fin.cases codesSecond (Fin.cases orderSecond (Fin.cases groupSecond (Fin.cases supportSecond (Fin.cases fixingSecond (Fin.cases ranksSecond (Fin.cases selectionSecond (Fin.cases rankBoundSecond (Fin.cases tabSecond (Fin.cases germGroupSecond (Fin.cases quotientSecond (Fin.cases projectionSecond (Fin.cases repsSecond (Fin.cases nonidentitySecond (Fin.cases detectorDomainSecond (Fin.cases detectorSecond (Fin.cases detectorSitesSecond (Fin.cases patternCarrierSecond (Fin.cases patternOrderSecond (Fin.cases selectorDomainSecond (Fin.cases selectorSecond (Fin.cases vertexLabelsSecond (Fin.cases commonObjects (Fin.cases commonIndex (Fin.cases d (Fin.cases vertex (Fin.cases label (Fin.cases tau (Fin.cases e (Fin.cases vertexSecond (Fin.cases sigma (Fin.cases f (Fin.cases commonRoot (Fin.cases oldRoot (Fin.cases oldIndex (Fin.cases oldIdeal (Fin.cases oldRootSecond (Fin.cases oldIndexSecond (Fin.cases oldIdealSecond (env)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  let uplabelEnv : Fin k → Fin (k+75) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have helabelEnv (i : Fin k) : labelEnv (uplabelEnv i) = env i := rfl
  have hAssignedLabel := (ForcingAssigned.assigned_reindex hM env labelEnv uplabelEnv helabelEnv rho I G F mul q bound labels E w top K B zero Q families d vertex label tau).mpr h
  have hLabel := ForcingAssignedLaws.assigned_label hM labelEnv (fun j => uplabelEnv (rho j)) (uplabelEnv I) (uplabelEnv G) (uplabelEnv F) (uplabelEnv mul) (uplabelEnv q) (uplabelEnv bound) (uplabelEnv labels) (uplabelEnv E) 1 (uplabelEnv w) 2 7 8 12 13 (uplabelEnv top) 14 6 15 3 (uplabelEnv K) (uplabelEnv B) (uplabelEnv zero) 16 17 20 (uplabelEnv high) 22 25 (uplabelEnv one) (uplabelEnv vertices) (uplabelEnv diagrams) (uplabelEnv objImage) (uplabelEnv objects) (uplabelEnv arrows) (uplabelEnv mapImage) (uplabelEnv maps) 28 60 61 62 63 (uplabelEnv Q) (uplabelEnv pr) 0 (fun j => uplabelEnv (families j))
    hm hJ hw hChain hResult.1.1 hDiagrams hObj hObjects hArrows hMaps hMapFamily (ForcingLabelSystem.system_of_families hObj hObjects hMapFamily) hCommon hRootFiber hVertexFiber hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields hAssignedLabel
  have hCommonLabel := label_in_extension hObjects hVertexFiber hOldCode hTargetObjects hExtension hLabel
  obtain ⟨targetOne,targetLabels,hTarget,_,_⟩ := ForcingLabelVertices.construct hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hTargetObjects hCommonIndex hCommonSub hCommonLabel
  have hTargetCopy := hTarget
  obtain ⟨commonIdeal,hCode,_,_⟩ := hTargetCopy
  have hTarget' : ForcingLabelVertices.LabelVertex (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) commonRoot commonIndex label targetOne := hTarget
  let other : Fin (k+77) → M.Carrier .set := Fin.cases a (Fin.cases root (Fin.cases chain (Fin.cases r (Fin.cases rootIndex (Fin.cases rootU (Fin.cases labelSet (Fin.cases codes (Fin.cases order (Fin.cases group (Fin.cases support (Fin.cases fixing (Fin.cases ranks (Fin.cases selection (Fin.cases rankBound (Fin.cases tab (Fin.cases germGroup (Fin.cases quotient (Fin.cases projection (Fin.cases reps (Fin.cases nonidentity (Fin.cases detectorDomain (Fin.cases detector (Fin.cases detectorSites (Fin.cases patternCarrier (Fin.cases patternOrder (Fin.cases selectorDomain (Fin.cases selector (Fin.cases vertexLabels (Fin.cases aSecond (Fin.cases rootSecond (Fin.cases chainSecond (Fin.cases rSecond (Fin.cases rootIndexSecond (Fin.cases rootUSecond (Fin.cases labelSetSecond (Fin.cases codesSecond (Fin.cases orderSecond (Fin.cases groupSecond (Fin.cases supportSecond (Fin.cases fixingSecond (Fin.cases ranksSecond (Fin.cases selectionSecond (Fin.cases rankBoundSecond (Fin.cases tabSecond (Fin.cases germGroupSecond (Fin.cases quotientSecond (Fin.cases projectionSecond (Fin.cases repsSecond (Fin.cases nonidentitySecond (Fin.cases detectorDomainSecond (Fin.cases detectorSecond (Fin.cases detectorSitesSecond (Fin.cases patternCarrierSecond (Fin.cases patternOrderSecond (Fin.cases selectorDomainSecond (Fin.cases selectorSecond (Fin.cases vertexLabelsSecond (Fin.cases commonObjects (Fin.cases commonIndex (Fin.cases targetOne (Fin.cases commonIdeal (Fin.cases d (Fin.cases vertex (Fin.cases label (Fin.cases tau (Fin.cases e (Fin.cases vertexSecond (Fin.cases sigma (Fin.cases f (Fin.cases commonRoot (Fin.cases oldRoot (Fin.cases oldIndex (Fin.cases oldIdeal (Fin.cases oldRootSecond (Fin.cases oldIndexSecond (Fin.cases oldIdealSecond (env)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  let upother : Fin k → Fin (k+77) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have heother (i : Fin k) : other (upother i) = env i := rfl
  have hAssigned := (ForcingAssigned.assigned_reindex hM env other upother heother rho I G F mul q bound labels E w top K B zero Q families d vertex label tau).mpr h
  have hAssignedSecond := (ForcingAssigned.assigned_reindex hM env other upother heother rho I G F mul q bound labels E w top K B zero Q families e vertexSecond label sigma).mpr hSecond
  obtain ⟨hCarrier,hOrder,hGroup,_,_,_,_,_,_,_,hRanks,_,hFamily,hType,_,hTable⟩ := hData
  let rankEnv : Fin (k+8) → M.Carrier .set := Fin.cases order (Fin.cases codes (Fin.cases labelSet (Fin.cases rootU (Fin.cases rootIndex (Fin.cases r (Fin.cases chain (Fin.cases root (env))))))))
  let rankMap : Fin (k+8) → Fin (k+77) := Fin.cases (8) (Fin.cases (7) (Fin.cases (6) (Fin.cases (5) (Fin.cases (4) (Fin.cases (3) (Fin.cases (2) (Fin.cases (1) (upother))))))))
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
  have hSelector : ConstructionGermConditionSelector.Selector (env w) (env (rho 0)) chain germGroup quotient nonidentity (env K) (env (rho 1)) (env B) (env zero) (env high) detector patternOrder (env (rho 2)) selectorDomain selector := hResult.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSigmaName : ForcingNames.IsName (env (rho 6)) sigma := by
    obtain ⟨_,_,_,_,_,_,_,_,hLocal⟩ := hEntrySecond
    exact ForcingHS.isName hLocal.1.1
  have hOut := ForcingAssignedCompatibility.compatible_one hM hChoice other (fun j => upother (rho j)) (upother I) (upother K) (upother B) (upother w) (upother G) (upother F) (upother mul) (upother one) (upother mu) (upother history) (upother kappa) (upother mark) (upother H) (upother C) (upother incoming) (upother base) (upother q) (upother A) (upother Hq) (upother labelMap) (upother top) (upother bit) (upother labels) (upother E) (upother bound) (upother zero) 1 (upother vertices) 2 (upother names) 7 8 9 3 4 5 12 13 14 6 15 69 60 65 64 (upother diagrams) (upother objImage) (upother objects) (upother maps) 16 17 20 (upother high) 22 25 26 27 70 59 61 68 18 19 21 23 24 (upother Q) (upother pr) 0 62 63 (upother arrows) (upother mapImage) 28 58 71 72 73 30 31 36 37 41 42 43 35 44 32 45 46 49 (upother high) 51 54 33 34 47 48 50 52 53 55 56 66 67 29 57 60 74 75 76 (fun j => upother (families j))
    hK hResult hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hChain hCarrier hGroup hRoot hFamily hType hDiagrams hObj hObjects hCommon hRootFiber hSelector hOrder hOtherRanks hTable hCode hSigmaName hVertices hQuotient hProjection hReps hChains hFunctions hGerms hFields he hde hIndex hAssigned hArrows hMaps hMapFamily hVertexFiber hTargetObjects hTarget' hOldCode hOldVertex hExtension hChainSecond hRootSecond hResultSecond hdeSecond hIndexSecond hFieldsSecond hAssignedSecond hRootFiberSecond hVertexFiberSecond hTarget' hOldCodeSecond hOldVertexSecond hExtensionSecond
  change ForcingPrincipalFilter.EqF (orderFormula (upother (rho 0)) (upother mul)) other (env (rho 6)) f commonRoot tau sigma at hOut
  have hOrderRel (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (upother (rho 0)) (upother mul)) other x y ↔
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heother]
  simpa only [ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hOrderRel,heother] using hOut

/-- Pinned AssignedGraphs.graphRelation_one:109. Both dense witnesses and the
common genuine condition are produced here; compatibility is instantiated from
the actual common orbit records, and label equality uses actual separation. -/
theorem holds_one (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo : Fin k) (families : Fin 16 → Fin k)
    {p x y z : M.Carrier .set}
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
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
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
    (hUncountable : ¬ ForcingSupportSize.Small (env K) (env w))
    (hCoding : Injection (env K) (env groundValues) (env labelMap))
    (hLo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B))
    (hBit : (Project.FirstOrderSemantics.reduct M).mem (env bit) (env B))
    (hBits : env lo ≠ env bit)
    (h : ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y)
    (h' : ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x z) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y z p := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  apply ForcingAtomicBasic.eq_of_dense hM hpre h.1
  intro r hr hrp
  obtain ⟨s,hsr,d,v,j,tau,r1,i1,U1,c1,n1,hd,hcv,hv,hj,hEntry,hc1,hsc1,ha,hn1,hxj,hyt⟩ := h.2 r hr hrp
  have hs := ForcingAtomicBasic.condition hM hxj
  obtain ⟨t,hts,e,v2,j2,sigma,r2,i2,U2,c2,n2,he,hcv2,hv2,hj2,hEntry2,hc2,htc2,hb,hn2,hxj2,hzs⟩ := h'.2 s hs (hpre.2 s r p hs hr h.1 hsr hrp)
  have ht := ForcingAtomicBasic.condition hM hxj2
  obtain ⟨f,commonRoot,c,hf,hRoot,hc,hct⟩ := ForcingLabelDensity.exists_condition_below hM hp hm hq ht
  have hcW := ForcingSupportingRoot.code_mem hp hf hRoot hc
  have hct' := (orderFormula_semantics env (rho 0) mul c t).mpr hct
  have hcs := hpre.2 c t s hcW ht hs hct' hts
  have hc1W := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp hd) hv.1 hc1
  have hc2W := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 e).mp he) hv2.1 hc2
  have hb1 := (ForcingSupportingRoot.code_le hc hc1).mp ((orderFormula_semantics env (rho 0) mul c c1).mp (hpre.2 c s c1 hcW hs hc1W hcs hsc1))
  have hb2 := (ForcingSupportingRoot.code_le hc hc2).mp ((orderFormula_semantics env (rho 0) mul c c2).mp (hpre.2 c t c2 hcW ht hc2W hct' htc2))
  have hjEq : j = j2 := by
    apply Classical.byContradiction
    intro hne
    exact ForcingLabelSeparation.label_not_equal hM env rho mul hp hm hw hUncountable hCoding hTop hLo hBit hBits hq hj hj2 hne hn1 hn2
      (ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hcW hcs hxj)) (ForcingAtomicBasic.eq_mono hM hpre hcW hct' hxj2))
  subst j2
  have hCompat := compatible_one_from_records hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records families d v j tau e v2 sigma f commonRoot r1 i1 U1 r2 i2 U2
    hK hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains ((hp.2.2.1 f).mpr hf) hb1.1 ha hArrows hMaps hMapFamily hcv hv hb1.2 hb2.1 hb hcv2 hv2 hb2.2 hRecords hProjections hRoot hEntry2
  obtain ⟨c',hc',hEq⟩ := hCompat
  have hcc : c' = c := by
    obtain ⟨a,ha,hca⟩ := hc'
    obtain ⟨b,hb,hcb⟩ := hc
    have hab := KuratowskiZF.code_unique hM ha hb
    subst b
    exact ForcingWithTopCarrier.single_unique hM hca hcb
  subst c'
  exact ⟨c,hcW,hpre.2 c s r hcW hs hr hcs hsr,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hcW hcs hyt)
      (ForcingAtomicLaws.eq_trans hM hpre hEq (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hcW hct' hzs)))⟩

/-- Actual graph single-valuedness; all parameters belong to the SAME internal L. -/
def oneSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
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
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small K w)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection labelMap K groundValues))
    (.imp (.mem (.bound lo) (.bound B))
    (.imp (.mem (.bound bit) (.bound B))
    (.imp (.neg (Project.Formula.extensionalEq (.bound lo) (.bound bit)))
    (.imp (ForcingAssignedGraph.holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y)
    (.imp (ForcingAssignedGraph.holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x z)
    (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) y z p))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingOrbitParameterFamily.family_freeClosed,ForcingAssignedParameters.projections_freeClosed,ForcingAssignedGraph.holds_freeClosed,Project.Formula.extensionalEq]

theorem one_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,Project.Formula.satisfies_mem_iff,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingOrbitParameterFamily.family_semantics hM,ForcingAssignedParameters.projections_semantics hM,ForcingAssignedGraph.holds_semantics hM,ForcingAtomicRelations.forces_semantics (M := M),Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact holds_one hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo families

theorem one_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z families))) := by
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
  apply ConstructibleGround.relative_models hM (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z families)).mp
      (one_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo p x y z families hL hChoice)

end PPAC.Migration.ForcingAssignedGraphOne
