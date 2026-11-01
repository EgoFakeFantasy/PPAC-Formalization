/- Fixed AssignedGraphs.graphRelation_total:189. Consume actual whole-orbit
records, existing assigned_total and diagram coverage. The source all-orbit
count hypothesis is an explicit internal formula over the SAME field family. -/
import PPAC.Migration.ForcingAssignedDensity
import PPAC.Migration.ForcingAssignedGraphBounds
import PPAC.Migration.ConstructionDiagramCoverage
import PPAC.Migration.ForcingAssignedParameters
import PPAC.Migration.ForcingAssignedGraph
import PPAC.Migration.ForcingLabelDensity

namespace PPAC.Migration.ForcingAssignedGraphTotal
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

def AllCounts (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I mul q w top Q d0 : Fin k)
    (families : Fin 16 → Fin k) : Prop :=
  ∀ d a selection r labelSet,
    ForcingCohenConditions.Condition (env (rho 2)) (env w) d →
    ForcingPowerName.Subset (env d0) d →
    (Project.FirstOrderSemantics.reduct M).mem a (env Q) →
    PureKuratowski.PairMember M a selection (env (families 5)) →
    PureKuratowski.PairMember M a r (env (families 9)) →
    PureKuratowski.PairMember M a labelSet (env (families 7)) →
    ForcingOrbitCounts.RootCounts hM
      (Fin.cases labelSet (Fin.cases r (Fin.cases selection (Fin.cases a (Fin.cases d env)))))
      (fun j => (rho j).succ.succ.succ.succ.succ) I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ
      q.succ.succ.succ.succ.succ w.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ 2 1 0 d

def allCounts {k : Nat} (rho : Fin 7 → Fin k) (I mul q w top Q d0 : Fin k)
    (families : Fin 16 → Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  .forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (rho 2)) (up w) 4))
    (.imp (Project.Formula.subset (.bound (up d0)) (.bound 4))
    (.imp (.mem (.bound 3) (.bound (up Q)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up (families 5)) 3 2))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up (families 9)) 3 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up (families 7)) 3 0))
      (ForcingOrbitCounts.rootCounts (fun j => up (rho j)) (up I) (up mul) (up q) (up w) (up top) 2 1 0 4)))))))))))

theorem allCounts_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (I mul q w top Q d0 : Fin k)
    (families : Fin 16 → Fin k) : (allCounts rho I mul q w top Q d0 families).FreeClosed := by
  simp -implicitDefEqProofs [allCounts,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,ForcingOrbitCounts.rootCounts_freeClosed]

theorem allCounts_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k)
    (I mul q w top Q d0 : Fin k) (families : Fin 16 → Fin k) :
    Project.Formula.satisfies env (allCounts rho I mul q w top Q d0 families) ↔
      AllCounts hM env.bound rho I mul q w top Q d0 families := by
  simp only [allCounts,AllCounts,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenConditions.condition_semantics (M := M),KuratowskiZF.source_edge,ForcingOrbitCounts.rootCounts_semantics hM]
  rfl

private theorem total_from_records (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 : Fin k) (families : Fin 16 → Fin k)
    (d vertex label vertexLabels : M.Carrier .set)
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
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) vertex vertexLabels)
    (hj : (Project.FirstOrderSemantics.reduct M).mem label vertexLabels) :
    ∃ e tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧ ForcingPowerName.Subset d e ∧
      ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertex tau ∧
      Assigned hM env rho I G F mul q bound labels E w top K B zero Q families e vertex label tau := by
  obtain ⟨a,hClass⟩ := ForcingOrbitQuotient.exists_class hM (env (rho 0)) (env I) (env mul) (env q) (env vertices) vertex
  have ha := (hQuotient a).mpr ⟨vertex,hv,hClass⟩
  have hIndex := (hProjection vertex a).mpr ⟨hv,hClass⟩
  obtain ⟨output,hOutput,_⟩ := hRecords.1.2 a ha
  obtain ⟨root,chain,hRootEdge,hChainEdge,hRecord⟩ := hRecords.2 a output hOutput
  obtain ⟨r,rootIndex,rootU,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,nonidentity,detectorDomain,detector,detectorSites,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hRecordCode,hRoot,hRootFiber,hData,hResult⟩ := hRecord
  have hFields : Fields env families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity (env high) detector patternOrder :=
    ForcingAssignedParameters.fields_of_record hRecords.1 hOutput hProjections hA hB hC hRecordCode
  let other : Fin (k+32) → M.Carrier .set := Fin.cases a (Fin.cases root (Fin.cases chain (Fin.cases r (Fin.cases rootIndex (Fin.cases rootU (Fin.cases labelSet (Fin.cases codes (Fin.cases order (Fin.cases group (Fin.cases support (Fin.cases fixing (Fin.cases ranks (Fin.cases selection (Fin.cases rankBound (Fin.cases tab (Fin.cases germGroup (Fin.cases quotient (Fin.cases projection (Fin.cases reps (Fin.cases nonidentity (Fin.cases detectorDomain (Fin.cases detector (Fin.cases detectorSites (Fin.cases patternCarrier (Fin.cases patternOrder (Fin.cases selectorDomain (Fin.cases selector (Fin.cases vertexLabels (Fin.cases d (Fin.cases vertex (Fin.cases label (env))))))))))))))))))))))))))))))))
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
  obtain ⟨e,tau,he,hde,hEntry,hAssigned⟩ := ForcingAssignedDensity.assigned_total hM hChoice other (fun j => upother (rho j)) (upother w) (upother mu) (upother history) (upother kappa) (upother one) (upother mark) (upother H) (upother C) (upother incoming) (upother base) (upother I) (upother K) (upother B) (upother G) (upother F) (upother mul) (upother labelMap) (upother top) (upother bit) (upother labels) (upother bound) (upother E) (upother q) (upother A) (upother Hq) (upother zero) 1 (upother vertices) 2 (upother names) 30 7 8 12 13 9 3 4 5 10 11 14 6 15 31 29 16 17 18 19 20 21 22 23 (upother high) 24 25 26 27 (upother diagrams) (upother objImage) (upother objects) (upother arrows) (upother mapImage) (upother maps) 28 (upother Q) (upother pr) 0 (fun j => upother (families j))
    hw hMu hI hSmallD hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hOtherRanks hOtherSelection hFamily hType hRank hTable hd hj hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily (ForcingLabelSystem.system_of_families hObj hObjects hMapFamily) hCommon hRootFiber hOtherCount hQuotient hProjection hReps hIndex hChains hFields hVertexFiber
  exact ⟨e,tau,he,hde,hEntry,(ForcingAssigned.assigned_reindex hM env other upother heother rho I G F mul q bound labels E w top K B zero Q families e vertex label tau).mp hAssigned⟩

theorem holds_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 : Fin k) (families : Fin 16 → Fin k)
    {p x : M.Carrier .set}
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
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d0))
    (hz0 : ForcingSupportingRoot.Code (env z0) (env d0) (env q))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env name))
    (hp0 : MapRel (orderFormula (rho 0) mul) env p (env z0))
    (hx : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env labels) p) :
    ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env r p →
      ∃ s, (Project.FirstOrderSemantics.reduct M).mem s (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env s r ∧
        ∃ y, ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y ∧
          Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env name) s ∧
          ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families s x y := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hpW := ForcingAtomicBasic.condition hM hx
  have hz0W := ForcingSupportingRoot.code_mem hp hd0 hq hz0
  have htW := (hp.2.2.2.2.2 (env top)).mpr (Or.inl hTop)
  have htop (s : M.Carrier .set) (_ : (Project.FirstOrderSemantics.reduct M).mem s (env (rho 6))) : MapRel (orderFormula (rho 0) mul) env s (env top) :=
    (orderFormula_semantics env (rho 0) mul s (env top)).mpr (Or.inl hTop)
  have hSmall : ForcingSupportSize.Small (env w) (env mu) := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  have hLarge : ¬ ForcingSupportSize.Small (env I) (env mu) := by
    intro hsmall
    exact hI.not_cardinalLessOrEqual (SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) ((ForcingSupportSize.native_small hM (env I) (env mu)).mp hsmall)
  intro r hr hrp
  obtain ⟨s,j,n,hs,hsr,hj,hn,hxj⟩ := ((ForcingLabelDensity.mem_labelSet hM (orderFormula (rho 0) mul) env hLabels hpW htW htop).mp hx) r hr hrp
  obtain ⟨d,root,c,hd,hRoot,hc,hcs⟩ := ForcingLabelDensity.exists_condition_below hM hp hm hq hs
  have hcW := ForcingSupportingRoot.code_mem hp hd hRoot hc
  have hcs' := (orderFormula_semantics env (rho 0) mul c s).mpr hcs
  have hcz0 := hpre.2 c s (env z0) hcW hs hz0W hcs' (hpre.2 s r (env z0) hs hr hz0W hsr (hpre.2 r p (env z0) hr hpW hz0W hrp hp0))
  have hBase := (ForcingSupportingRoot.code_le hc hz0).mp ((orderFormula_semantics env (rho 0) mul c (env z0)).mp hcz0)
  obtain ⟨single,hSingle⟩ := ForcingWithTopCarrier.exists_single hM j
  have hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset single (env I) := fun y hy => ((hSingle y).mp hy).symm ▸ hj
  have hJmu := ForcingLabelNames.singleton_small hM hw hSmall hSingle
  obtain ⟨t,ht,hSub,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard (hm.2.1 (env mark) hMark) hRoot hJI hJmu
  have htr : ForcingDiagramOrder.Le (env (rho 0)) (env mul) t root := ⟨env mark,hMark,hSub⟩
  obtain ⟨index,hIndex,hSubq⟩ := ForcingDiagramPoset.le_trans hm htr hBase.2
  obtain ⟨objectsT,hObjectsT,_⟩ := hObj.1.2 t ((hDiagrams t).mpr ht)
  have hjT := (((hObjects t objectsT).mp hObjectsT).2 j).mpr (hCover j ((hSingle j).mpr rfl))
  obtain ⟨vertex,vertexLabels,hLabelVertex,hVertexFiber,hLabelMem⟩ := ForcingLabelVertices.construct hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hObjectsT hIndex hSubq hjT
  obtain ⟨ideal,hCode,hVertex,_⟩ := hLabelVertex
  have hv := (hVertices vertex).mpr ⟨t,index,ideal,hCode,hVertex⟩
  obtain ⟨e,tau,he,hde,hEntry,hAssigned⟩ := total_from_records hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 families d vertex j vertexLabels
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hd hBase.1 hv hVertexFiber hLabelMem
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM e t
  have hzW := ForcingSupportingRoot.code_mem hp he ht hz
  have hzc := (orderFormula_semantics env (rho 0) mul z c).mpr ((ForcingSupportingRoot.code_le hz hc).mpr ⟨hde,htr⟩)
  have hzs := hpre.2 z c s hzW hcW hs hzc hcs'
  have hWitness : ForcingAssignedGraph.Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families z x tau :=
    ⟨e,vertex,j,tau,t,index,ideal,z,n,(hp.2.2.1 e).mpr he,hCode,hVertex,hj,hEntry,hz,hpre.1 z hzW,hAssigned,hn,ForcingAtomicBasic.eq_mono hM hpre hzW hzs hxj,ForcingAtomicBasic.eq_refl hM hpre tau z hzW⟩
  have hBounds := ForcingAssignedGraphBounds.witness_bounds hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q A Hq zero vertices names Q high objects maps records families
    hw hMu hI hSmallD hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hRecords hProjections hChains hEHS hName hWitness
  have hHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) tau := by
    obtain ⟨_,_,_,_,_,_,_,_,hLocal⟩ := hEntry
    exact hLocal.1.1
  exact ⟨z,hzW,hpre.2 z s r hzW hs hr hzs hsr,tau,hHS,hBounds.2,ForcingAssignedGraph.witness_holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp hWitness⟩

/-- Source dense totality for the actual graph, with every output in HS. -/
def totalSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (.mem (.bound mark) (.bound (rho 0)))
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 q))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingQuotientName.quotient rho G F mul I K labelMap top bit labels E id name))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) id p z0))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x labels p))
    (.forallE (.imp (.mem (.bound 0) (.bound ((rho 6).succ)))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => i.succ) 0 p.succ))
      (.existsE (.conj (.mem (.bound 0) (.bound ((rho 6).succ.succ)))
        (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => i.succ.succ) 0 1))
          (.existsE (.conj (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula (fun j => (rho j).succ.succ.succ) G.succ.succ.succ (rho 6).succ.succ.succ F.succ.succ.succ 0))
            (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) (fun i => i.succ.succ.succ) (rho 6).succ.succ.succ 0 name.succ.succ.succ 1))
              (ForcingAssignedGraph.holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun i => i.succ.succ.succ) 1 x.succ.succ.succ 0)))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingOrbitParameterFamily.family_freeClosed,ForcingAssignedParameters.projections_freeClosed,ForcingAssignedGraph.holds_freeClosed,allCounts_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed]

theorem total_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (totalSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingOrbitParameterFamily.family_semantics hM,ForcingAssignedParameters.projections_semantics hM,ForcingAssignedGraph.holds_semantics hM,ForcingAtomicRelations.forces_semantics (M := M),allCounts_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),ForcingHS.hs_semantics (M := M),ForcingQuotientName.quotient_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,id_eq]
  exact holds_total hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 families

theorem total_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (totalSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x families))) := by
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
  apply ConstructibleGround.relative_models hM (totalSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (totalSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x families)).mp
      (total_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 p x families hL hChoice)


end PPAC.Migration.ForcingAssignedGraphTotal
