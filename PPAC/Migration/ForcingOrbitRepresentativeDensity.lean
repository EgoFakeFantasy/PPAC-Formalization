/- Fixed OrbitAssignments.assigned_total:479-489 and assigned_onto:498-508.
Use the actual quotient projection, the same representative and the same whole
orbit-chain function. All action witnesses are constructed internally; the exact
source full-root count premise discharges the nested inverse counts. -/
import PPAC.Migration.ForcingOrbitCounts
import PPAC.Migration.ForcingOrbitOnto
import PPAC.Migration.ForcingOrbitChains

namespace PPAC.Migration.ForcingOrbitRepresentativeDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingComponentFibers (VertexFiber)
open ForcingProductSymmetry (orderFormula)
open ForcingStableAt (StableAt stableAt)
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment)
open ForcingOrbitCounts (RootCounts rootCounts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem orbitAssignment_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (d vertex label tau : M.Carrier .set) :
    OrbitAssignment hM other (fun j => base (rho j)) (base I) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base root) (base w) (base chain) (base codes) (base order) (base ranks) (base selection) (base top) (base rankBound) (base labelSet) (base tab) (base r) (base K) (base B) (base zero) (base germGroup) (base quotient) (base nonidentity) (base high) (base detector) (base patternOrder) d vertex label tau ↔
    OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau := by
  simp only [OrbitAssignment,ForcingOrbitAssignment.corrected_reindex hM env other base he,
    he]

theorem representative_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env rootIndex) (env rootU))
    (hRootA : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env rootA))
    (hRootH : ForcingLabelPermutations.Fixing (env G) (env rootA) (env rootH))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env rootH) (env group))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hRank : ForcingRawRank.Rank (env selection) (env rankBound))
    (hTable : ForcingOrdinalTable.Table hM (env labelSet) (env rankBound) (env tab))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hj : (Project.FirstOrderSemantics.reduct M).mem (env label) (env vertexLabels))
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hSys : ForcingEligibleSystem.System (env (rho 0)) (env objects) (env maps))
    (hFibers : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hCount : RootCounts hM env rho I mul q w top selection r labelSet (env d))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env orbitQuotient))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env orbitProjection))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env orbitQuotient) (env orbitReps))
    (hRep : PureKuratowski.PairMember M (env orbitIndex) (env root) (env orbitReps))
    (hVertexIndex : PureKuratowski.PairMember M (env vertex) (env orbitIndex) (env orbitProjection))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env orbitQuotient) (env orbitReps) (env orbitChains))
    (hChainValue : PureKuratowski.PairMember M (env orbitIndex) (env chain) (env orbitChains))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertex) (env vertexLabels)) :
    ∃ e tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧
      ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) tau ∧
      OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder e (env vertex) (env label) tau := by
  obtain ⟨chosenRoot,hChosenRoot,hChosenChain⟩ := hChains.2 (env orbitIndex) (env chain) hChainValue
  have hRootEq := ForcingConditionGraphs.function_unique hReps.1.1 hChosenRoot hRep
  have hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain) := hRootEq ▸ hChosenChain
  have hRoundTrip := ForcingOrbitRepresentatives.representative_roundtrip hM hm hJ hq hVertices hQuotient hProjection hReps
  have hLaws := ForcingOrbitQuotient.quotient_laws hM hm hJ hq hVertices hProjection
  have hOrbit := (hLaws (env root) (env vertex) (env orbitIndex) (env orbitIndex) (hRoundTrip _ _ hRep) hVertexIndex).1.mp rfl
  obtain ⟨g,oldVertex,hg,hgFix,hMove,hCommon⟩ := hOrbit
  obtain ⟨outer,hOuter,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hg
  have hOuterFix := ForcingDiagramCarrier.reverse hg hq hInverse hgFix
  have hReverse : ForcingConditionGraphs.InverseGraph outer g := fun x y => (hInverse y x).symm
  obtain ⟨act,hAct⟩ := ForcingProductFamily.exists_action hM hp hg
  obtain ⟨ac,hCohen⟩ := ForcingLocalTransport.part_of_action hAct
  obtain ⟨oldD,hdd,_⟩ := (ForcingLocalTransport.part_permutation hCohen).1.1.2 (env d) ((hp.2.2.1 (env d)).mpr hd)
  let other : Fin (k+6) → M.Carrier .set := Fin.cases outer (Fin.cases g (Fin.cases act (Fin.cases ac (Fin.cases oldD (Fin.cases oldVertex env)))))
  let up : Fin k → Fin (k+6) := fun i => i.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hOtherRanks : ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order)) id (up (rho 0)) (up I) (up (rho 2)) (up w)) other (env codes) (env order) (env (rho 6)) (env ranks) := by
    simpa only [ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,
      ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,
      ForcingCodeSelection.mapRel_relation hM,id_eq,ForcingCodeRanks.selected_reindex env other up henv,henv] using hRanks
  have hOtherSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order)) id (up (rho 0)) (up I) (up (rho 2)) (up w))
      other (env codes) (env ranks) (env (rho 6)) (env selection) := by
    simpa only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,
      ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,
      ForcingCodeSelection.mapRel_relation hM,id_eq,ForcingCodeRanks.selected_reindex env other up henv,henv] using hSelection
  have hRootCount := (ForcingOrbitCounts.rootCounts_reindex hM env other up henv rho I mul q w top selection r labelSet (env d)).mpr hCount
  have hInverseCounts := ForcingOrbitCounts.inverseCounts_of_rootCounts hM other (fun j => up (rho j)) (up I) (up K) (up B) (up mul) (up q) (up w) (up top) (up selection) (up r) (up labelSet) (up root) (up germGroup) 1 3 (up d) 4 hp hq hResult.1.1 hg hgFix hCohen hdd hRootCount
  obtain ⟨e,tau,he,hde,hEntry,hAssignment⟩ := ForcingOrbitDensity.orbitAssignment_total_at hM hChoice other (fun j => up (rho j)) (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base) (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound) (up E) (up q) (up Aq) (up Hq) (up zero) (up root) (up vertices) (up chain) (up names) (up vertex) (up codes) (up order) (up ranks) (up selection) (up group) (up r) (up rootIndex) (up rootU) (up rootA) (up rootH) (up rankBound) (up labelSet) (up tab) (up label) (up d) (up germGroup) (up quotient) (up projection) (up reps) (up nonidentity) (up detectorDomain) (up detector) (up detectorSites) (up high) (up patternCarrier) (up patternOrder) (up selectorDomain) (up selector) (up diagrams) (up objImage) (up objects) (up arrows) (up mapImage) (up maps) 0 1 2 3 4 5 (up vertexLabels)
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hChain hCarrier hRoot hRootA hRootH hIncl hOrder hOtherRanks hOtherSelection hFamily hType hRank hTable hd hCommon hj hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hInverseCounts hOuter hOuterFix hg hReverse hAct hCohen hdd hMove hVertexFiber
  exact ⟨e,tau,he,hde,hEntry,(orbitAssignment_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder e (env vertex) (env label) tau).mp hAssignment⟩

def totalSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k) : Project.Sentence where
  formula :=
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ConstructionComponentCarrier.code root r rootIndex rootU)
    (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image r (rho 0) rootA))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G rootA rootH))
    (.imp (Project.Formula.subset (.bound rootH) (.bound group))
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ProjectSyntax.encode id (LayerRankSyntax.rank selection rankBound))
    (.imp (ForcingOrdinalTable.table labelSet rankBound tab)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (.mem (.bound label) (.bound vertexLabels))
    (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingEligibleSystem.system (rho 0) objects maps)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (rootCounts rho I mul q w top selection r labelSet d)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices orbitQuotient)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices orbitProjection)
    (.imp (ConstructionGermDetectors.representatives vertices orbitQuotient orbitReps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitReps orbitIndex root))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitProjection vertex orbitIndex))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices orbitQuotient orbitReps orbitChains)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitChains orbitIndex chain))
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (ForcingTailCodes.entry (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ bound.succ.succ vertex.succ.succ 0)
      (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (fun j => j.succ.succ) 1 vertex.succ.succ label.succ.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed,
      ForcingOrbitCounts.rootCounts_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed, ConstructionConcreteSelector.resultFormula_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem total_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,

    ForcingTailCodes.entry_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ForcingOrbitCounts.rootCounts_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,

    KuratowskiZF.source_edge,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,ForcingEligibleSystem.system_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ForcingOrbitAssignment.orbitAssignment_semantics hM]
  exact representative_total hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains

theorem total_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains))) := by
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
  apply ConstructibleGround.relative_models hM (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains)).mp
      (total_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitReps orbitIndex orbitChains hL hChoice)


theorem representative_onto (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env rootIndex) (env rootU))
    (hRootA : ForcingStabilizerTransport.Image (env r) (env (rho 0)) (env rootA))
    (hRootH : ForcingLabelPermutations.Fixing (env G) (env rootA) (env rootH))
    (hIncl : (Project.FirstOrderSemantics.reduct M).MemberSubset (env rootH) (env group))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hRank : ForcingRawRank.Rank (env selection) (env rankBound))
    (hTable : ForcingOrdinalTable.Table hM (env labelSet) (env rankBound) (env tab))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hSys : ForcingEligibleSystem.System (env (rho 0)) (env objects) (env maps))
    (hFibers : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hCount : RootCounts hM env rho I mul q w top selection r labelSet (env d))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env orbitQuotient))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env orbitProjection))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env orbitQuotient) (env orbitReps))
    (hRep : PureKuratowski.PairMember M (env orbitIndex) (env root) (env orbitReps))
    (hVertexIndex : PureKuratowski.PairMember M (env vertex) (env orbitIndex) (env orbitProjection))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env orbitQuotient) (env orbitReps) (env orbitChains))
    (hChainValue : PureKuratowski.PairMember M (env orbitIndex) (env chain) (env orbitChains))
    (hStable : StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) (env d) (env vertex) (env tau)) :
    ∃ e label, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧ (Project.FirstOrderSemantics.reduct M).mem label (env I) ∧
      OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder e (env vertex) label (env tau) := by
  obtain ⟨chosenRoot,hChosenRoot,hChosenChain⟩ := hChains.2 (env orbitIndex) (env chain) hChainValue
  have hRootEq := ForcingConditionGraphs.function_unique hReps.1.1 hChosenRoot hRep
  have hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain) := hRootEq ▸ hChosenChain
  have hRoundTrip := ForcingOrbitRepresentatives.representative_roundtrip hM hm hJ hq hVertices hQuotient hProjection hReps
  have hLaws := ForcingOrbitQuotient.quotient_laws hM hm hJ hq hVertices hProjection
  have hOrbit := (hLaws (env root) (env vertex) (env orbitIndex) (env orbitIndex) (hRoundTrip _ _ hRep) hVertexIndex).1.mp rfl
  obtain ⟨g,oldVertex,hg,hgFix,hMove,hCommon⟩ := hOrbit
  obtain ⟨outer,hOuter,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hg
  have hOuterFix := ForcingDiagramCarrier.reverse hg hq hInverse hgFix
  have hReverse : ForcingConditionGraphs.InverseGraph outer g := fun x y => (hInverse y x).symm
  obtain ⟨act,hAct⟩ := ForcingProductFamily.exists_action hM hp hg
  obtain ⟨ac,hCohen⟩ := ForcingLocalTransport.part_of_action hAct
  obtain ⟨oldD,hdd,_⟩ := (ForcingLocalTransport.part_permutation hCohen).1.1.2 (env d) ((hp.2.2.1 (env d)).mpr hd)
  let other : Fin (k+6) → M.Carrier .set := Fin.cases outer (Fin.cases g (Fin.cases act (Fin.cases ac (Fin.cases oldD (Fin.cases oldVertex env)))))
  let up : Fin k → Fin (k+6) := fun i => i.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hOtherRanks : ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order)) id (up (rho 0)) (up I) (up (rho 2)) (up w)) other (env codes) (env order) (env (rho 6)) (env ranks) := by
    simpa only [ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,
      ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,
      ForcingCodeSelection.mapRel_relation hM,id_eq,ForcingCodeRanks.selected_reindex env other up henv,henv] using hRanks
  have hOtherSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order)) id (up (rho 0)) (up I) (up (rho 2)) (up w))
      other (env codes) (env ranks) (env (rho 6)) (env selection) := by
    simpa only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,
      ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,
      ForcingCodeSelection.mapRel_relation hM,id_eq,ForcingCodeRanks.selected_reindex env other up henv,henv] using hSelection
  have hRootCount := (ForcingOrbitCounts.rootCounts_reindex hM env other up henv rho I mul q w top selection r labelSet (env d)).mpr hCount
  have hInverseCounts := ForcingOrbitCounts.inverseCounts_of_rootCounts hM other (fun j => up (rho j)) (up I) (up K) (up B) (up mul) (up q) (up w) (up top) (up selection) (up r) (up labelSet) (up root) (up germGroup) 1 3 (up d) 4 hp hq hResult.1.1 hg hgFix hCohen hdd hRootCount
  have hStableInput := (ForcingGermCorrectedStable.stable_reindex env other up henv rho G F mul bound labels E (env d) (env vertex) (env tau)).mpr hStable
  obtain ⟨e,label,he,hde,hLabel,hAssignment⟩ := ForcingOrbitOnto.orbitAssignment_onto_at hM hChoice other (fun j => up (rho j)) (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base) (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound) (up E) (up q) (up Aq) (up Hq) (up zero) (up root) (up vertices) (up chain) (up names) (up vertex) (up codes) (up order) (up ranks) (up selection) (up group) (up r) (up rootIndex) (up rootU) (up rootA) (up rootH) (up rankBound) (up labelSet) (up tab) (up tau) (up d) (up germGroup) (up quotient) (up projection) (up reps) (up nonidentity) (up detectorDomain) (up detector) (up detectorSites) (up high) (up patternCarrier) (up patternOrder) (up selectorDomain) (up selector) (up diagrams) (up objImage) (up objects) (up arrows) (up mapImage) (up maps) 0 1 2 3 4 5
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hNames hVertices hChain hCarrier hRoot hRootA hRootH hIncl hOrder hOtherRanks hOtherSelection hFamily hType hRank hTable hd hCommon hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hInverseCounts hOuter hOuterFix hg hReverse hAct hCohen hdd hMove hStableInput
  exact ⟨e,label,he,hde,hLabel,(orbitAssignment_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder e (env vertex) label (env tau)).mp hAssignment⟩

def ontoSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k) : Project.Sentence where
  formula :=
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ConstructionComponentCarrier.code root r rootIndex rootU)
    (.imp (ProjectSyntax.encode id (ForcingStabilizerTransport.image r (rho 0) rootA))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G rootA rootH))
    (.imp (Project.Formula.subset (.bound rootH) (.bound group))
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ProjectSyntax.encode id (LayerRankSyntax.rank selection rankBound))
    (.imp (ForcingOrdinalTable.table labelSet rankBound tab)
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingEligibleSystem.system (rho 0) objects maps)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (rootCounts rho I mul q w top selection r labelSet d)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices orbitQuotient)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices orbitProjection)
    (.imp (ConstructionGermDetectors.representatives vertices orbitQuotient orbitReps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitReps orbitIndex root))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitProjection vertex orbitIndex))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices orbitQuotient orbitReps orbitChains)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitChains orbitIndex chain))
    (.imp (stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul bound labels E d vertex tau)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (.mem (.bound 0) (.bound I.succ.succ))
      (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (fun j => j.succ.succ) 1 vertex.succ.succ 0 tau.succ.succ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.candidates_freeClosed,ForcingStableAt.stableAt_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed,
      ForcingOrbitCounts.rootCounts_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed, ConstructionConcreteSelector.resultFormula_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem onto_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,

    ForcingTailCodes.candidates_semantics hM,ForcingStableAt.stableAt_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ForcingOrbitCounts.rootCounts_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,

    KuratowskiZF.source_edge,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,ForcingEligibleSystem.system_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ForcingOrbitAssignment.orbitAssignment_semantics hM]
  exact representative_onto hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains

theorem onto_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains))) := by
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
  apply ConstructibleGround.relative_models hM (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains)).mp
      (onto_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitReps orbitIndex orbitChains hL hChoice)


end PPAC.Migration.ForcingOrbitRepresentativeDensity
