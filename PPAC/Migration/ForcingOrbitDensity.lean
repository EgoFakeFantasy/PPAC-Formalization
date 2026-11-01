/- Pinned OrbitAssignments.orbitAssignment_total_at:333-358.
Move the actual label and condition to the representative component, consume
corrected_total, then transport the same local name back to the original vertex. -/
import PPAC.Migration.ForcingOrbitAssignment

namespace PPAC.Migration.ForcingOrbitDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingComponentFibers (VertexFiber)
open ConstructionComponentCofinal (EncodedCommon Chain)
open ForcingProductSymmetry (orderFormula)
open ForcingGermDensity (OrdinalCount)
open ForcingGermCorrectedDensity (InverseCounts inverseCounts)
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment corrected_reindex)
open ForcingGermCorrected (Corrected corrected)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem inverseCounts_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i) (rho : Fin 7 → Fin k)
    (I mul w top selection r labelSet germGroup : Fin k) (d : M.Carrier .set) :
    InverseCounts hM other (fun j => base (rho j)) (base I) (base mul) (base w) (base top)
      (base selection) (base r) (base labelSet) (base germGroup) d ↔
    InverseCounts hM env rho I mul w top selection r labelSet germGroup d := by
  have hR (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (base (rho 0)) (base mul)) other x y ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  simp only [InverseCounts,OrdinalCount,ForcingPrincipalFilter.EqF,
    ForcingEquivariantMix.forces_order_congr hR,he]

theorem orbitAssignment_total_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels : Fin k)
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
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
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
    (_hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hCommon : EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env oldVertex))
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
    (hCount : InverseCounts hM env rho I mul w top selection r labelSet germGroup (env oldD))
    (hg : Permutation (env I) (env g))
    (hgFix : CompositionGraph (env (rho 0)) (env g) (env q) (env q))
    (hInv : Permutation (env I) (env inv))
    (hInverse : ForcingConditionGraphs.InverseGraph (env g) (env inv))
    (hAct : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) (env inv) (env act))
    (hCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env inv) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env oldD) (env ac))
    (hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env inv) (env vertex) (env oldVertex))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertex) (env vertexLabels)) :
    ∃ e tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧
      ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) tau ∧
      OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder e (env vertex) (env label) tau := by
  have hLabelI : (Project.FirstOrderSemantics.reduct M).mem (env label) (env I) := by
    obtain ⟨s,a,U,Os,hCode,hs,hFiber⟩ := hVertexFiber
    obtain ⟨n,_,hn⟩ := (((hObjects s Os).mp hs).2 (env label)).mp ((hFiber (env label)).mp hj).1
    exact ((hDiagrams s).mp (ForcingConditionGraphs.function_input hObj.1 hs)).1.2 n (env label) hn
  obtain ⟨oldLabel,hLabel,_⟩ := hInv.1.1.2 (env label) hLabelI
  obtain ⟨oldFiber,hOldFiber⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj
    (ForcingComponentMove.target_vertex hMove)
  have hMovedLabel := ForcingGermCorrectedDensity.label_move hM hm hInv hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hMove hVertexFiber hOldFiber hj hLabel
  have hFiberEq := hFibers (env q) (env root) (env oldVertex) (env labelSet) oldFiber hCommon hRootFiber hOldFiber
  have hOldLabel : (Project.FirstOrderSemantics.reduct M).mem oldLabel (env labelSet) := hFiberEq.symm ▸ hMovedLabel
  have hOldD := (hp.2.2.1 (env oldD)).mp ((ForcingLocalTransport.part_permutation hCohen).1.2 (env d) (env oldD) hdd)
  let other : Fin (k+1) → M.Carrier .set := Fin.cases oldLabel env
  let up : Fin k → Fin (k+1) := Fin.succ
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
  have hOtherCount := (inverseCounts_reindex hM env other up henv rho I mul w top selection r labelSet germGroup (env oldD)).mpr hCount
  obtain ⟨f,tau,hf,hdf,hEntry,hCorrected⟩ := ForcingGermCorrectedDensity.corrected_total hM hChoice other (fun j => up (rho j)) (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base) (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound) (up E) (up q) (up Aq) (up Hq) (up zero) (up root) (up vertices) (up chain) (up names) (up oldVertex) (up codes) (up order) (up ranks) (up selection) (up group) (up r) (up rootIndex) (up rootU) (up rootA) (up rootH) (up rankBound) (up labelSet) (up tab) 0 (up oldD) (up germGroup) (up quotient) (up projection) (up reps) (up nonidentity) (up detectorDomain) (up detector) (up detectorSites) (up high) (up patternCarrier) (up patternOrder) (up selectorDomain) (up selector) (up diagrams) (up objImage) (up objects) (up arrows) (up mapImage) (up maps)
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hChain hCarrier hRoot hRootA hRootH hIncl hOrder hOtherRanks hOtherSelection hFamily hType hRank hTable hOldD hCommon hOldLabel hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hOtherCount
  have hCorrectedOld := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder f (env oldVertex) oldLabel tau).mp hCorrected
  obtain ⟨forward,hForward⟩ := ForcingProductFamily.exists_action hM hp hg
  obtain ⟨fc,hForwardCohen⟩ := ForcingLocalTransport.part_of_action hForward
  have hfc := ForcingLocalTransport.part_permutation hForwardCohen
  obtain ⟨e,hfe,_⟩ := hfc.1.1.2 f ((hp.2.2.1 f).mpr hf)
  have he := (hp.2.2.1 e).mp (hfc.1.2 f e hfe)
  have hReverse : ForcingConditionGraphs.InverseGraph (env inv) (env g) := fun x y => (hInverse y x).symm
  have hBackD := ForcingAssignmentInvariant.cohen_inverse hp hReverse hCohen hForwardCohen hdd
  have hForwardOrder : ForcingCohenOrderAction.OrderPreserving fc := by
    obtain ⟨_,_,_,_,ht,_,_,hGraph⟩ := hForwardCohen
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  have hde := (hForwardOrder f (env oldD) e (env d) hfe hBackD).mpr hdf
  have hBackE := ForcingAssignmentInvariant.cohen_inverse hp hInverse hForwardCohen hCohen hfe
  have hBackMove := ForcingComponentMove.move_inverse hInv hReverse hMove
  obtain ⟨s,a,U,A,Hfix,hCode,hRange,hFixing,hLocal⟩ := hEntry
  obtain ⟨sigma,hTau⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hForward).1 tau
  obtain ⟨conj,hConjPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hg hInv hInverse
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env g) (env inv) conj forward (env act) :=
    ⟨hp,hG,hg,hInv,hInverse,hConjPerm,hConj,hForward,hAct,hF⟩
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hOmegaSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  obtain ⟨hLabelsHS,hLabelsFix⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hOmegaSmall hLabelMap hTop hLabels
  have hBound := ForcingLocalNameTransport.bound_supported hM hp hG hLabelsHS hLabelsFix ((ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound)
  obtain ⟨s0,a0,U0,R,hCode0,hNewCode,hs,hR,hComp⟩ := hBackMove
  obtain ⟨es,ea,eU⟩ := ConstructionComponentCarrier.code_injective hCode hCode0
  subst s0; subst a0; subst U0
  obtain ⟨newRange,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM hg.1 (J := A)
  obtain ⟨newFix,hNewFix⟩ := ForcingLabelPermutations.exists_fixing hM (env G) newRange
  have hNewRange := ForcingLocalNameTransport.range_image hRange hComp hImage
  have hNewLocal := ForcingLocalNameTransport.local_name_move hM hData hBound (ForcingTailGroup.range_subset hs.1 hRange) hImage hFixing hNewFix hLocal hTau
  have hInverseAction := ForcingProductCovariance.inverse hM hp hg hInverse hForward hAct
  have hBackTau := ForcingNameConjugacy.inverse_action hM (ForcingProductFamily.action_permutation hForward).1 (ForcingProductFamily.action_permutation hAct).1 hInverseAction (ForcingHS.isName hLocal.1.1) hTau
  exact ⟨e,sigma,he,hde,
    ⟨R,a,U,newRange,newFix,hNewCode,hNewRange,hNewFix,hNewLocal⟩,
    env g,env inv,env act,env ac,f,env oldVertex,tau,oldLabel,
    hg,hgFix,hInv,hInverse,hAct,hCohen,hBackE,hMove,hBackTau,hOldLabel,
    (hInverse oldLabel (env label)).mpr hLabel,hCorrectedOld⟩

def totalSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels : Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
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
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root oldVertex)
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
    (.imp (inverseCounts rho I mul w top selection r labelSet germGroup oldD)
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I g))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) g q q))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I inv))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph g inv))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) inv act))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) inv ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d oldD))
    (.imp (ForcingComponentMove.move (rho 0) I mul q inv vertex oldVertex)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (ForcingTailCodes.entry (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ bound.succ.succ vertex.succ.succ 0)
      (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (fun j => j.succ.succ) 1 vertex.succ.succ label.succ.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed,
      ForcingGermCorrectedDensity.inverseCounts_freeClosed,ForcingComponentMove.move_freeClosed, ConstructionConcreteSelector.resultFormula_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem total_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels)).TrueIn M := by
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
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    ForcingTailCodes.entry_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ForcingGermCorrectedDensity.inverseCounts_semantics hM,
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ForcingProductFamily.action_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),KuratowskiZF.source_edge,ForcingComponentMove.move_semantics hM,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,ForcingEligibleSystem.system_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ForcingOrbitAssignment.orbitAssignment_semantics hM]
  exact orbitAssignment_total_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels

theorem total_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels))) := by
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
  apply ConstructibleGround.relative_models hM (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels)).mp
      (total_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps g inv act ac oldD oldVertex vertexLabels hL hChoice)


end PPAC.Migration.ForcingOrbitDensity
