/- Fixed OrbitAssignments.component_difference:272 and orbitAssignment_eq_iff:282.
Align the two actual inverse orbit witnesses by their difference permutation;
consume existing component action and Corrected equality, preserving both directions. -/
import PPAC.Migration.ForcingOrbitAssignment
import PPAC.Migration.ForcingGermCorrectedEquality
import PPAC.Migration.ForcingGermCorrectedPermutation
import PPAC.Migration.ForcingGermEquality

namespace PPAC.Migration.ForcingOrbitEquality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment corrected_reindex)
open ForcingConditionGraphs (Permutation CompositionGraph function_input function_unique)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem component_difference (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q root diff source target : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiff : Permutation I diff) (hFix : CompositionGraph D diff q q)
    (hMove : ForcingComponentMove.Move D I mul q diff source target)
    (hTarget : ConstructionComponentCofinal.EncodedCommon D I mul q root target)
    (hSource : ConstructionComponentCofinal.EncodedCommon D I mul q root source) :
    ConstructionCountableAlignments.Stabilizes D I mul q root diff := by
  have hRoot : ConstructionComponentCarrier.EncodedVertex D I mul q root := by
    obtain ⟨r,a,U,s,b,V,hr,_,hv,_,_⟩ := hSource
    exact ⟨r,a,U,hr,hv⟩
  obtain ⟨movedRoot,hMovedRoot⟩ := ForcingComponentMove.exists_move hM hDiff hFix hRoot
  have hCommon := ForcingComponentMove.move_common hM hDiff hFix hMovedRoot hMove hSource
  exact ⟨hDiff,hFix,movedRoot,hMovedRoot,
    ForcingComponentGluing.common_between hM hm hJ (ForcingComponentRebase.common_symm hTarget)
      (ForcingComponentRebase.common_symm hCommon)⟩

theorem orbitAssignment_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier : Fin k)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
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
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hGroup : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) (env group))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env rootIndex) (env rootU))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hCommon : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hSelector : ConstructionGermConditionSelector.Selector (env w) (env (rho 0)) (env chain) (env germGroup) (env quotient) (env nonidentity) (env K) (env (rho 1)) (env B) (env zero) (env high) (env detector) (env patternOrder) (env (rho 2)) (env selectorDomain) (env selector))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) env (env codes) (env order) (env (rho 6)) (env ranks))
    (hTable : ForcingOrdinalTable.Table hM (env labelSet) (env rankBound) (env tab))
    (hCode : ConstructionComponentCarrier.Code (env vertex) (env localRoot) (env index) (env U))
    (hSigmaName : ForcingNames.IsName (env (rho 6)) (env sigma))
    (hA : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau))
    (hB : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env otherLabel) (env sigma)) :
    ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env localRoot) (env tau) (env sigma) ↔ env label = env otherLabel := by
  obtain ⟨pi,inv,act,ac,movedD,movedVertex,movedTau,movedLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,hMove,hTau,hk,hLabel,hCorrectedA⟩ := hA
  obtain ⟨s,sInv,sAct,sAc,oldD,oldVertex,oldSigma,oldLabel,hs,hsFix,hsInv,hsInverse,hsAct,hsCohen,hsdd,hsMove,hsSigma,hl,hsLabel,hCorrectedB⟩ := hB
  have hGerm := hResult.1.1
  have hCommonA := ForcingOrbitAssignment.corrected_common_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices movedD movedVertex movedLabel movedTau hm hJ hw hChain hGerm hCorrectedA
  have hCommonB := ForcingOrbitAssignment.corrected_common_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices oldD oldVertex oldLabel oldSigma hm hJ hw hChain hGerm hCorrectedB
  have hInvFix := ForcingDiagramCarrier.reverse hPi hq hInverse hFix
  obtain ⟨diff,hDiff,hProduct⟩ := ForcingConditionGraphs.exists_composition hM hInv hs
  have hDiffFix := ConstructionGermSeparation.compose_diagrams hq hProduct hsFix hInvFix
  have hSBack := ForcingComponentMove.move_inverse hsInv (fun x y => (hsInverse y x).symm) hsMove
  have hDiffMove := ConstructionGermSeparation.move_composition hProduct hSBack hMove
  have hDiffStab := component_difference hM hm hJ hDiff hDiffFix hDiffMove hCommonA hCommonB
  have hDiffGerm := (hGerm diff).mpr hDiffStab
  have hCancel : CompositionGraph (env I) diff sInv inv := by
    intro x z
    constructor
    · intro hxz
      have hx := function_input hInv.1.1 hxz
      obtain ⟨y,hxy,_⟩ := hsInv.1.1.2 x hx
      have hyx := (hsInverse y x).mpr hxy
      exact ⟨hx,y,hxy,(hProduct y z).mpr ⟨function_input hs.1.1 hyx,x,hyx,hxz⟩⟩
    · rintro ⟨_,y,hxy,hyz⟩
      obtain ⟨_,t,hyt,htz⟩ := (hProduct y z).mp hyz
      have htx := function_unique hs.1.1 hyt ((hsInverse y x).mpr hxy)
      exact htx ▸ htz
  obtain ⟨diffAct,hDiffAct⟩ := ForcingProductFamily.exists_action hM hp hDiff
  obtain ⟨diffAc,hDiffCohen⟩ := ForcingLocalTransport.part_of_action hDiffAct
  have hCancelCohen := ForcingAssignmentCosets.cohen_composition hM hp hsInv hCancel hDiffCohen hsCohen hCohen
  have hDiffD : PureKuratowski.PairMember M oldD movedD diffAc := by
    obtain ⟨_,mid,hMid,hOut⟩ := (hCancelCohen (env d) movedD).mp hdd
    exact (function_unique (ForcingLocalTransport.part_permutation hsCohen).1.1 hMid hsdd) ▸ hOut
  have hOtherI := hs.1.2 oldLabel (env otherLabel) hsLabel
  obtain ⟨movedOther,hOther,_⟩ := hInv.1.1.2 (env otherLabel) hOtherI
  have hDiffLabel := (hProduct oldLabel movedOther).mpr ⟨function_input hs.1.1 hsLabel,env otherLabel,hsLabel,hOther⟩
  obtain ⟨movedSigma,hDiffSigma⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hDiffAct).1 oldSigma
  have hCancelAct := ForcingProductFamily.multiplication hM hp hsInv hCancel hDiffAct hsAct hAct
  have hSigma := ForcingNameConjugacy.composition hM (ForcingProductFamily.action_permutation hDiffAct).1
    (ForcingProductFamily.action_permutation hsAct).1 hCancelAct hsSigma hDiffSigma
  have hMovedSigmaName := ForcingNameConjugacy.name_preservation hM (ForcingProductFamily.action_permutation hAct).1 hSigmaName hSigma
  obtain ⟨r0,a0,U0,movedRoot,hCode0,hMovedCode,hr0,hMovedRoot,hComp⟩ := hMove
  obtain ⟨er,_,_⟩ := ConstructionComponentCarrier.code_injective hCode0 hCode
  let other : Fin (k+17) → M.Carrier .set := Fin.cases diff (Fin.cases diffAct (Fin.cases diffAc (Fin.cases oldD (Fin.cases movedD (Fin.cases oldVertex (Fin.cases movedVertex (Fin.cases oldLabel (Fin.cases movedOther (Fin.cases oldSigma (Fin.cases movedSigma (Fin.cases movedLabel (Fin.cases movedTau (Fin.cases movedRoot (Fin.cases a0 (Fin.cases U0 (Fin.cases act (env)))))))))))))))))
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInputB := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder oldD oldVertex oldLabel oldSigma).mpr hCorrectedB
  have hAligned := ForcingGermCorrectedPermutation.corrected_permute hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order) (up ranks) (up selection) (up top) (up rankBound) (up labelSet) (up tab) (up r) (up K) (up B) (up zero) (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder) (up one) (up vertices) (up projection) (up reps) (up detectorDomain) (up detectorSites) (up patternCarrier) (up selectorDomain) (up selector) 0 1 2 3 4 5 6 7 8 9 10
    hw hm hJ hp hq hChain hK hResult hDiffGerm hDiffAct hDiffCohen hDiffD hDiffMove hDiffLabel hDiffSigma hInputB
  have hInputA := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder movedD movedVertex movedLabel movedTau).mpr hCorrectedA
  have hOtherRanks : ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order)) id (up (rho 0)) (up I) (up (rho 2)) (up w)) other (env codes) (env order) (env (rho 6)) (env ranks) := by
    simpa only [ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,
      ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,
      ForcingCodeSelection.mapRel_relation hM,id_eq,ForcingCodeRanks.selected_reindex env other up henv,henv] using hRanks
  have hEqCorrected := ForcingGermCorrectedEquality.corrected_eq_iff hM hChoice other (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up zero) (up root) (up vertices) (up chain) (up names) (up codes) (up order) (up group) (up r) (up rootIndex) (up rootU) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) 4 6 12 11 (up diagrams) (up objImage) (up objects) (up maps) (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder) (up selectorDomain) (up selector) 13 14 15 8 10
    hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hChain hCarrier hGroup hRoot hFamily hType hDiagrams hObj hObjects hCommon hRootFiber hSelector hOrder hOtherRanks hTable hMovedCode hMovedSigmaName hInputA hAligned
  have hOrderRel (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (up (rho 0)) (up mul)) other x y ↔
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,henv]
  have hReindex (dd rr tt ss : M.Carrier .set) :
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (up (rho 0)) (up mul)) other (env (rho 6)) dd rr tt ss ↔
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) dd rr tt ss := by
    simp only [ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hOrderRel]
  have hTransport := ForcingPersistentCovariance.eqF_transport_iff hM other (fun j => up (rho j)) (up mul) 16
    hm hp hInv hAct hCohen hdd hr0.1 hMovedRoot.1 hComp hTau hSigma
  have hSymmetry : ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) movedD movedRoot movedTau movedSigma ↔
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env localRoot) (env tau) (env sigma) := by
    simpa only [er] using (hReindex movedD movedRoot movedTau movedSigma).symm.trans
      (hTransport.trans (hReindex (env d) r0 (env tau) (env sigma)))
  have hLabelBack := (hInverse movedLabel (env label)).mp hLabel
  have hLabelsEqual : movedLabel = movedOther ↔ env label = env otherLabel := by
    constructor
    · intro hEq
      exact hInv.2.1 (env label) (env otherLabel) movedLabel hLabelBack (hEq.symm ▸ hOther)
    · intro hEq
      exact function_unique hInv.1.1 (hEq ▸ hLabelBack) hOther
  have hAlignedEq := (hReindex movedD movedRoot movedTau movedSigma).symm.trans hEqCorrected
  exact hSymmetry.symm.trans (hAlignedEq.trans hLabelsEqual)

def equalitySentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
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
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailGroup.tailGroup w (rho 0) G chain group)
    (.imp (ConstructionComponentCarrier.code root r rootIndex rootU)
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (ConstructionGermConditionSelector.selector w (rho 0) chain germGroup quotient nonidentity K (rho 1) B zero high detector patternOrder (rho 2) selectorDomain selector)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w) id codes order (rho 6) ranks))
    (.imp (ForcingOrdinalTable.table labelSet rankBound tab)
    (.imp (ConstructionComponentCarrier.code vertex localRoot index U)
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) sigma))
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex otherLabel sigma)
    (.iff (ForcingPrincipalFilter.eqF (ForcingProductSymmetry.orderFormula (rho 0) mul) id (rho 6) d localRoot tau sigma)
      (Project.Formula.extensionalEq (.bound label) (.bound otherLabel)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,
      ConstructionConcreteSelector.resultFormula_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,
      ConstructionGermConditionSelector.selector_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem equality_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ForcingTailGroup.tailGroup_semantics hM,
    ConstructionComponentCarrier.code_semantics hM,ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M),ForcingNames.isName_semantics (M := M),
    Project.Formula.satisfies_iff_iff,ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ConstructionGermConditionSelector.selector_semantics hM,ForcingOrbitAssignment.orbitAssignment_semantics hM,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact orbitAssignment_eq_iff hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier

theorem equality_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier))) := by
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
  apply ConstructibleGround.relative_models hM (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier)).mp
      (equality_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier hL hChoice)


end PPAC.Migration.ForcingOrbitEquality
