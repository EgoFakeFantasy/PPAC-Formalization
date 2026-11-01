/- Fixed OrbitAssignments.assigned_compatible_one/inj:597-630.
Keep both actual source vertices, their own orbit records, the common stronger
condition and the literal label-availability vertices. Consume existing native
Assigned extension/equality/ideal and forcedAvailability_congr. -/
import PPAC.Migration.ForcingAssignedExtension
import PPAC.Migration.ForcingAssignedEquality
import PPAC.Migration.ForcingAssignedIdeal
import PPAC.Migration.ForcingForcedAvailabilityCongruence

namespace PPAC.Migration.ForcingAssignedCompatibility
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingAssigned (Assigned assigned Fields Functions Germs fields functions germs assigned_freeClosed functions_freeClosed germs_freeClosed fields_freeClosed assigned_semantics functions_semantics germs_semantics fields_semantics)
open ConstructionComponentCofinal (Chain)
open ForcingTailCodes (Entry)
open ForcingSupportSize (MapsTo Injection)
open ForcingComponentFibers (VertexFiber)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- An actual arrow transports the original orbit projection; no new field equality premise. -/
theorem projection_at_arrow (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q vertices pr source target n a : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hq : Injection D I q)
    (hVertices : ConstructionComponentCarrier.Carrier D I mul q vertices)
    (hPr : ForcingOrbitQuotient.Projection D I mul q vertices pr)
    (hArrow : ConstructionComponentCofinal.EncodedArrow D I mul q source target n)
    (hIndex : PureKuratowski.PairMember M target a pr) :
    PureKuratowski.PairMember M source a pr := by
  obtain ⟨r,i,U,s,j,V,hSource,hTarget,hSourceV,hTargetV,hArrow⟩ := hArrow
  have hCommon : ConstructionComponentCofinal.EncodedCommon D I mul q source target :=
    ⟨r,i,U,s,j,V,hSource,hTarget,hSourceV,hTargetV,
      ConstructionComponentVertices.common_of_arrow hm hTargetV hArrow⟩
  have hOrbit := ForcingOrbitQuotient.orbit_common hM hq hCommon
  have hClass := ((hPr target a).mp hIndex).2
  apply (hPr source a).mpr
  refine ⟨(hVertices source).mpr ⟨r,i,U,hSource,hSourceV⟩,?_⟩
  intro z
  exact (hClass z).trans (and_congr_right fun _ => ⟨
    fun hz => ForcingOrbitQuotient.orbit_trans hM hm hJ hq hOrbit hz,
    fun hz => ForcingOrbitQuotient.orbit_trans hM hm hJ hq (ForcingOrbitQuotient.orbit_symm hM hq hOrbit) hz⟩)

/-- LocalName.restrict keeps the literal name; range and stabilizer use existing constructors. -/
theorem entry_at_arrow (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I G F bound mul q source target n tau : M.Carrier .set}
    (hArrow : ConstructionComponentCofinal.EncodedArrow (v 0) I mul q source target n)
    (hEntry : ForcingTailCodes.Entry v G F bound target tau) :
    ForcingTailCodes.Entry v G F bound source tau := by
  obtain ⟨r,i,U,s,j,V,hSource,hTarget,hSourceV,_,hArrow⟩ := hArrow
  obtain ⟨t,k,W,A,H,hCode,hRange,hFix,hLocal⟩ := hEntry
  obtain ⟨es,_,_⟩ := ConstructionComponentCarrier.code_injective hCode hTarget
  have hRangeS : ForcingSupportedNames.Range (v 0) s A := es ▸ hRange
  obtain ⟨B,hB⟩ := ForcingLabelSystem.exists_range hM hSourceV.1
  obtain ⟨K,hK⟩ := ForcingLabelPermutations.exists_fixing hM G B
  have hAB : ForcingPowerName.Subset A B := by
    intro z hz
    obtain ⟨x,_,hx⟩ := (hRangeS z).mp hz
    obtain ⟨_,y,hy,_,hyz⟩ := (hArrow.2.1 x z).mp hx
    exact (hB z).mpr ⟨y,hy,hyz⟩
  exact ⟨r,i,U,B,K,hSource,hB,hK,hLocal.1,ForcingSupportedNames.supported_mono hFix hK hAB hLocal.2⟩

theorem compatible_one (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond : Fin k) (families : Fin 16 → Fin k)
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
    (hCode : ConstructionComponentCarrier.Code (env targetOne) (env commonRoot) (env commonIndex) (env commonIdeal))
    (hSigmaName : ForcingNames.IsName (env (rho 6)) (env sigma))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hFunctions : Functions env families (env Q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env f) (env (rho 3)))
    (hde : ForcingPowerName.Subset (env d) (env f))
    (hIndex : PureKuratowski.PairMember M (env vertex) (env a) (env pr))
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertex) (env vertexLabels))
    (hTargetObjects : PureKuratowski.PairMember M (env commonRoot) (env commonObjects) (env objects))
    (hTarget : ForcingLabelVertices.LabelVertex (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env commonRoot) (env commonIndex) (env label) (env targetOne))
    (hOldCode : ConstructionComponentCarrier.Code (env vertex) (env oldRoot) (env oldIndex) (env oldIdeal))
    (hOldVertex : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env oldRoot) (env oldIndex) (env oldIdeal))
    (hExtension : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env commonRoot) (env oldRoot))
    (hChainSecond : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env rootSecond) (env vertices) (env chainSecond))
    (hRootSecond : ConstructionComponentCarrier.Code (env rootSecond) (env rSecond) (env rootIndexSecond) (env rootUSecond))
    (hResultSecond : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env rootSecond) (env chainSecond) (env K) (env zero) (env germGroupSecond) (env quotientSecond) (env projectionSecond) (env repsSecond) (env nonidentitySecond) (env detectorDomainSecond) (env detectorSecond) (env detectorSitesSecond) (env highSecond) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrierSecond) (env patternOrderSecond) (env selectorDomainSecond) (env selectorSecond))
    (hdeSecond : ForcingPowerName.Subset (env e) (env f))
    (hIndexSecond : PureKuratowski.PairMember M (env vertexSecond) (env aSecond) (env pr))
    (hFieldsSecond : Fields env families (env aSecond) (env rootSecond) (env chainSecond) (env codesSecond) (env orderSecond) (env ranksSecond) (env selectionSecond) (env rankBoundSecond) (env labelSetSecond) (env tabSecond) (env rSecond) (env germGroupSecond) (env quotientSecond) (env nonidentitySecond) (env highSecond) (env detectorSecond) (env patternOrderSecond))
    (hSecond : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env e) (env vertexSecond) (env label) (env sigma))
    (hRootFiberSecond : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env rootSecond) (env labelSetSecond))
    (hVertexFiberSecond : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertexSecond) (env vertexLabelsSecond))
    (hTargetSecond : ForcingLabelVertices.LabelVertex (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env commonRoot) (env commonIndex) (env label) (env targetTwo))
    (hOldCodeSecond : ConstructionComponentCarrier.Code (env vertexSecond) (env oldRootSecond) (env oldIndexSecond) (env oldIdealSecond))
    (hOldVertexSecond : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env oldRootSecond) (env oldIndexSecond) (env oldIdealSecond))
    (hExtensionSecond : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env commonRoot) (env oldRootSecond)) :
    ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env f) (env commonRoot) (env tau) (env sigma) := by
  have hGermFirst := hGerms (env a) (env root) (env germGroup) hFields.1 hFields.2.2.2.2.2.2.2.2.2.2.1
  have hSystemFirst := ForcingLabelSystem.system_of_families hObj hObjects hMapFamily
  have hLabelFirst := ForcingAssignedLaws.assigned_label hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau Q pr a families
    hm hJ hw hChain hGermFirst hDiagrams hObj hObjects hArrows hMaps hMapFamily hSystemFirst hCommon hRootFiber hVertexFiber hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h
  have hAssignedFirst := ForcingAssignedExtension.assigned_at_extension hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices rootIndex rootU projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d f vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels commonRoot commonObjects commonIndex targetOne oldRoot oldIndex oldIdeal families
    hm hp hChain hRoot hK hResult he hde hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h hDiagrams hObj hObjects hArrows hMaps hMapFamily hCommon hRootFiber hVertexFiber hTargetObjects hTarget hOldCode hOldVertex hExtension
  obtain ⟨nFirst,hArrowFirst⟩ := ForcingLabelVertices.labelVertex_arrow hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hTargetObjects hTarget hOldCode hOldVertex hVertexFiber hLabelFirst hExtension
  have hIndexFirst := projection_at_arrow hM hm hJ hq hVertices hProjection hArrowFirst hIndex
  have hAssignedSecond := ForcingAssignedExtension.assigned_at_extension hM env rho I G F mul q bound labels E rootSecond w chainSecond codesSecond orderSecond ranksSecond selectionSecond top rankBoundSecond labelSetSecond tabSecond rSecond K B zero germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond one vertices rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e f vertexSecond label sigma Q pr aSecond diagrams objImage objects arrows mapImage maps vertexLabelsSecond commonRoot commonObjects commonIndex targetTwo oldRootSecond oldIndexSecond oldIdealSecond families
    hm hp hChainSecond hRootSecond hK hResultSecond he hdeSecond hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexSecond hFieldsSecond hSecond hDiagrams hObj hObjects hArrows hMaps hMapFamily hCommon hRootFiberSecond hVertexFiberSecond hTargetObjects hTargetSecond hOldCodeSecond hOldVertexSecond hExtensionSecond
  have hVertexEq := ForcingLabelVertices.labelVertex_unique hM hTarget hTargetSecond
  have hSecondAt : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env f) (env targetOne) (env label) (env sigma) := by
    simpa only [hVertexEq] using hAssignedSecond
  have hCompare := ForcingAssignedEquality.assigned_eq_iff hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal label sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families
    hK hResult hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hChain hCarrier hGroup hRoot hFamily hType hDiagrams hObj hObjects hCommon hRootFiber hSelector hOrder hRanks hTable hCode hSigmaName hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexFirst hFields hAssignedFirst hSecondAt
  exact hCompare.mpr rfl

def oneSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCarrier.code targetOne commonRoot commonIndex commonIdeal)
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) sigma))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (functions families Q)
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
    (.imp ( .mem (.bound f) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound f))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertex a))
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects commonRoot commonObjects))
    (.imp (ForcingLabelVertices.labelVertex (rho 0) I mul q objects maps commonRoot commonIndex label targetOne)
    (.imp (ConstructionComponentCarrier.code vertex oldRoot oldIndex oldIdeal)
    (.imp (ConstructionComponentVertices.vertex (rho 0) I mul q oldRoot oldIndex oldIdeal)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul commonRoot oldRoot))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero rootSecond vertices chainSecond)
    (.imp (ConstructionComponentCarrier.code rootSecond rSecond rootIndexSecond rootUSecond)
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q rootSecond chainSecond K zero germGroupSecond quotientSecond projectionSecond repsSecond nonidentitySecond detectorDomainSecond detectorSecond detectorSitesSecond highSecond B (rho 1) (rho 2) patternCarrierSecond patternOrderSecond selectorDomainSecond selectorSecond)
    (.imp (Project.Formula.subset (.bound e) (.bound f))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertexSecond aSecond))
    (.imp (fields families aSecond rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families e vertexSecond label sigma)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps rootSecond labelSetSecond)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertexSecond vertexLabelsSecond)
    (.imp (ForcingLabelVertices.labelVertex (rho 0) I mul q objects maps commonRoot commonIndex label targetTwo)
    (.imp (ConstructionComponentCarrier.code vertexSecond oldRootSecond oldIndexSecond oldIdealSecond)
    (.imp (ConstructionComponentVertices.vertex (rho 0) I mul q oldRootSecond oldIndexSecond oldIdealSecond)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul commonRoot oldRootSecond))
    (ForcingPrincipalFilter.eqF (ForcingProductSymmetry.orderFormula (rho 0) mul) id (rho 6) f commonRoot tau sigma)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionConcreteSelector.resultFormula_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,ConstructionComponentCarrier.code_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,ConstructionGermConditionSelector.selector_freeClosed,ForcingAssigned.assigned_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingAssigned.functions_freeClosed,ForcingAssigned.germs_freeClosed,ForcingAssigned.fields_freeClosed,ForcingOrdinalTable.table_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,Project.Formula.subset,assigned_freeClosed,functions_freeClosed,germs_freeClosed,fields_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingLabelVertices.labelVertex_freeClosed,ConstructionComponentVertices.vertex_freeClosed]

theorem one_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM,ForcingTailGroup.tailGroup_semantics hM,ConstructionComponentCarrier.code_semantics hM,ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),ForcingNames.isName_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ConstructionGermConditionSelector.selector_semantics hM,ForcingAssigned.assigned_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,ForcingAssigned.functions_semantics hM,ForcingAssigned.germs_semantics hM,KuratowskiZF.source_edge,ForcingAssigned.fields_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalTable.table_semantics hM,ForcingPrincipalFilter.eqF_semantics hM,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingLabelVertices.labelVertex_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ForcingDiagramOrder.le_semantics (M := M)]
  exact compatible_one hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond families

theorem one_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond families))) := by
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
  apply ConstructibleGround.relative_models hM (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (oneSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond families)).mp
      (one_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond families hL hChoice)

theorem compatible_inj (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond : Fin k) (families : Fin 16 → Fin k)
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
    (hCode : ConstructionComponentCarrier.Code (env targetOne) (env commonRoot) (env commonIndex) (env commonIdeal))
    (hSigmaName : ForcingNames.IsName (env (rho 6)) (env sigma))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hFunctions : Functions env families (env Q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env f) (env (rho 3)))
    (hde : ForcingPowerName.Subset (env d) (env f))
    (hIndex : PureKuratowski.PairMember M (env vertex) (env a) (env pr))
    (h : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertex) (env vertexLabels))
    (hTargetObjects : PureKuratowski.PairMember M (env commonRoot) (env commonObjects) (env objects))
    (hTarget : ForcingLabelVertices.LabelVertex (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env commonRoot) (env commonIndex) (env label) (env targetOne))
    (hOldCode : ConstructionComponentCarrier.Code (env vertex) (env oldRoot) (env oldIndex) (env oldIdeal))
    (hOldVertex : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env oldRoot) (env oldIndex) (env oldIdeal))
    (hExtension : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env commonRoot) (env oldRoot))
    (hChainSecond : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env rootSecond) (env vertices) (env chainSecond))
    (hRootSecond : ConstructionComponentCarrier.Code (env rootSecond) (env rSecond) (env rootIndexSecond) (env rootUSecond))
    (hResultSecond : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env rootSecond) (env chainSecond) (env K) (env zero) (env germGroupSecond) (env quotientSecond) (env projectionSecond) (env repsSecond) (env nonidentitySecond) (env detectorDomainSecond) (env detectorSecond) (env detectorSitesSecond) (env highSecond) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrierSecond) (env patternOrderSecond) (env selectorDomainSecond) (env selectorSecond))
    (hdeSecond : ForcingPowerName.Subset (env e) (env f))
    (hIndexSecond : PureKuratowski.PairMember M (env vertexSecond) (env aSecond) (env pr))
    (hFieldsSecond : Fields env families (env aSecond) (env rootSecond) (env chainSecond) (env codesSecond) (env orderSecond) (env ranksSecond) (env selectionSecond) (env rankBoundSecond) (env labelSetSecond) (env tabSecond) (env rSecond) (env germGroupSecond) (env quotientSecond) (env nonidentitySecond) (env highSecond) (env detectorSecond) (env patternOrderSecond))
    (hSecond : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env e) (env vertexSecond) (env otherLabel) (env sigma))
    (hRootFiberSecond : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env rootSecond) (env labelSetSecond))
    (hVertexFiberSecond : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertexSecond) (env vertexLabelsSecond))
    (hTargetSecond : ForcingLabelVertices.LabelVertex (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env commonRoot) (env commonIndex) (env otherLabel) (env targetTwo))
    (hOldCodeSecond : ConstructionComponentCarrier.Code (env vertexSecond) (env oldRootSecond) (env oldIndexSecond) (env oldIdealSecond))
    (hOldVertexSecond : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env oldRootSecond) (env oldIndexSecond) (env oldIdealSecond))
    (hExtensionSecond : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env commonRoot) (env oldRootSecond))
    (hqIdealFirst : Injection (env (rho 0)) (env I) (env q))
    (hChainIdealFirst : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hChainIdealSecond : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env rootSecond) (env vertices) (env chainSecond))
    (hCarrierIdealSecond : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chainSecond) (env codesSecond))
    (hVertexCode : ConstructionComponentCarrier.Code (env targetTwo) (env commonRoot) (env commonIndex) (env commonIdealSecond))
    (hOriginalEntryFirst : ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hOriginalEntrySecond : ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertexSecond) (env sigma))
    (hEq : ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env f) (env commonRoot) (env tau) (env sigma)) :
    env label = env otherLabel := by
  have hGermFirst := hGerms (env a) (env root) (env germGroup) hFields.1 hFields.2.2.2.2.2.2.2.2.2.2.1
  have hSystemFirst := ForcingLabelSystem.system_of_families hObj hObjects hMapFamily
  have hLabelFirst := ForcingAssignedLaws.assigned_label hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau Q pr a families
    hm hJ hw hChain hGermFirst hDiagrams hObj hObjects hArrows hMaps hMapFamily hSystemFirst hCommon hRootFiber hVertexFiber hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h
  have hAssignedFirst := ForcingAssignedExtension.assigned_at_extension hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices rootIndex rootU projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d f vertex label tau Q pr a diagrams objImage objects arrows mapImage maps vertexLabels commonRoot commonObjects commonIndex targetOne oldRoot oldIndex oldIdeal families
    hm hp hChain hRoot hK hResult he hde hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields h hDiagrams hObj hObjects hArrows hMaps hMapFamily hCommon hRootFiber hVertexFiber hTargetObjects hTarget hOldCode hOldVertex hExtension
  obtain ⟨nFirst,hArrowFirst⟩ := ForcingLabelVertices.labelVertex_arrow hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hTargetObjects hTarget hOldCode hOldVertex hVertexFiber hLabelFirst hExtension
  have hIndexFirst := projection_at_arrow hM hm hJ hq hVertices hProjection hArrowFirst hIndex
  have hGermSecond := hGerms (env aSecond) (env rootSecond) (env germGroupSecond) hFieldsSecond.1 hFieldsSecond.2.2.2.2.2.2.2.2.2.2.1
  have hSystemSecond := ForcingLabelSystem.system_of_families hObj hObjects hMapFamily
  have hLabelSecond := ForcingAssignedLaws.assigned_label hM env rho I G F mul q bound labels E rootSecond w chainSecond codesSecond orderSecond ranksSecond selectionSecond top rankBoundSecond labelSetSecond tabSecond rSecond K B zero germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond one vertices diagrams objImage objects arrows mapImage maps vertexLabelsSecond e vertexSecond otherLabel sigma Q pr aSecond families
    hm hJ hw hChainSecond hGermSecond hDiagrams hObj hObjects hArrows hMaps hMapFamily hSystemSecond hCommon hRootFiberSecond hVertexFiberSecond hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexSecond hFieldsSecond hSecond
  have hAssignedSecond := ForcingAssignedExtension.assigned_at_extension hM env rho I G F mul q bound labels E rootSecond w chainSecond codesSecond orderSecond ranksSecond selectionSecond top rankBoundSecond labelSetSecond tabSecond rSecond K B zero germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond one vertices rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e f vertexSecond otherLabel sigma Q pr aSecond diagrams objImage objects arrows mapImage maps vertexLabelsSecond commonRoot commonObjects commonIndex targetTwo oldRootSecond oldIndexSecond oldIdealSecond families
    hm hp hChainSecond hRootSecond hK hResultSecond he hdeSecond hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexSecond hFieldsSecond hSecond hDiagrams hObj hObjects hArrows hMaps hMapFamily hCommon hRootFiberSecond hVertexFiberSecond hTargetObjects hTargetSecond hOldCodeSecond hOldVertexSecond hExtensionSecond
  obtain ⟨nSecond,hArrowSecond⟩ := ForcingLabelVertices.labelVertex_arrow hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hTargetObjects hTargetSecond hOldCodeSecond hOldVertexSecond hVertexFiberSecond hLabelSecond hExtensionSecond
  have hIndexSecond := projection_at_arrow hM hm hJ hq hVertices hProjection hArrowSecond hIndexSecond
  have hEntryFirst := entry_at_arrow hM hArrowFirst hOriginalEntryFirst
  have hIdealFirst := ForcingAssignedIdeal.assigned_ideal hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q A Hq zero root vertices chain names targetOne f tau codes order ranks selection rankBound labelSet tab r label germGroup quotient nonidentity high detector patternOrder Q pr a commonRoot commonIndex commonIdeal families
    hw hMu hI hSmallD hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hqIdealFirst hRange hHq hE hChainIdealFirst hCarrier hEntryFirst hGermFirst hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexFirst hFields hAssignedFirst hCode he
  have hEntrySecond := entry_at_arrow hM hArrowSecond hOriginalEntrySecond
  have hIdealSecond := ForcingAssignedIdeal.assigned_ideal hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q A Hq zero rootSecond vertices chainSecond names targetTwo f sigma codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond otherLabel germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond Q pr aSecond commonRoot commonIndex commonIdealSecond families
    hw hMu hI hSmallD hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hqIdealFirst hRange hHq hE hChainIdealSecond hCarrierIdealSecond hEntrySecond hGermSecond hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexSecond hFieldsSecond hAssignedSecond hVertexCode he
  have hCommonInjection : Injection (env (rho 0)) (env I) (env commonRoot) := by
    obtain ⟨_,_,hv,_⟩ := hTarget
    exact hv.1
  have hIdeals := ForcingForcedAvailabilityCongruence.carrier_congr hM env rho I K B w mul one G F bound f commonRoot tau sigma commonIndex commonIdeal commonIdealSecond hm hp he hCommonInjection hEq hIdealFirst hIdealSecond
  have hVertexEq := ConstructionComponentCarrier.code_unique hM (hIdeals ▸ hCode) hVertexCode
  have hSecondAt : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env f) (env targetOne) (env otherLabel) (env sigma) := by
    simpa only [hVertexEq] using hAssignedSecond
  have hCompare := ForcingAssignedEquality.assigned_eq_iff hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families
    hK hResult hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hChain hCarrier hGroup hRoot hFamily hType hDiagrams hObj hObjects hCommon hRootFiber hSelector hOrder hRanks hTable hCode hSigmaName hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndexFirst hFields hAssignedFirst hSecondAt
  exact hCompare.mp hEq

def injSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCarrier.code targetOne commonRoot commonIndex commonIdeal)
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) sigma))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (functions families Q)
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
    (.imp ( .mem (.bound f) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound f))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertex a))
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects commonRoot commonObjects))
    (.imp (ForcingLabelVertices.labelVertex (rho 0) I mul q objects maps commonRoot commonIndex label targetOne)
    (.imp (ConstructionComponentCarrier.code vertex oldRoot oldIndex oldIdeal)
    (.imp (ConstructionComponentVertices.vertex (rho 0) I mul q oldRoot oldIndex oldIdeal)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul commonRoot oldRoot))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero rootSecond vertices chainSecond)
    (.imp (ConstructionComponentCarrier.code rootSecond rSecond rootIndexSecond rootUSecond)
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q rootSecond chainSecond K zero germGroupSecond quotientSecond projectionSecond repsSecond nonidentitySecond detectorDomainSecond detectorSecond detectorSitesSecond highSecond B (rho 1) (rho 2) patternCarrierSecond patternOrderSecond selectorDomainSecond selectorSecond)
    (.imp (Project.Formula.subset (.bound e) (.bound f))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertexSecond aSecond))
    (.imp (fields families aSecond rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families e vertexSecond otherLabel sigma)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps rootSecond labelSetSecond)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertexSecond vertexLabelsSecond)
    (.imp (ForcingLabelVertices.labelVertex (rho 0) I mul q objects maps commonRoot commonIndex otherLabel targetTwo)
    (.imp (ConstructionComponentCarrier.code vertexSecond oldRootSecond oldIndexSecond oldIdealSecond)
    (.imp (ConstructionComponentVertices.vertex (rho 0) I mul q oldRootSecond oldIndexSecond oldIdealSecond)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul commonRoot oldRootSecond))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero rootSecond vertices chainSecond)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chainSecond codesSecond)
    (.imp (ConstructionComponentCarrier.code targetTwo commonRoot commonIndex commonIdealSecond)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (ForcingTailCodes.entry rho G F bound vertexSecond sigma)
    (.imp (ForcingPrincipalFilter.eqF (ForcingProductSymmetry.orderFormula (rho 0) mul) id (rho 6) f commonRoot tau sigma)
    (Project.Formula.extensionalEq (.bound label) (.bound otherLabel))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionConcreteSelector.resultFormula_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,ConstructionComponentCarrier.code_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,ConstructionGermConditionSelector.selector_freeClosed,ForcingAssigned.assigned_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingAssigned.functions_freeClosed,ForcingAssigned.germs_freeClosed,ForcingAssigned.fields_freeClosed,ForcingOrdinalTable.table_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,Project.Formula.subset,assigned_freeClosed,functions_freeClosed,germs_freeClosed,fields_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingLabelVertices.labelVertex_freeClosed,ConstructionComponentVertices.vertex_freeClosed,ForcingTailCodes.entry_freeClosed]

theorem inj_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (injSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM,ForcingTailGroup.tailGroup_semantics hM,ConstructionComponentCarrier.code_semantics hM,ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),ForcingNames.isName_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ConstructionGermConditionSelector.selector_semantics hM,ForcingAssigned.assigned_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,ForcingAssigned.functions_semantics hM,ForcingAssigned.germs_semantics hM,KuratowskiZF.source_edge,ForcingAssigned.fields_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalTable.table_semantics hM,ForcingPrincipalFilter.eqF_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingLabelVertices.labelVertex_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ForcingDiagramOrder.le_semantics (M := M),ForcingTailCodes.entry_semantics hM]
  exact compatible_inj hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond families

theorem inj_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (injSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond families))) := by
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
  apply ConstructibleGround.relative_models hM (injSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (injSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond families)).mp
      (inj_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab f targetOne tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector commonRoot commonIndex commonIdeal otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a d vertex arrows mapImage vertexLabels commonObjects oldRoot oldIndex oldIdeal rootSecond chainSecond codesSecond orderSecond ranksSecond selectionSecond rankBoundSecond labelSetSecond tabSecond rSecond germGroupSecond quotientSecond nonidentitySecond highSecond detectorSecond patternOrderSecond rootIndexSecond rootUSecond projectionSecond repsSecond detectorDomainSecond detectorSitesSecond patternCarrierSecond selectorDomainSecond selectorSecond e vertexSecond aSecond vertexLabelsSecond targetTwo oldRootSecond oldIndexSecond oldIdealSecond commonIdealSecond families hL hChoice)

end PPAC.Migration.ForcingAssignedCompatibility
