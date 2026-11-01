/- Pinned OrbitAssignments.corrected_onto:88-121.
Consume existing StableAt transport, linked-working and Preliminary onto.
The given actual stable name is retained; no independently assigned surrogate. -/
import PPAC.Migration.ForcingGermCorrectedDensity
import PPAC.Migration.ForcingLinkedWorking

namespace PPAC.Migration.ForcingGermCorrectedOnto
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingComponentFibers (VertexFiber)
open ConstructionComponentCofinal (EncodedCommon Chain)
open ForcingProductSymmetry (orderFormula)
open ForcingGermDensity (OrdinalCount)
open ForcingGermCorrectedDensity (InverseCounts label_move)
open ForcingStableAt (StableAt stableAt)
open ForcingGermPreliminary (Preliminary)
open ForcingGermCorrected (Corrected corrected)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The Works subformula of the existing selected_reindex calculation. -/
theorem works_reindex {k n : Nat} (env : Fin k → M.Carrier .set)
    (other : Fin n → M.Carrier .set) (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain : Fin k)
    (d a : M.Carrier .set) :
    ForcingPersistentWorks.Works (orderFormula (base (rho 0)) (base mul))
      (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F)) other
      (fun j => other (base (rho j))) (other (base I)) (other (base G)) (other (base F))
      (other (base mul)) (other (base q)) (other (base bound)) (other (base labels))
      (other (base E)) (other (base root)) (other (base w)) (other (base chain)) d a ↔
    ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound)
      (env labels) (env E) (env root) (env w) (env chain) d a := by
  have hR (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (base (rho 0)) (base mul)) other x y ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  have hH (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F)) other x ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,he]
  simp only [ForcingPersistentWorks.Works,ForcingPersistentWorks.Represented,
    ForcingPersistentWorks.Bundle,ForcingTailCodes.Represents,ForcingTailCodes.At,
    ForcingEligibleFamily.Family,ForcingEligibleFamily.Row,
    ForcingEligibleMapFamily.Family,ForcingEligibleMapFamily.MapRow,ForcingEligibleFamily.Data,
    ForcingLocalQuotient.Classes,ForcingLocalQuotient.Projection,ForcingLocalQuotient.Class,
    ForcingEligibleObjects.Carrier,ForcingEligibility.Eligible,ForcingEligibility.EligibleName,
    ForcingLocalAtomic.EqG,
    ForcingSeparation.force_congr hR hH,ForcingEquivariantMix.forces_order_congr hR,he]

theorem corrected_onto (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps : Fin k)
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
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hCommon : EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env vertex))
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
    (hCount : InverseCounts hM env rho I mul w top selection r labelSet germGroup (env d))
    (hStable : StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) (env d) (env vertex) (env tau)) :
    ∃ e label, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧ (Project.FirstOrderSemantics.reduct M).mem label (env labelSet) ∧
      Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder e (env vertex) label (env tau) := by
  obtain ⟨e,he,hde,hGood⟩ := ConstructionConcreteSelector.good_dense hM hResult hd
  obtain ⟨pi,cls,hpi,hClass,hSelected⟩ := ConstructionConcreteSelector.selected_exists hM hResult he hGood
  have hStab := (hResult.1.1 pi).mp hpi
  obtain ⟨inv,hInv,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hStab.1
  have hInvStab := ConstructionGermSeparation.stabilizes_inverse hM hq hStab hInv hInverse
  obtain ⟨act,hAct⟩ := ForcingProductFamily.exists_action hM hp hInv
  obtain ⟨forward,hForward⟩ := ForcingProductFamily.exists_action hM hp hStab.1
  obtain ⟨ac,hCohen⟩ := ForcingLocalTransport.part_of_action hAct
  obtain ⟨fc,hForwardCohen⟩ := ForcingLocalTransport.part_of_action hForward
  have hac := ForcingLocalTransport.part_permutation hCohen
  have hfc := ForcingLocalTransport.part_permutation hForwardCohen
  obtain ⟨oldD,hdd,_⟩ := hac.1.1.2 (env d) ((hp.2.2.1 (env d)).mpr hd)
  obtain ⟨oldE,hee,_⟩ := hac.1.1.2 e ((hp.2.2.1 e).mpr he)
  have hInverseOrder : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨_,_,_,_,ht,_,_,hGraph⟩ := hCohen
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  have hOldDE := (hInverseOrder e (env d) oldE oldD hee hdd).mpr hde
  have hOldE := (hp.2.2.1 oldE).mp (hac.1.2 e oldE hee)
  have hVertex : ConstructionComponentCarrier.EncodedVertex (env (rho 0)) (env I) (env mul) (env q) (env vertex) := by
    obtain ⟨_,_,_,s,b,V,_,hv,_,hs,_⟩ := hCommon
    exact ⟨s,b,V,hv,hs⟩
  obtain ⟨oldVertex,hMove⟩ := ForcingComponentMove.exists_move hM hInv hInvStab.2.1 hVertex
  obtain ⟨movedRoot,hMoveRoot,hRootCommon⟩ := hInvStab.2.2
  have hMovedCommon := ForcingComponentMove.move_common hM hInv hInvStab.2.1 hMoveRoot hMove hCommon
  have hOldCommon := (ForcingComponentRebase.common_iff hM hm hJ hRootCommon).mpr hMovedCommon
  have hCountE : OrdinalCount hM env rho mul w top selection r labelSet oldE := by
    intro f hf hef
    exact hCount pi inv ac oldD hpi hInv hInverse hCohen hdd f hf (fun x hx => hef x (hOldDE x hx))
  have hReverse : ForcingConditionGraphs.InverseGraph inv pi := fun x y => (hInverse y x).symm
  obtain ⟨oldTau,hTau⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hAct).1 (env tau)
  obtain ⟨conj,hConjPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hInv hStab.1 hReverse
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) inv pi conj act forward :=
    ⟨hp,hG,hInv,hStab.1,hReverse,hConjPerm,hConj,hAct,hForward,hF⟩
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hOmegaSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  obtain ⟨hLabelsHS,hLabelsFix⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hOmegaSmall hLabelMap hTop hLabels
  have hBound := ForcingLocalNameTransport.bound_supported hM hp hG hLabelsHS hLabelsFix ((ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound)
  have hInvHq : (Project.FirstOrderSemantics.reduct M).mem inv (env Hq) := by
    apply (hHq inv).mpr
    refine ⟨(hG inv).mpr hInv,?_⟩
    intro x hx
    obtain ⟨j,_,hjx⟩ := (hAq x).mp hx
    obtain ⟨_,y,hjy,hyx⟩ := (hInvStab.2.1 j x).mp hjx
    have hy : y = x := ForcingConditionGraphs.function_unique hq.1.1 hjy hjx
    exact hy ▸ hyx
  let movedEnv : Fin (k+1) → M.Carrier .set := Fin.cases act env
  have hEnv (i : Fin k) : movedEnv i.succ = env i := rfl
  have hStableInput := (ForcingGermCorrectedStable.stable_reindex env movedEnv Fin.succ hEnv rho G F mul bound labels E (env d) (env vertex) (env tau)).mpr hStable
  have hRel := (ForcingProductFamily.mapRel_action (fun j => env (rho j)) inv act).mpr hAct
  have hMoved := ForcingStableAt.permute hM movedEnv (fun j => (rho j).succ) G.succ F.succ mul.succ 0
    hm hData hNormal hBound (hLabelsFix inv ((hG inv).mpr hInv) act hRel) (hE inv hInvHq act hRel)
    hCohen hdd hMove hTau hStableInput
  have hOldStable := (ForcingGermCorrectedStable.stable_reindex env movedEnv Fin.succ hEnv rho G F mul bound labels E oldD oldVertex oldTau).mp hMoved
  obtain ⟨s,index,U,A,Hfix,z,hCode,hRange,hFix,hLocal,hz,hForce,hPermanent⟩ := hOldStable
  let other : Fin (k+7) → M.Carrier .set := Fin.cases oldD (Fin.cases oldVertex (Fin.cases oldTau
    (Fin.cases s (Fin.cases index (Fin.cases U (Fin.cases z env))))))
  let up : Fin k → Fin (k+7) := fun i => i.succ.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hR (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (up (rho 0)) (up mul)) other x y ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,henv]
  have hH (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun j => up (rho j)) (up G) (up F)) other x ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,henv]
  have hForceOther := (ForcingSeparation.force_congr hR hH (ForcingEligibility.isClass 0 1 2) (Source.SetLanguage.args3 oldTau (env labels) (env E)) (env (rho 6)) z).mpr hForce
  have hPermanentOther : ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset oldD e →
      ForcingForcedAvailability.Carrier (orderFormula (up (rho 0)) (up mul)) other (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) e s index oldTau U := by
    simpa only [ForcingForcedAvailability.Carrier,ForcingForcedAvailability.Available,ForcingPrincipalFilter.EqF,
      ForcingEquivariantMix.forces_order_congr hR] using hPermanent
  obtain ⟨a,ha,hWorks,hLinks⟩ := ForcingLinkedWorking.exists_linked_working_of_stable hM hChoice other (fun j => up (rho j))
    (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base)
    (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound) (up E) (up q) (up Aq) (up Hq)
    (up zero) (up root) (up vertices) (up chain) (up names) 1 3 4 5 0 2 6
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
    hNames hVertices hChain hCode hOldCommon ⟨s,index,U,A,Hfix,hCode,hRange,hFix,hLocal⟩ (hac.1.2 (env d) oldD hdd) hz hForceOther hPermanentOther
  have hWorksOld := (works_reindex env other up henv rho I G F mul q bound labels E root w chain oldD a).mp hWorks
  change ForcingCodeLinks.Links (orderFormula (up (rho 0)) (up mul)) other (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) oldD oldVertex oldTau a at hLinks
  have hLinksOld : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) oldD oldVertex oldTau a := by
    simpa only [ForcingCodeLinks.Links,ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hR] using hLinks
  have hLinksE := ForcingCodeLinks.links_mono hM env rho mul hm hp (hac.1.2 e oldE hee) hOldDE hLinksOld
  have hHS : ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env oldTau :=
    (ForcingPairUnion.domain_semantics env rho G F oldTau).mpr hLocal.1.1
  obtain ⟨f,oldLabel,hf,hef,hPreliminary⟩ := ForcingGermDensity.onto_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul top labels bound E q zero root vertices chain names codes order ranks selection group r rootIndex rootU rootA rootH labelSet (env rankBound) (env tab) oldVertex oldE a oldTau
    hw hMu hI hSmall hMergers hRow hm hp hG hF hTop hChain hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hOldE ((hCarrier a).mpr ha) hHS (ForcingPersistentWorks.works_mono hOldDE hWorksOld) hLinksE hCountE
  obtain ⟨g,hfg,_⟩ := hfc.1.1.2 f ((hp.2.2.1 f).mpr hf)
  have hg := (hp.2.2.1 g).mp (hfc.1.2 f g hfg)
  have hBackE := ForcingAssignmentInvariant.cohen_inverse hp hReverse hCohen hForwardCohen hee
  have hForwardOrder : ForcingCohenOrderAction.OrderPreserving fc := by
    obtain ⟨_,_,_,_,ht,_,_,hGraph⟩ := hForwardCohen
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  have heg := (hForwardOrder f oldE g e hfg hBackE).mpr hef
  have hBackG := ForcingAssignmentInvariant.cohen_inverse hp hInverse hForwardCohen hCohen hfg
  have hLabelI : (Project.FirstOrderSemantics.reduct M).mem oldLabel (env I) := by
    obtain ⟨s,a,U,Os,_,hs,hFiber⟩ := hRootFiber
    obtain ⟨n,_,hn⟩ := (((hObjects s Os).mp hs).2 oldLabel).mp ((hFiber oldLabel).mp hPreliminary.1).1
    exact ((hDiagrams s).mp (ForcingConditionGraphs.function_input hObj.1 hs)).1.2 n oldLabel hn
  obtain ⟨label,hLabel,_⟩ := hStab.1.1.1.2 oldLabel hLabelI
  obtain ⟨forwardRoot,hMoveForward,hCommonForward⟩ := hStab.2.2
  obtain ⟨forwardFiber,hForwardFiber⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj (ForcingComponentMove.target_vertex hMoveForward)
  have hMovedLabel := label_move hM hm hStab.1 hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hMoveForward hRootFiber hForwardFiber hPreliminary.1 hLabel
  have hFiberEq := hFibers (env q) (env root) forwardRoot (env labelSet) forwardFiber hCommonForward hRootFiber hForwardFiber
  have hLabelMem : (Project.FirstOrderSemantics.reduct M).mem label (env labelSet) := hFiberEq.symm ▸ hMovedLabel
  obtain ⟨hGerm,_,_,hX,hDet,_,_,_,_,hZero,hHigh,hBits,hCoords,hS,hCover,hWO,_,_⟩ := hResult
  have hSelectedG := ConstructionGermSelected.selected_mono hM hGerm.1 hDet.1 hX hCoords hS hK hCover hWO hZero hHigh hBits he hg heg hSelected
  exact ⟨g,label,hg,(fun x hx => heg x (hde x hx)),hLabelMem,
    pi,cls,hpi,hClass,hSelectedG,inv,act,ac,f,oldVertex,oldLabel,oldTau,
    hStab.1,hInv,hInverse,hAct,hCohen,hBackG,hMove,(hInverse oldLabel label).mp hLabel,hTau,hPreliminary⟩

def ontoSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps : Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex)
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
    (.imp (ForcingGermCorrectedDensity.inverseCounts rho I mul w top selection r labelSet germGroup d)
    (.imp (stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul bound labels E d vertex tau)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (.mem (.bound 0) (.bound labelSet.succ.succ))
      (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (fun j => j.succ.succ) 1 vertex.succ.succ 0 tau.succ.succ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.candidates_freeClosed,ForcingStableAt.stableAt_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingGermCorrected.corrected_freeClosed,
      ForcingGermCorrectedDensity.inverseCounts_freeClosed, ConstructionConcreteSelector.resultFormula_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem onto_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps)).TrueIn M := by
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
    ForcingTailCodes.candidates_semantics hM,ForcingStableAt.stableAt_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingStabilizerTransport.image_semantics (M := M),Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    ForcingOrdinalFixed.fixedFamily_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ForcingGermCorrectedDensity.inverseCounts_semantics hM,
    Project.Formula.satisfies_isOrdinal_iff,ConstructionConcreteSelector.resultFormula_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,ForcingEligibleSystem.system_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ForcingGermCorrected.corrected_semantics hM]
  exact corrected_onto hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps

theorem onto_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps))) := by
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
  apply ConstructibleGround.relative_models hM (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps)).mp
      (onto_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps hL hChoice)


end PPAC.Migration.ForcingGermCorrectedOnto
