/- Fixed AssignedGraphs.assignmentGraph:100-105 and assignmentGraph_bijection:253-269.
Construct the actual HS/supported graph name for the decoded Assigned relation
from ForcingRelationGraphSupport.construct and ForcingAssignedGraphMove.holds_move,
then combine ForcingAssignedRelation.{monotone,congruent,regular},
ForcingRelationGraphFunctions.{graph_surjection,graph_injection}, and
ForcingAssignedGraph{Total,One,Onto,Inj} in the SAME internal L. -/
import PPAC.Migration.ForcingAssignedRelation
import PPAC.Migration.ForcingAssignedGraphMove
import PPAC.Migration.ForcingAssignedGraphOne
import PPAC.Migration.ForcingAssignedGraphInj
import PPAC.Migration.ForcingAssignedGraphTotal
import PPAC.Migration.ForcingAssignedGraphOnto
import PPAC.Migration.ForcingRelationGraphFunctions

namespace PPAC.Migration.ForcingAssignedGraphBijection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source.SetLanguage (args3)
open ForcingSupportSize (MapsTo Injection)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingRelationGraphApplication (actionAt hs_actionAt)
open ForcingAssignedGraphTotal (AllCounts allCounts allCounts_freeClosed allCounts_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem witness_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin m → M.Carrier .set) (up : Fin k → Fin m)
    (he : ∀ i, other (up i) = env i) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (p x y : M.Carrier .set) :
    ForcingAssignedGraph.Witness hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up w) (up top) (up K) (up B) (up zero) (up Q) (up labelMap) (up bit) (fun j => up (families j)) p x y ↔
      ForcingAssignedGraph.Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y := by
  have hOrder (a b : M.Carrier .set) :
      MapRel (orderFormula (up (rho 0)) (up mul)) other a b ↔ MapRel (orderFormula (rho 0) mul) env a b := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  simp only [ForcingAssignedGraph.Witness,he,hOrder,
    ForcingAssigned.assigned_reindex hM env other up he,
    ForcingEquivariantMix.forces_order_congr hOrder]

private theorem holds_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin m → M.Carrier .set) (up : Fin k → Fin m)
    (he : ∀ i, other (up i) = env i) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (p x y : M.Carrier .set) :
    ForcingAssignedGraph.Holds hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up w) (up top) (up K) (up B) (up zero) (up Q) (up labelMap) (up bit) (fun j => up (families j)) p x y ↔
      ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y := by
  have hOrder (a b : M.Carrier .set) :
      MapRel (orderFormula (up (rho 0)) (up mul)) other a b ↔ MapRel (orderFormula (rho 0) mul) env a b := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  simp only [ForcingAssignedGraph.Holds,he,hOrder,witness_reindex hM env other up he]

/-- Pinned AssignedGraphs.graphRelation_move:90-98 as ForcingRelationGraphSupport.Moves
on the actual decoded Source relation. -/
theorem relation_moves (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul mu q A Hq labelMap top bit labels E bound zero Q : Fin k) (families : Fin 16 → Fin k)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq)) :
    ForcingRelationGraphSupport.Moves
      (ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families)
      env rho G F Hq := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall : ForcingSupportSize.Small (env w) (env mu) := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  obtain ⟨hLabelsHS,hLabelsFixed⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hLabelMap hTop hLabels
  have hBound := ForcingLocalNameTransport.bound_supported hM hp hG hLabelsHS hLabelsFixed ((ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound)
  intro pi hpiHq a ha p p' x y x' y' _ hpp _ _ hxx hyy hRel
  obtain ⟨hpiG,hFixes⟩ := (hHq pi).mp hpiHq
  have hpi := (hG pi).mp hpiG
  have hFixComp := ForcingComponentMove.root_fixed hpi hq hRange hFixes
  obtain ⟨inv,hi,hpii⟩ := ForcingConditionGraphs.exists_inverse hM hpi
  obtain ⟨c,hc,hcg⟩ := ForcingConjugationGraph.exists_graph hM hG hpi hi hpii
  have hr := (ForcingProductFamily.mapRel_action (fun j => env (rho j)) pi a).mp ha
  obtain ⟨ai,hiA⟩ := ForcingProductFamily.exists_action hM hp hi
  let other : Fin (k+5) → M.Carrier .set := Fin.cases ai (Fin.cases a (Fin.cases c (Fin.cases inv (Fin.cases pi env))))
  let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  have he (i : Fin k) : other (up i) = env i := rfl
  have hData : ForcingProductCovariance.SystemData (fun j => other (up (rho j))) (other (up I)) (other (up K)) (other (up B)) (other (up w)) (other (up G)) (other (up F)) (other (up mu)) (other 4) (other 3) (other 2) (other 1) (other 0) :=
    ⟨hp,hG,hpi,hi,hpii,hc,hcg,hr,hiA,hF⟩
  have hHolds := (ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y).mp hRel
  have hOther := (holds_reindex hM env other up he rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y).mpr hHolds
  have hMoved := ForcingAssignedGraphMove.holds_move hM other (fun j => up (rho j))
    (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up w) (up top)
    (up K) (up B) (up zero) (up Q) (up labelMap) (up bit) (up mu) 4 3 2 1 0
    (fun j => up (families j)) hData hq hFixComp hBound hLabelMap hTop hpp hxx hyy hOther
  exact (ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p' x' y').mpr
    ((holds_reindex hM env other up he rho I G F mul q bound labels E w top K B zero Q labelMap bit families p' x' y').mp hMoved)

/-- Pinned AssignedGraphs.assignmentGraph:100-105. Construct the actual HS
and Fix(q.range)-supported graph name for the Assigned relation. -/
theorem exists_assignmentGraph (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul mu q A Hq labelMap top bit labels E bound zero Q name : Fin k) (families : Fin 16 → Fin k)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hRange : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hEHS : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env name)) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
        (ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families)
        env (rho 6) top labels name graph ∧
      ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) graph := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall : ForcingSupportSize.Small (env w) (env mu) := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  obtain ⟨A',hA',hAI,hASmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hSmallD
  have hAA := ForcingCohenOrderAction.image_unique hM hRange hA'
  have hAI' : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x (env A) →
      (Project.FirstOrderSemantics.reduct M).mem x (env I) := hAA ▸ hAI
  have hASmall' : ForcingSupportSize.Small (env A) (env mu) := hAA ▸ hASmall
  have hGroup := ForcingConjugationGraph.fixing_subgroup hM hG hHq hAI'
  have hHF : (Project.FirstOrderSemantics.reduct M).mem (env Hq) (env F) :=
    (hF (env Hq)).mpr ⟨hGroup,env A,env Hq,hAI',hASmall',hHq,fun _ h => h⟩
  obtain ⟨hLabelsHS,hLabelsFixed⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hLabelMap hTop hLabels
  obtain ⟨hNameHS,hNameFixed⟩ := ForcingQuotientName.hs_and_fixed hM env rho G F mul I K labelMap top bit labels E hp hG hF hw hMu hLabelMap hTop hLabels hEHS hName
  have hfixX : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env labels) :=
    fun g hg a ha => hLabelsFixed g (hGroup.1 g hg) a ha
  have hfixY : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env name) :=
    fun g hg a ha => hNameFixed g (hGroup.1 g hg) a ha (hE g hg a ha)
  have hMoves := relation_moves hM env rho I K B w G F mul mu q A Hq labelMap top bit labels E bound zero Q families
    hp hG hF hw hMu hLabelMap hTop hLabels hLabelBound hq hRange hHq
  exact ForcingRelationGraphSupport.construct hM
    (ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families)
    env rho I K B w G F Hq mul top labels name
    hp hG hNormal hGroup hTop hLabelsHS hNameHS hfixX hfixY hMoves hHF

/-- Pinned AssignedGraphs.assignmentGraph_bijection:253-269. -/
theorem assignmentGraph_bijection (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo : Fin k)
    (families : Fin 16 → Fin k) {graph : M.Carrier .set}
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
    (hq : Injection (env (rho 0)) (env I) (env q))
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
    (hEHS : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E (env name))
    (hUncountable : ¬ ForcingSupportSize.Small (env K) (env w))
    (hCoding : Injection (env K) (env groundValues) (env labelMap))
    (hLo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B))
    (hBit : (Project.FirstOrderSemantics.reduct M).mem (env bit) (env B))
    (hBits : env lo ≠ env bit)
    (hGraph : ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families)
      env (rho 6) top labels name graph) :
    ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 graph (env labels) (env name)) (env (rho 6)) (env z0)
      ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)) := by
  let rel := ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families
  let v := args3 graph (env labels) (env name)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hz0W := ForcingSupportingRoot.code_mem hp hd0 hq hz0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall : ForcingSupportSize.Small (env w) (env mu) := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  obtain ⟨hLabelsHS,_⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hLabelMap hTop hLabels
  obtain ⟨hNameHS,_⟩ := ForcingQuotientName.hs_and_fixed hM env rho G F mul I K labelMap top bit labels E hp hG hF hw hMu hLabelMap hTop hLabels hEHS hName
  have hmono := ForcingAssignedRelation.monotone hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  have hcongr := ForcingAssignedRelation.congruent hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  have hregular := ForcingAssignedRelation.regular hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  have htotal : ForcingRelationGraphFunctions.Total (orderFormula (rho 0) mul) (actionAt rho) rel env (env (rho 6)) (env G) (env F) (env labels) (env name) (env z0) := by
    intro x _ p _ hp0 hMX r hr hrp
    obtain ⟨s,hs,hsr,y,hyHS,hMY,hHolds⟩ := ForcingAssignedGraphTotal.holds_total hM hChoice env rho
      I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 families
      hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hMark hCard hd0 hz0 hEHS hName hp0 hMX r hr hrp
    exact ⟨s,hs,hsr,y,(hs_actionAt env rho (env G) (env (rho 6)) (env F) y).mpr hyHS,hMY,
      (ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families s x y).mpr hHolds⟩
  have hone : ForcingRelationGraphFunctions.One (orderFormula (rho 0) mul) (actionAt rho) rel env (env (rho 6)) (env G) (env F) (env z0) := by
    intro p _ _ x y z _ _ _ hxy hxz
    exact ForcingAssignedGraphOne.holds_one hM hChoice env rho
      I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records groundValues lo families
      hK hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hUncountable hCoding hLo hBit hBits
      ((ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y).mp hxy)
      ((ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x z).mp hxz)
  have honto : ForcingRelationGraphFunctions.Onto (orderFormula (rho 0) mul) (actionAt rho) rel env (env (rho 6)) (env G) (env F) (env labels) (env name) (env z0) := by
    intro y _ p _ hp0 hMY r hr hrp
    obtain ⟨s,hs,hsr,x,hxHS,hMX,hHolds⟩ := ForcingAssignedGraphOnto.holds_onto hM hChoice env rho
      I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop families
      hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hName hp0 hMY r hr hrp
    exact ⟨s,hs,hsr,x,(hs_actionAt env rho (env G) (env (rho 6)) (env F) x).mpr hxHS,hMX,
      (ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families s x y).mpr hHolds⟩
  have hinj : ForcingRelationGraphFunctions.Injective (orderFormula (rho 0) mul) (actionAt rho) rel env (env (rho 6)) (env G) (env F) (env z0) := by
    intro p _ _ x y z _ _ _ hxz hyz
    exact ForcingAssignedGraphInj.holds_inj hM hChoice env rho
      I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records families
      hK hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections
      ((ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x z).mp hxz)
      ((ForcingAssignedRelation.relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p y z).mp hyz)
  rw [ForcingFormula.force_conj]
  exact ⟨ForcingRelationGraphFunctions.graph_surjection hM env rho G F mul top labels name rel v 0 1 2
      hp hG hNormal hTop hpre hLabelsHS hNameHS hmono hcongr hregular hGraph rfl rfl htotal hone honto hz0W,
    ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top labels name rel v 0 1 2
      hp hG hNormal hTop hpre hLabelsHS hNameHS hmono hcongr hregular hGraph rfl rfl htotal hone hinj hz0W⟩

/-- Construct the actual HS/supported assignmentGraph name and prove that z0
forces it to be a bijection from labelSet onto quotientName in the SAME internal L. -/
def bijectionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo : Fin k)
    (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingQuotientName.quotient rho G F mul I K labelMap top bit labels E id name))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small K w)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection labelMap K groundValues))
    (.imp (.mem (.bound lo) (.bound B))
    (.imp (.mem (.bound bit) (.bound B))
    (.imp (.neg (Project.Formula.extensionalEq (.bound lo) (.bound bit)))
    (.existsE (.conj
      (ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) mul)
        (ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families)
        Fin.succ (rho 6) top labels name 0))
      (.conj
        (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (rho j).succ) G.succ (rho 6).succ F.succ 0))
        (.conj
          (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => (rho j).succ) Hq.succ 0))
          (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F)
            Fin.succ (args3 0 labels.succ name.succ) (rho 6).succ z0.succ
            ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,ForcingTailCodes.candidates_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingOrbitParameterFamily.family_freeClosed,ForcingAssignedParameters.projections_freeClosed,allCounts_freeClosed,ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed,Project.Formula.extensionalEq]

theorem bijection_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo : Fin k)
    (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ForcingTailCodes.candidates_semantics hM,ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,Project.Formula.satisfies_mem_iff,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingOrbitParameterFamily.family_semantics hM,ForcingAssignedParameters.projections_semantics hM,allCounts_semantics hM,ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),ForcingHS.hs_semantics (M := M),ForcingQuotientName.quotient_semantics (M := M),Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ForcingRelationGraph.graph_semantics (M := M),ForcingFormula.formula_semantics (M := M),id_eq]
  intro hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hName hUncountable hCoding hLo hBit hBits
  obtain ⟨graph,hGraph,hHS,hSupp⟩ := exists_assignmentGraph hM env rho
    I K B w G F mul mu q A Hq labelMap top bit labels E bound zero Q name families
    hp hG hF hw hMu hSmallD hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hEHS hName
  have hBij := assignmentGraph_bijection hM hChoice env rho
    I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hName hUncountable hCoding hLo hBit hBits hGraph
  have hargs : (fun i => (Fin.cases graph env : Fin (k+1) → M.Carrier .set) (args3 0 labels.succ name.succ i)) =
      args3 graph (env labels) (env name) := by
    funext i
    exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.elim0 i) i) i) i
  refine ⟨graph,hGraph,hHS,hSupp,?_⟩
  change ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
    (fun i => (Fin.cases graph env : Fin (k+1) → M.Carrier .set) (args3 0 labels.succ name.succ i))
    (env (rho 6)) (env z0) ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))
  rw [hargs]
  exact hBij

theorem bijection_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo : Fin k)
    (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families))) := by
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
  apply ConstructibleGround.relative_models hM (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families)).mp
      (bijection_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families hL hChoice)

end PPAC.Migration.ForcingAssignedGraphBijection
