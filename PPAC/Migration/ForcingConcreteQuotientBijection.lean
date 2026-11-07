/- Fixed ConcreteQuotients.preliminary_ordinalCount:339-353 and
quotient_bijection_above:369-397.
Discharge AllCounts from the concrete ideal-probe / outside-local witness package
via ForcingIdealProbeCount.source_construct and ForcingLabelCardinality.fiber_equinumerous,
show that the restricted base condition d0 = d.restrict Ap is fixed by every
Fix(q.range) Cohen action so Subset d0 d' transfers to Subset d0 movedD, and combine
ForcingAssignedGraphBijection.{exists_assignmentGraph,assignmentGraph_bijection}. -/
import PPAC.Migration.ForcingAssignedGraphBijection
import PPAC.Migration.ForcingIdealProbeCount
import PPAC.Migration.ForcingLabelCardinality
import PPAC.Migration.ForcingCodeRanks

namespace PPAC.Migration.ForcingConcreteQuotientBijection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source.SetLanguage (args3)
open ForcingSupportSize (MapsTo Injection)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (actionFormula)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingAssignedGraphTotal (AllCounts allCounts allCounts_freeClosed allCounts_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Pinned ConcreteQuotients.quotient_bijection_above:390-397.
Every permutation fixing q along D also fixes p = q.sub mark on its range Ap,
so its Cohen action fixes d0 = d.restrict Ap and preserves d0 ⊆ d'. -/
theorem restricted_fixed_subset (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w S C P A E W mul q mark p Ap d d0 d' pi ac movedD : M.Carrier .set}
    (hp : ForcingProductFamily.Presentation D I K B w S C P A E W)
    (hq : Injection D I q)
    (hSubq : ForcingDiagramOrder.Sub D mul q mark p)
    (hAp : ForcingSupportedNames.Range D p Ap)
    (hd0 : ForcingCohenConditions.Condition C w d0)
    (hRestr : ConstructionCohenCompatibility.Restricted Ap d d0)
    (hPi : ForcingConditionGraphs.Permutation I pi)
    (hPiFix : ForcingConditionGraphs.CompositionGraph D pi q q)
    (hCohen : ForcingLocalTransport.CohenPart S C P pi ac)
    (hd0d' : ForcingPowerName.Subset d0 d')
    (hMoved : PureKuratowski.PairMember M d' movedD ac) :
    ForcingPowerName.Subset d0 movedD := by
  have hApFix (i : M.Carrier .set) (hi : (Project.FirstOrderSemantics.reduct M).mem i Ap) :
      PureKuratowski.PairMember M i i pi := by
    obtain ⟨x,_,hxp⟩ := (hAp i).mp hi
    obtain ⟨_,y,_,_,hyq⟩ := (hSubq x i).mp hxp
    obtain ⟨_,j,hyj,hjpi⟩ := (hPiFix y i).mp hyq
    exact ForcingConditionGraphs.function_unique hq.1.1 hyj hyq ▸ hjpi
  obtain ⟨f,t,hf,hfg,ht,htg,hac,hacg⟩ := hCohen
  obtain ⟨d0',hd0',_⟩ := hac.1.1.2 d0 ((hp.2.2.1 d0).mpr hd0)
  obtain ⟨_,hd0'P,hIm0⟩ := (hacg d0 d0').mp hd0'
  have hd0'Cond := (hp.2.2.1 d0').mp hd0'P
  have hMoved0 := ConstructionCohenCompatibility.moved_of_image hM hp.1 hp.2.1 hfg htg hd0 hIm0
  have hd0Eq : d0' = d0 := by
    apply ConstructionCohenCompatibility.entries_ext hM hp.1 hp.2.1 hd0'Cond hd0
    intro j k b
    rw [hMoved0 j k b]
    constructor
    · rintro ⟨i,hij,hiEntry⟩
      have hiAp := ((ConstructionCohenCompatibility.restricted_entry hRestr).mp hiEntry).2
      have hii := hApFix i hiAp
      exact ForcingConditionGraphs.function_unique hPi.1.1 hij hii ▸ hiEntry
    · intro hjEntry
      have hjAp := ((ConstructionCohenCompatibility.restricted_entry hRestr).mp hjEntry).2
      exact ⟨j,hApFix j hjAp,hjEntry⟩
  have hd0Self : PureKuratowski.PairMember M d0 d0 ac := hd0Eq ▸ hd0'
  exact (ForcingCohenOrderAction.graph_order hp.2.2.1 ht hacg d' d0 movedD d0 hMoved hd0Self).mpr hd0d'

/-- Pinned ConcreteQuotients.preliminary_ordinalCount:339-353 and
quotient_bijection_above:387-397: discharge AllCounts for every orbit record. -/
theorem all_counts (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q arrows mapImage high records d0 p b Ap Hp XP ordinal enum list Power continuum s j sigma d z : Fin k)
    (families : Fin 16 → Fin k)
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
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hRecords : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q (env records))
    (hProjections : ForcingAssignedParameters.Projections (env high) (env Q) (env records) (env (families 0)) (env (families 1)) (env (families 2)) (env (families 3)) (env (families 4)) (env (families 5)) (env (families 6)) (env (families 7)) (env (families 8)) (env (families 9)) (env (families 10)) (env (families 11)) (env (families 12)) (env (families 13)) (env (families 14)) (env (families 15)))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d0))
    (hEHS : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hSubq : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hKLeMu : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hAllIdeals : ConstructionIdealProbes.AllIdeals (env mu) (env history) (env kappa))
    (hbNe : env b ≠ env one)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hp) (env E))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env b) (env p))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : ConstructionCohenCompatibility.Restricted (env Ap) (env d) (env d0))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env s))
    (hj : ConstructionPlacementTriple.ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : ForcingRelationClassMove.Value (orderFormula (rho 0) mul) (domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env labelMap) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list)) :
    AllCounts hM env rho I mul q w top Q d0 families := by
  intro d' a selection' r' labelSet' _ hd0d' ha hSel' hr' hLab'
  obtain ⟨output,hOutput,_⟩ := hRecords.1.2 a ha
  obtain ⟨root,chain,hRootEdge,hChainEdge,hRecord⟩ := hRecords.2 a output hOutput
  obtain ⟨r,rootIndex,rootU,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,nonidentity,detectorDomain,detector,detectorSites,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hRecordCode,hRoot,hRootFiber,hData,_⟩ := hRecord
  have hFields : ForcingAssigned.Fields env families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity (env high) detector patternOrder :=
    ForcingAssignedParameters.fields_of_record hRecords.1 hOutput hProjections hA hB hC hRecordCode
  have hSelEq : selection' = selection :=
    ForcingConditionGraphs.function_unique hProjections.2.2.2.2.2.1.1 hSel' hFields.2.2.2.2.2.1
  have hLabEq : labelSet' = labelSet :=
    ForcingConditionGraphs.function_unique hProjections.2.2.2.2.2.2.2.1.1 hLab' hFields.2.2.2.2.2.2.2.1
  have hrEq : r' = r :=
    ForcingConditionGraphs.function_unique hProjections.2.2.2.2.2.2.2.2.2.1.1 hr' hFields.2.2.2.2.2.2.2.2.2.1
  subst selection' labelSet' r'
  obtain ⟨root',hRootEdge',hChain'⟩ := hChains.2 a chain hChainEdge
  have hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) root (env vertices) chain :=
    ForcingConditionGraphs.function_unique hReps.1.1 hRootEdge' hRootEdge ▸ hChain'
  obtain ⟨hrI,hSuba,hIdeal⟩ := ForcingTailGroup.root_vertex hChain hRoot
  obtain ⟨t,_,hae⟩ := (hm.2.1 rootIndex hIdeal.2.1).1 (env mark) hMark
  have hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) r t (env p) :=
    ForcingDiagramPoset.sub_sub hm hIdeal.2.1 hMark hae hSuba hSubq
  obtain ⟨P,hP⟩ := ForcingCohenCoordinates.exists_cartesian hM (env mu) (env mu)
  obtain ⟨coordS,hCoord⟩ := ForcingCohenCoordinates.exists_cartesian hM (env (rho 0)) (env K)
  obtain ⟨localS,hLocal⟩ := ForcingCohenCoordinates.exists_cartesian hM coordS (env B)
  obtain ⟨r_f,a_f,U_f,Or,hRoot_f,hOr,hFiber⟩ := hRootFiber
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot_f
  have hProbes := hAllIdeals (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base)
    rootIndex (env b) rootU hRow hb hbNe hIdeal
  have hCenters := ForcingLabelSystem.centers_of_families hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily
  obtain ⟨idMu,hIdMu⟩ := ZF.exists_identityBijection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) (env mu)
  have hLabelCard := ForcingLabelCardinality.fiber_equinumerous hM hDiagrams hObjects hCenters hOr hIdeal hProbes hFiber hSmallD ⟨idMu,hIdMu⟩
  obtain ⟨hCarrier,hOrder,_,hRootA,hRootH,hIncl,_,_,_,_,hRanks,hSelection,hFamily,_,_,_⟩ := hData
  let other : Fin (k+17) → M.Carrier .set :=
    Fin.cases localS (Fin.cases coordS (Fin.cases P (Fin.cases t (Fin.cases selection (Fin.cases ranks (Fin.cases fixing (Fin.cases support (Fin.cases group
      (Fin.cases order (Fin.cases codes (Fin.cases labelSet (Fin.cases rootU (Fin.cases rootIndex (Fin.cases r (Fin.cases chain (Fin.cases root env))))))))))))))))
  let upother : Fin k → Fin (k+17) := fun i =>
    i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have heother (i : Fin k) : other (upother i) = env i := rfl
  let rankEnv : Fin (k+8) → M.Carrier .set :=
    Fin.cases order (Fin.cases codes (Fin.cases labelSet (Fin.cases rootU (Fin.cases rootIndex (Fin.cases r (Fin.cases chain (Fin.cases root env)))))))
  let rankMap : Fin (k+8) → Fin (k+17) :=
    Fin.cases 9 (Fin.cases 10 (Fin.cases 11 (Fin.cases 12 (Fin.cases 13 (Fin.cases 14 (Fin.cases 15 (Fin.cases 16 upother)))))))
  have heRank (i : Fin (k+8)) : other (rankMap i) = rankEnv i :=
    Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))))) i
  let upRank : Fin k → Fin (k+8) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ
  change ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0) id (upRank (rho 0)) (upRank I) (upRank (rho 2)) (upRank w)) rankEnv codes order (env (rho 6)) ranks at hRanks
  have hSelected (u v : M.Carrier .set) :
      ForcingCodeSelection.IsSelected other (fun j => upother (rho j)) (upother I) (upother G) (upother F) (upother mul) (upother q) (upother bound) (upother labels) (upother E) 16 (upother w) 15 10 9 u v ↔
      ForcingCodeSelection.IsSelected rankEnv (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0 u v :=
    ForcingCodeRanks.selected_reindex rankEnv other rankMap heRank (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0 u v
  have hOtherRanks : ForcingOrdinalRanks.Ranks (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upother (rho j)) (upother I) (upother G) (upother F) (upother mul) (upother q) (upother bound) (upother labels) (upother E) 16 (upother w) 15 10 9) id (upother (rho 0)) (upother I) (upother (rho 2)) (upother w)) other codes order (env (rho 6)) ranks := by
    simpa only [ForcingOrdinalRanks.Ranks,ForcingOrdinalRanks.PredEntry,ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,ForcingCodeSelection.mapRel_relation hM,id_eq,hSelected,heother,rankEnv,upRank,Fin.cases_succ] using hRanks
  change ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upRank (rho j)) (upRank I) (upRank G) (upRank F) (upRank mul) (upRank q) (upRank bound) (upRank labels) (upRank E) 7 (upRank w) 6 1 0) id (upRank (rho 0)) (upRank I) (upRank (rho 2)) (upRank w)) rankEnv codes ranks (env (rho 6)) selection at hSelection
  have hOtherSelection : ForcingCollectedName.Collected (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation (fun j => upother (rho j)) (upother I) (upother G) (upother F) (upother mul) (upother q) (upother bound) (upother labels) (upother E) 16 (upother w) 15 10 9) id (upother (rho 0)) (upother I) (upother (rho 2)) (upother w)) other codes ranks (env (rho 6)) selection := by
    simpa only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,ForcingCollectedName.Admissible,ForcingCohenSelection.mapRel_lift,ForcingCohenSelection.Lift,ForcingCodeSelection.mapRel_relation hM,id_eq,hSelected,heother,rankEnv,upRank,Fin.cases_succ] using hSelection
  have hROther (u v : M.Carrier .set) :
      MapRel (orderFormula (upother (rho 0)) (upother mul)) other u v ↔
      MapRel (orderFormula (rho 0) mul) env u v := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heother]
  have hHOther (u : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (domain (fun i => upother (rho i)) (upother G) (upother F)) other u ↔
      ForcingClassEvaluation.Predicate (domain rho G F) env u := by
    simp only [ForcingPairUnion.domain_semantics,heother]
  obtain ⟨hjI,hSigmaHS,xLbl,hxLbl,hSigmaClass⟩ := hSigma
  have hOtherSigma : ForcingRelationClassMove.Value (orderFormula (upother (rho 0)) (upother mul))
      (domain (fun i => upother (rho i)) (upother G) (upother F)) other (fun i => other (upother (rho i)))
      (other (upother G)) (other (upother F)) (other (upother I)) (other (upother K)) (other (upother labelMap))
      (other (upother top)) (other (upother bit)) (other (upother labels)) (other (upother E)) (other (upother j)) (other (upother sigma)) := by
    refine ⟨hjI,hSigmaHS,xLbl,hxLbl,fun child q => (hSigmaClass child q).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (ForcingEquivariantMix.forces_order_congr (fun u v => (hROther u v).symm) false (env (rho 6)) child (env labels) q)
        (ForcingSeparation.force_congr (fun u v => (hROther u v).symm) (fun u => (hHOther u).symm) _ _ _ _))))⟩
  have hOtherOut : ForcingOutsideLocal.Outside (orderFormula (upother (rho 0)) (upother mul))
      other (other (upother (rho 6))) (other (upother z)) (other (upother sigma)) (other (upother list)) := by
    intro q' hq'W hq'z hForce
    exact hOut q' hq'W ((hROther q' (env z)).mp hq'z)
      ((ForcingEquivariantMix.forces_order_congr hROther false (env (rho 6)) (env sigma) (env list) q').mp hForce)
  have hCount0 : ForcingGermDensity.OrdinalCount hM other (fun i => upother (rho i)) (upother mul) (upother w) (upother top) 4 14 11 (env d0) :=
    ForcingIdealProbeCount.source_construct hM hChoice other (fun i => upother (rho i))
      (upother w) (upother mu) (upother history) (upother kappa) (upother one) (upother mark) (upother H) (upother C) (upother incoming) (upother base)
      (upother I) (upother K) (upother B) (upother G) (upother F) (upother mul) (upother labelMap) (upother top) (upother bit) (upother labels) (upother bound)
      (upother E) (upother q) (upother A) (upother Hq) 14 13 12 (upother p) (upother b) 3 (upother Ap) (upother Hp) (upother XP) (upother ordinal) (upother enum) (upother list)
      (upother d0) (upother zero) 16 (upother vertices) 15 (upother names) 7 6 10 9 5 4 8 2 (upother Power) (upother continuum) 1 0 11
      (upother s) (upother j) (upother sigma) (upother d) (upother z)
      hw hMu hI hSmallD hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hrI hpI hAp hHp hXP
      hIdeal.2.1 hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hRootA hRootH hCarrier hOrder hOtherRanks hOtherSelection hFamily hIncl
      hTwo hP hVertices hCard hMark hEHS hCoord hLocal hKLeMu hParameters hLabelCard hAllIdeals hbNe hEf hs hSub hd hSupp hRestr hz hj hOtherSigma hOtherOut
  let countEnv : Fin (k+5) → M.Carrier .set :=
    Fin.cases labelSet (Fin.cases r (Fin.cases selection (Fin.cases a (Fin.cases d' env))))
  let upCount : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  have heCount (i : Fin k) : countEnv (upCount i) = env i := rfl
  have hRCount (u v : M.Carrier .set) :
      MapRel (orderFormula (upCount (rho 0)) (upCount mul)) countEnv u v ↔
      MapRel (orderFormula (upother (rho 0)) (upother mul)) other u v := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,heCount,heother]
  intro pi ac movedD hPi hPiFix hCohen hMoved e he hMovedE theta ntheta htheta hntheta hEq
  have hd0Moved := restricted_fixed_subset hM hp hq hSubq hAp hd0 hRestr hPi hPiFix hCohen hd0d' hMoved
  have hd0e : ForcingPowerName.Subset (env d0) e := fun u hu => hMovedE u (hd0Moved u hu)
  obtain ⟨zc,hzc,hForceEq⟩ := hEq
  have hEqOther : ForcingPrincipalFilter.EqF (orderFormula (upother (rho 0)) (upother mul)) other
      (other (upother (rho 6))) e r selection ntheta :=
    ⟨zc,hzc,(ForcingEquivariantMix.forces_order_congr hRCount true (env (rho 6)) selection ntheta zc).mp hForceEq⟩
  exact hCount0 e he hd0e theta ntheta htheta hntheta hEqOther

/-- Pinned ConcreteQuotients.quotient_bijection_above:369-397.
Construct the HS, Fix(q.range)-supported assignment graph and force it to be a
bijection from labels to name (quotientName E) at z0 = (d0, q). -/
theorem quotient_bijection_above (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z : Fin k)
    (families : Fin 16 → Fin k)
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
    (hzero : ForcingWithTopCarrier.Empty (env zero))
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
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hSubq : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hKLeMu : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hAllIdeals : ConstructionIdealProbes.AllIdeals (env mu) (env history) (env kappa))
    (hbNe : env b ≠ env one)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hp) (env E))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env b) (env p))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : ConstructionCohenCompatibility.Restricted (env Ap) (env d) (env d0))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env s))
    (hj : ConstructionPlacementTriple.ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : ForcingRelationClassMove.Value (orderFormula (rho 0) mul) (domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env labelMap) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list)) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
        (ForcingAssignedRelation.relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families)
        env (rho 6) top labels name graph ∧
      ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) graph ∧
      ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
        (args3 graph (env labels) (env name)) (env (rho 6)) (env z0)
        ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2)) := by
  have hCounts := all_counts hM hChoice env rho
    I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q arrows mapImage high records d0 p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families
    hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hzero hNames hDiagrams hObj hObjects hVertices hReps hChains hArrows hMaps hMapFamily hRecords hProjections hMark hCard hd0 hEHS hpI hSubq hAp hHp hXP hb hEnum hList hTwo hKLeMu hParameters hAllIdeals hbNe hEf hs hSub hd hSupp hRestr hz hj hSigma hOut
  obtain ⟨graph,hGraph,hGraphHS,hGraphSupp⟩ := ForcingAssignedGraphBijection.exists_assignmentGraph hM env rho
    I K B w G F mul mu q A Hq labelMap top bit labels E bound zero Q name families
    hp hG hF hw hMu hSmallD hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hEHS hName
  have hBij := ForcingAssignedGraphBijection.assignmentGraph_bijection hM hChoice env rho
    I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo families
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hCounts hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hName hUncountable hCoding hLo hBit hBits hGraph
  exact ⟨graph,hGraph,hGraphHS,hGraphSupp,hBij⟩

def bijectionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z : Fin k)
    (families : Fin 16 → Fin k) : Project.Sentence where
  formula :=
    Project.Formula.forallClosure k
    (.imp (Project.Formula.isOrdinal (.bound K))
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
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero))
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
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul q mark p))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap Hp))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hp XP))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ForcingProductParameters.two B)
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound K) (.bound mu))
    (.imp (ConstructionConcreteCardinals.parameters w Power continuum mu)
    (.imp (ConstructionIdealProbes.allIdeals mu history kappa)
    (.imp (.neg (Project.Formula.extensionalEq (.bound b) (.bound one)))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hp E))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b p))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d)
    (.imp (ConstructionCohenCompatibility.restricted Ap d d0)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
    (.imp (ConstructionPlacementTriple.imageAt s (rho 0) j)
    (.imp (ProjectSyntax.encode id (ForcingRelationClassMove.value (orderFormula (rho 0) mul) (domain rho G F) id rho G F I K labelMap top bit labels E j sigma))
    (.imp (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
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
            ((Source.SetLanguage.surjection 0 1 2).conj (Source.SetLanguage.injection 0 1 2))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingTailCodes.candidates_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,
      ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,
      ForcingOrbitChains.family_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingOrbitParameterFamily.family_freeClosed,ForcingAssignedParameters.projections_freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,Project.Formula.extensionalEq,
      ForcingProductParameters.two_freeClosed,ConstructionConcreteCardinals.parameters_freeClosed,
      ConstructionIdealProbes.allIdeals_freeClosed,ForcingLocalRecordPullback.supported_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed,ConstructionPlacementTriple.imageAt_freeClosed]

theorem bijection_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z : Fin k)
    (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingTailCodes.candidates_semantics hM,ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,
    ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,
    ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,
    Project.Formula.satisfies_mem_iff,ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,ForcingOrbitParameterFamily.family_semantics hM,
    ForcingAssignedParameters.projections_semantics hM,ConstructionFractionOrder.carrier_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingQuotientName.quotient_semantics (M := M),
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.sub_semantics (M := M),ForcingLocalNames.carrier_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingProductParameters.two_semantics (M := M),
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionConcreteCardinals.parameters_semantics hM,ConstructionIdealProbes.allIdeals_semantics hM,
    ForcingLocalRecordPullback.supported_semantics hM,ConstructionCohenCompatibility.restricted_semantics hM,
    ConstructionPlacementTriple.imageAt_semantics hM,ForcingRelationClassMove.value_semantics (M := M),
    ForcingOutsideLocal.outside_semantics (M := M),
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingRelationGraph.graph_semantics (M := M),ForcingFormula.formula_semantics (M := M),id_eq]
  intro hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hzero hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hName hUncountable hCoding hLo hBit hBits hpI hSubq hAp hHp hXP hb hEnum hList hTwo hKLeMu hParameters hAllIdeals hbNe hEf hs hSub hd hSupp hRestr hz hj hSigma hOut
  obtain ⟨graph,hGraph,hHS,hSupp,hBij⟩ := quotient_bijection_above hM hChoice env rho
    I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families
    hK hm hJ hp hG hF hw hMu hI hSmallD hMergers hRow hLabelMap hTop hLabels hLabelBound hq hRange hHq hE hzero hNames hDiagrams hObj hObjects hCommon hVertices hQuotient hProjection hReps hChains hArrows hMaps hMapFamily hRecords hProjections hQ hR hTopCut hObjFields hMark hCard hd0 hz0 hEHS hName hUncountable hCoding hLo hBit hBits hpI hSubq hAp hHp hXP hb hEnum hList hTwo hKLeMu hParameters hAllIdeals hbNe hEf hs hSub hd hSupp hRestr hz hj hSigma hOut
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
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z : Fin k)
    (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative
        (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families))) := by
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
  apply ConstructibleGround.relative_models hM
    (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL)
    (bijectionSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families)).mp
      (bijection_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero vertices names diagrams objImage objects maps Q pr arrows mapImage high records d0 name z0 Qcuts Rcuts realTop groundValues lo p b Ap Hp XP ordinal enum list Power continuum s j sigma d z families hL hChoice)

end PPAC.Migration.ForcingConcreteQuotientBijection
