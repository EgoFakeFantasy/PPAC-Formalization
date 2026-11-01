/- Fixed AssignedGraphs.graphWitness_bounds:67-77. Reuse the actual
whole-orbit record functions and existing Assigned/Orbit stability; no supplied
abstract stability law, rank cutoff, or replacement graph relation. -/
import PPAC.Migration.ForcingAssignedGraph
import PPAC.Migration.ForcingAssignedParameters
import PPAC.Migration.ForcingOrbitStable
import PPAC.Migration.ForcingQuotientName

namespace PPAC.Migration.ForcingAssignedGraphBounds
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitAssignment (OrbitAssignment)
open ForcingStableAt (StableAt)
open ForcingProductSymmetry (orderFormula)
open ConstructionComponentCofinal (Chain)
open ForcingTailCodes (Entry)
open ForcingSupportSize (Injection)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem orbit_stable_values (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names codes order ranks selection rankBound labelSet tab initialRoot germGroup quotient nonidentity high detector patternOrder : Fin k) (d vertex label tau : M.Carrier .set)
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
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertex tau)
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau) :
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) d vertex tau := by
  let other : Fin (k+4) → M.Carrier .set := Fin.cases tau (Fin.cases label (Fin.cases vertex (Fin.cases d env)))
  let up : Fin k → Fin (k+4) := fun i => i.succ.succ.succ.succ
  have he (i : Fin k) : other (up i) = env i := rfl
  have hInput := (ForcingOrbitRepresentativeDensity.orbitAssignment_reindex hM env other up he rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau).mpr h
  have hs := ForcingOrbitStable.orbitAssignment_stable hM hChoice other (fun j => up (rho j)) (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base) (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound) (up E) (up q) (up Aq) (up Hq) (up zero) (up root) (up vertices) (up chain) (up names) 2 3 0 (up codes) (up order) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) (up initialRoot) 1 (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder)
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hChain hCarrier hEntry hGerm hInput
  exact (ForcingGermCorrectedStable.stable_reindex env other up he rho G F mul bound labels E d vertex tau).mp hs

theorem assigned_stable_from_records (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records : Fin k) (families : Fin 16 → Fin k)
    {d vertex label tau : M.Carrier .set}
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
    (hRecords : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q (env records))
    (hProjections : ForcingAssignedParameters.Projections (env high) (env Q) (env records) (env (families 0)) (env (families 1)) (env (families 2)) (env (families 3)) (env (families 4)) (env (families 5)) (env (families 6)) (env (families 7)) (env (families 8)) (env (families 9)) (env (families 10)) (env (families 11)) (env (families 12)) (env (families 13)) (env (families 14)) (env (families 15)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertex tau)
    (h : ForcingAssigned.Assigned hM env rho I G F mul q bound labels E w top K B zero Q families d vertex label tau) :
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) d vertex tau := by
  obtain ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,initialRoot,germGroup,quotient,nonidentity,localHigh,detector,patternOrder,ha,hFields,hOrbit⟩ := h
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := hProjections
  obtain ⟨hf0,hf1,hf2,hf3,hf4,hf5,hf6,hf7,hf8,hf9,hf10,hf11,hf12,hf13,hf14,hf15⟩ := hFields
  obtain ⟨output,hOutput,_⟩ := hRecords.1.2 a ha
  obtain ⟨root0,chain0,hRoot0,hChain0,hRecord⟩ := hRecords.2 a output hOutput
  have eRoot := ForcingConditionGraphs.function_unique h0.1 hRoot0 hf0
  have eChain := ForcingConditionGraphs.function_unique h1.1 hChain0 hf1
  subst root0; subst chain0
  obtain ⟨r0,index0,U0,labels0,codes0,order0,group0,support0,fixing0,ranks0,selection0,rankBound0,tab0,germ0,quotient0,projection0,reps0,N0,X0,detector0,J0,patternCarrier0,patternOrder0,selectorDomain0,selector0,packA,packB,packC,hA,hB,hC,hCode,_,_,hData,hSelector⟩ := hRecord
  have hc0 := (h2.2 a codes0).mpr ⟨ha,output,hOutput,
    ForcingAssignedParameterFields.value_intro 2 (env high) output root chain r0 index0 U0 labels0 codes0 order0 group0 support0 fixing0 ranks0 selection0 rankBound0 tab0 germ0 quotient0 projection0 reps0 N0 X0 detector0 J0 patternCarrier0 patternOrder0 selectorDomain0 selector0 packA packB packC hA hB hC hCode⟩
  have hg0 := (h10.2 a germ0).mpr ⟨ha,output,hOutput,
    ForcingAssignedParameterFields.value_intro 10 (env high) output root chain r0 index0 U0 labels0 codes0 order0 group0 support0 fixing0 ranks0 selection0 rankBound0 tab0 germ0 quotient0 projection0 reps0 N0 X0 detector0 J0 patternCarrier0 patternOrder0 selectorDomain0 selector0 packA packB packC hA hB hC hCode⟩
  have ec := ForcingConditionGraphs.function_unique h2.1 hc0 hf2
  have eg := ForcingConditionGraphs.function_unique h10.1 hg0 hf10
  subst codes0; subst germ0
  have hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) chain codes := hData.1
  have hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) root germGroup := hSelector.1.1
  obtain ⟨root1,hRoot1,hChain⟩ := hChains.2 a chain hf1
  have er := ForcingConditionGraphs.function_unique h0.1 hRoot1 hf0
  subst root1
  let other := ForcingAssigned.context env a root chain codes order ranks selection rankBound labelSet tab initialRoot germGroup quotient nonidentity localHigh detector patternOrder
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have he (i : Fin k) : other (up i) = env i := rfl
  have hs := orbit_stable_values hM hChoice other (fun j => up (rho j)) (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base) (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound) (up E) (up q) (up Aq) (up Hq) (up zero) 15 (up vertices) 14 (up names) 13 12 11 10 9 8 7 6 5 4 3 2 1 0 d vertex label tau
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hChain hCarrier hEntry hGerm hOrbit
  exact (ForcingGermCorrectedStable.stable_reindex env other up he rho G F mul bound labels E d vertex tau).mp hs

theorem witness_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records : Fin k) (families : Fin 16 → Fin k)
    {name p x y : M.Carrier .set}
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
    (hRecords : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q (env records))
    (hProjections : ForcingAssignedParameters.Projections (env high) (env Q) (env records) (env (families 0)) (env (families 1)) (env (families 2)) (env (families 3)) (env (families 4)) (env (families 5)) (env (families 6)) (env (families 7)) (env (families 8)) (env (families 9)) (env (families 10)) (env (families 11)) (env (families 12)) (env (families 13)) (env (families 14)) (env (families 15)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E name)
    (h : ForcingAssignedGraph.Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env labels) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name p := by
  obtain ⟨d,vertex,j,tau,r,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,hpz,hAssigned,hLabel,hx,hy⟩ := h
  have hs := assigned_stable_from_records hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records families
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hRecords hProjections hChains hEntry hAssigned
  obtain ⟨r',index',U',A',H',z',hCode',_,_,hLocal,hz',hclass,_⟩ := hs
  obtain ⟨er,_,_⟩ := ConstructionComponentCarrier.code_injective hCode' hCode
  subst r'
  have ez : z' = z := by
    obtain ⟨c',hc',hcSingle'⟩ := hz'
    obtain ⟨c,hc,hcSingle⟩ := hz
    have ec := KuratowskiZF.code_unique hM hc' hc
    subst c'
    exact ForcingWithTopCarrier.single_unique hM hcSingle' hcSingle
  subst z'
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hpW := ForcingAtomicBasic.condition hM hx
  have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp hd) hVertex.1 hz
  have htW := (hp.2.2.2.2.2 (env top)).mpr (Or.inl hTop)
  have htop : ∀ t, (Project.FirstOrderSemantics.reduct M).mem t (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env t (env top) := by
    intro t _
    exact (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul t (env top)).mpr (Or.inl hTop)
  constructor
  · apply (ForcingAtomicLaws.mem_congr_left hM hpre hx).mpr
    apply (ForcingLabelDensity.mem_labelSet hM _ env hLabels hpW htW htop).mpr
    intro t ht _
    exact ⟨t,j,labelName,ht,hpre.1 t ht,hj,hLabel,ForcingAtomicBasic.eq_refl hM hpre labelName t ht⟩
  · apply (ForcingAtomicLaws.mem_congr_left hM hpre hy).mpr
    apply ForcingAtomicBasic.mem_mono hM hpre hpW hpz
    exact (ForcingQuotientName.mem_quotient_iff_isClass hM env rho G F mul I K labelMap top bit labels E
      hp hG hF hw hMu hLabelMap hTop hLabels hEHS hName hLocal.1.1 hpre hzW).mpr hclass

theorem holds_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records : Fin k) (families : Fin 16 → Fin k)
    {name p x y : M.Carrier .set}
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
    (hRecords : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q (env records))
    (hProjections : ForcingAssignedParameters.Projections (env high) (env Q) (env records) (env (families 0)) (env (families 1)) (env (families 2)) (env (families 3)) (env (families 4)) (env (families 5)) (env (families 6)) (env (families 7)) (env (families 8)) (env (families 9)) (env (families 10)) (env (families 11)) (env (families 12)) (env (families 13)) (env (families 14)) (env (families 15)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hName : ForcingQuotientName.Quotient env rho G F mul I K labelMap top bit labels E name)
    (h : ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env labels) p ∧
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name p := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hd : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env r p → ∃ s,
        (Project.FirstOrderSemantics.reduct M).mem s (env (rho 6)) ∧
        MapRel (orderFormula (rho 0) mul) env s r ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env labels) s ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y name s := by
    intro r hr hrp
    obtain ⟨t,htr,ht⟩ := h.2 r hr hrp
    have hb := witness_bounds hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records families
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hRecords hProjections hChains hEHS hName ht
    exact ⟨t,ForcingAtomicBasic.condition hM hb.1,htr,hb⟩
  constructor
  · apply ForcingAtomicBasic.mem_of_dense hM hpre h.1
    intro r hr hrp
    obtain ⟨t,ht,htr,hx,_⟩ := hd r hr hrp
    exact ⟨t,ht,htr,hx⟩
  · apply ForcingAtomicBasic.mem_of_dense hM hpre h.1
    intro r hr hrp
    obtain ⟨t,ht,htr,_,hy⟩ := hd r hr hrp
    exact ⟨t,ht,htr,hy⟩

def boundsSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y : Fin k)
    (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
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
    (.imp (ForcingOrbitParameterFamily.family rho I K B w G F mul q bound labels E zero names high objects maps (families 0) (families 1) Q id records)
    (.imp (ForcingAssignedParameters.projections high Q records (families 0) (families 1) (families 2) (families 3) (families 4) (families 5) (families 6) (families 7) (families 8) (families 9) (families 10) (families 11) (families 12) (families 13) (families 14) (families 15))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingQuotientName.quotient rho G F mul I K labelMap top bit labels E id name))
    (.conj (.imp (ForcingAssignedGraph.witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y) (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x labels p)) (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) y name p))))
      (.imp (ForcingAssignedGraph.holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y) (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) x labels p)) (ProjectSyntax.encode id (ForcingAtomicRelations.forces false (orderFormula (rho 0) mul) id (rho 6) y name p)))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingOrbitParameterFamily.family_freeClosed,ForcingAssignedParameters.projections_freeClosed,
      ForcingOrbitChains.family_freeClosed,ForcingAssignedGraph.witness_freeClosed,ForcingAssignedGraph.holds_freeClosed]

theorem bounds_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y : Fin k)
    (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (boundsSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
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
    ForcingSupportedNames.supported_semantics (M := M),ForcingOrbitParameterFamily.family_semantics hM,
    ForcingAssignedParameters.projections_semantics hM,ForcingOrbitChains.family_semantics hM,
    ForcingHS.hs_semantics (M := M),ForcingQuotientName.quotient_semantics (M := M),
    ForcingAssignedGraph.witness_semantics hM,ForcingAssignedGraph.holds_semantics hM,
    ForcingAtomicRelations.forces_semantics (M := M),id_eq]
  intro hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hRecords hProjections hChains hEHS hName
  exact ⟨witness_bounds hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records families
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hRecords hProjections hChains hEHS hName,
    holds_bounds hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records families
      hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hRecords hProjections hChains hEHS hName⟩

/-- Close in the SAME internal L using the already established L/Choice bridge. -/
theorem bounds_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y : Fin k)
    (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (boundsSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y families))) := by
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
  apply ConstructibleGround.relative_models hM (boundsSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (boundsSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y families)).mp
      (bounds_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero vertices names Q high objects maps records name p x y families hL hChoice)

end PPAC.Migration.ForcingAssignedGraphBounds
