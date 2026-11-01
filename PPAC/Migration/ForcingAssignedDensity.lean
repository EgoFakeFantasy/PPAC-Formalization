/- Fixed OrbitAssignments.assigned_total:471-489 and assigned_onto:491-508.
Consume density on the same actual chosen representative chain, then introduce
the single Assigned predicate using the same fixed per-orbit function values.
The existence of the complete auxiliary function family remains an assembly input. -/
import PPAC.Migration.ForcingAssigned

namespace PPAC.Migration.ForcingAssignedDensity
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

open ForcingAssigned (Assigned assigned Fields fields assigned_intro)

theorem assigned_total (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k)
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
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env orbitQuotient) (env (families 0)))
    (hVertexIndex : PureKuratowski.PairMember M (env vertex) (env orbitIndex) (env orbitProjection))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env orbitQuotient) (env (families 0)) (env (families 1)))
    (hFields : Fields env families (env orbitIndex) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env vertex) (env vertexLabels)) :
    ∃ e tau, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧
      ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) tau ∧
      Assigned hM env rho I G F mul q bound labels E w top K B zero orbitQuotient families e (env vertex) (env label) tau := by
  obtain ⟨e,tau,he,hde,hEntry,hOrbit⟩ := ForcingOrbitRepresentativeDensity.representative_total hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection (families 0) orbitIndex (families 1)
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hd hj hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hCount hQuotient hProjection hReps hFields.1 hVertexIndex hChains hFields.2.1 hVertexFiber
  exact ⟨e,tau,he,hde,hEntry,assigned_intro hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder orbitQuotient orbitIndex families e (env vertex) (env label) tau
    (ForcingConditionGraphs.function_input hReps.1.1 hFields.1) hFields hOrbit⟩

def totalSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ConstructionGermDetectors.representatives vertices orbitQuotient (families 0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitProjection vertex orbitIndex))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices orbitQuotient (families 0) (families 1))
    (.imp (fields families orbitIndex root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (ForcingTailCodes.entry (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ bound.succ.succ vertex.succ.succ 0)
      (assigned (fun j => (rho j).succ.succ) I.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ w.succ.succ top.succ.succ K.succ.succ B.succ.succ zero.succ.succ orbitQuotient.succ.succ (fun j => (families j).succ.succ) 1 vertex.succ.succ label.succ.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingAssigned.assigned_freeClosed,ForcingAssigned.fields_freeClosed,
      ForcingOrbitCounts.rootCounts_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed, ConstructionConcreteSelector.resultFormula_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem total_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex families)).TrueIn M := by
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
    ForcingAssigned.assigned_semantics hM,ForcingAssigned.fields_semantics hM]
  intro hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hd hj hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hCount hQuotient hProjection hReps hVertexIndex hChains hFields hVertexFiber
  obtain ⟨e,tau,he,hde,hEntry,hAssigned⟩ := assigned_total hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex families
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hd hj hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hCount hQuotient hProjection hReps hVertexIndex hChains hFields hVertexFiber
  let other : Fin (k+2) → M.Carrier .set := Fin.cases tau (Fin.cases e env)
  have hLift := (ForcingAssigned.assigned_reindex hM env other (fun j => j.succ.succ) (fun _ => rfl) rho I G F mul q bound labels E w top K B zero orbitQuotient families e (env vertex) (env label) tau).mpr hAssigned
  exact ⟨e,tau,he,hde,hEntry,hLift⟩

theorem total_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex families))) := by
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
  apply ConstructibleGround.relative_models hM (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (totalSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex families)).mp
      (total_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab label d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps vertexLabels orbitQuotient orbitProjection orbitIndex families hL hChoice)




theorem assigned_onto (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k)
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
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env orbitQuotient) (env (families 0)))
    (hVertexIndex : PureKuratowski.PairMember M (env vertex) (env orbitIndex) (env orbitProjection))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env orbitQuotient) (env (families 0)) (env (families 1)))
    (hFields : Fields env families (env orbitIndex) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (hStable : StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) (env d) (env vertex) (env tau)) :
    ∃ e label, ForcingCohenConditions.Condition (env (rho 2)) (env w) e ∧
      ForcingPowerName.Subset (env d) e ∧ (Project.FirstOrderSemantics.reduct M).mem label (env I) ∧
      Assigned hM env rho I G F mul q bound labels E w top K B zero orbitQuotient families e (env vertex) label (env tau) := by
  obtain ⟨e,label,he,hde,hLabel,hOrbit⟩ := ForcingOrbitRepresentativeDensity.representative_onto hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection (families 0) orbitIndex (families 1)
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hNames hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hd hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hCount hQuotient hProjection hReps hFields.1 hVertexIndex hChains hFields.2.1 hStable
  exact ⟨e,label,he,hde,hLabel,assigned_intro hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder orbitQuotient orbitIndex families e (env vertex) label (env tau)
    (ForcingConditionGraphs.function_input hReps.1.1 hFields.1) hFields hOrbit⟩

def ontoSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ConstructionGermDetectors.representatives vertices orbitQuotient (families 0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge orbitProjection vertex orbitIndex))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices orbitQuotient (families 0) (families 1))
    (.imp (fields families orbitIndex root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
    (.imp (stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul bound labels E d vertex tau)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ.succ w.succ.succ 1))
      (.conj (Project.Formula.subset (.bound d.succ.succ) (.bound 1))
      (.conj (.mem (.bound 0) (.bound I.succ.succ))
      (assigned (fun j => (rho j).succ.succ) I.succ.succ G.succ.succ F.succ.succ mul.succ.succ q.succ.succ bound.succ.succ labels.succ.succ E.succ.succ w.succ.succ top.succ.succ K.succ.succ B.succ.succ zero.succ.succ orbitQuotient.succ.succ (fun j => (families j).succ.succ) 1 vertex.succ.succ 0 tau.succ.succ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.candidates_freeClosed,ForcingStableAt.stableAt_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingAssigned.assigned_freeClosed,ForcingAssigned.fields_freeClosed,
      ForcingOrbitCounts.rootCounts_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed, ConstructionConcreteSelector.resultFormula_freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed]

theorem onto_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex families)).TrueIn M := by
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
    ForcingAssigned.assigned_semantics hM,ForcingAssigned.fields_semantics hM]
  intro hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hNames hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hd hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hCount hQuotient hProjection hReps hVertexIndex hChains hFields hStable
  obtain ⟨e,label,he,hde,hLabel,hAssigned⟩ := assigned_onto hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex families
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hNames hVertices hCarrier hRoot hRootA hRootH hIncl hOrder hRanks hSelection hFamily hType hRank hTable hd hK hResult hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hFibers hRootFiber hCount hQuotient hProjection hReps hVertexIndex hChains hFields hStable
  let other : Fin (k+2) → M.Carrier .set := Fin.cases label (Fin.cases e env)
  have hLift := (ForcingAssigned.assigned_reindex hM env other (fun j => j.succ.succ) (fun _ => rfl) rho I G F mul q bound labels E w top K B zero orbitQuotient families e (env vertex) label (env tau)).mpr hAssigned
  exact ⟨e,label,he,hde,hLabel,hLift⟩

theorem onto_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex families))) := by
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
  apply ConstructibleGround.relative_models hM (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (ontoSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex families)).mp
      (onto_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex codes order ranks selection group r rootIndex rootU rootA rootH rankBound labelSet tab tau d germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high patternCarrier patternOrder selectorDomain selector diagrams objImage objects arrows mapImage maps orbitQuotient orbitProjection orbitIndex families hL hChoice)


end PPAC.Migration.ForcingAssignedDensity
