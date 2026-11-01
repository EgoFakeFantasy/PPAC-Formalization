/- Fixed OrbitAssignments.assigned_eq_iff:457-467.
Canonicalize both actual Assigned witnesses at the same vertex projection, using
the same whole-orbit parameter functions, then consume orbitAssignment_eq_iff. -/
import PPAC.Migration.ForcingAssigned
import PPAC.Migration.ForcingOrbitEquality

namespace PPAC.Migration.ForcingAssignedEquality
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

open ForcingAssigned (Assigned assigned Fields Functions Germs fields functions germs)

theorem assigned_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a : Fin k) (families : Fin 16 → Fin k)
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
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hFunctions : Functions env families (env Q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hIndex : PureKuratowski.PairMember M (env vertex) (env a) (env pr))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (hA : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau))
    (hB : Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env otherLabel) (env sigma)) :
    ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env localRoot) (env tau) (env sigma) ↔ env label = env otherLabel := by
  have hFirst := (ForcingAssigned.assigned_iff_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau families hm hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields).mp hA
  have hSecond := (ForcingAssigned.assigned_iff_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex otherLabel sigma families hm hJ hw hq hVertices hQuotient hProjection hReps hChains hFunctions hGerms hIndex hFields).mp hB
  exact ForcingOrbitEquality.orbitAssignment_eq_iff hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier
    hK hResult hm hJ hp hG hF hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hChain hCarrier hGroup hRoot hFamily hType hDiagrams hObj hObjects hCommon hRootFiber hSelector hOrder hRanks hTable hCode hSigmaName hFirst hSecond

def equalitySentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (functions families Q)
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertex a))
    (.imp (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
    (.imp (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex otherLabel sigma)
    (.iff (ForcingPrincipalFilter.eqF (ForcingProductSymmetry.orderFormula (rho 0) mul) id (rho 6) d localRoot tau sigma)
      (Project.Formula.extensionalEq (.bound label) (.bound otherLabel)))))))))))))))))))))))))))))))))))))))))))))
)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,
      ConstructionConcreteSelector.resultFormula_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,
      ConstructionGermConditionSelector.selector_freeClosed,ForcingAssigned.assigned_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,ForcingAssigned.functions_freeClosed,ForcingAssigned.germs_freeClosed,ForcingAssigned.fields_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem equality_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families)).TrueIn M := by
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
    ConstructionGermConditionSelector.selector_semantics hM,ForcingAssigned.assigned_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,ForcingAssigned.functions_semantics hM,ForcingAssigned.germs_semantics hM,KuratowskiZF.source_edge,ForcingAssigned.fields_semantics hM,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact assigned_eq_iff hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families

theorem equality_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families))) := by
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
  apply ConstructibleGround.relative_models hM (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families)).mp
      (equality_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma projection reps detectorDomain detectorSites patternCarrier Q pr a families hL hChoice)


end PPAC.Migration.ForcingAssignedEquality
