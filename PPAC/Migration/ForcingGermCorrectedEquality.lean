/- Fixed StableSelectors.corrected_eq_iff:480. Align two actual Corrected
witnesses with the already proved corrected_selected; then consume the existing
Preliminary equality criterion and literal inverse EqF transport. -/
import PPAC.Migration.ForcingGermCorrected
import PPAC.Migration.ForcingGermEquality

namespace PPAC.Migration.ForcingGermCorrectedEquality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermCorrected (Corrected corrected)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem corrected_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (d vertex label tau : M.Carrier .set) :
    Corrected hM other (fun j => base (rho j)) (base I) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base root) (base w) (base chain) (base codes) (base order) (base ranks) (base selection) (base top) (base rankBound) (base labelSet) (base tab) (base r) (base K) (base B) (base zero) (base germGroup) (base quotient) (base nonidentity) (base high) (base detector) (base patternOrder) d vertex label tau ↔
      Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau := by
  simp only [Corrected,ForcingGermCorrected.Shift,he,
    ForcingAssignmentInvariant.preliminary_reindex hM env other base he]

theorem corrected_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma : Fin k)
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
    (hA : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau))
    (hB : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env otherLabel) (env sigma)) :
    ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env localRoot) (env tau) (env sigma) ↔ env label = env otherLabel := by
  obtain ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,movedD,movedVertex,movedLabel,movedTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMove,hLabel,hTau,hPreliminaryA⟩ := hA
  have hOtherI : (Project.FirstOrderSemantics.reduct M).mem (env otherLabel) (env I) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hInvB,_,_,_,_,_,hLabelB,_,_⟩ := hB
    exact ForcingConditionGraphs.function_input hInvB.1.1 hLabelB
  obtain ⟨movedOther,hOther,_⟩ := hInv.1.1.2 (env otherLabel) hOtherI
  obtain ⟨conj,hConjPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hPi hInv hInverse
  obtain ⟨forward,hForward⟩ := ForcingProductFamily.exists_action hM hp hPi
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j))
      (env I) (env K) (env B) (env w) (env G) (env F) (env mu) pi inv conj forward act :=
    ⟨hp,hG,hPi,hInv,hInverse,hConjPerm,hConj,hForward,hAct,hF⟩
  obtain ⟨movedSigma,hSigma⟩ := ForcingNameConjugacy.exists_action hM (ForcingProductFamily.action_permutation hAct).1 (env sigma)
  let other : Fin (k+11) → M.Carrier .set := (Fin.cases pi (Fin.cases inv (Fin.cases conj (Fin.cases forward (Fin.cases act (Fin.cases ac (Fin.cases movedD (Fin.cases movedVertex (Fin.cases movedSigma (Fin.cases movedOther (Fin.cases cls env)))))))))))
  let up : Fin k → Fin (k+11) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInput := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env otherLabel) (env sigma)).mpr hB
  have hAligned := (ForcingGermCorrected.corrected_selected hM hChoice other (fun j => up (rho j)) (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) 0 1 2 3 4 (up zero) (up root) (up vertices) (up chain) (up names) (up codes) (up order) (up group) (up r) (up rootIndex) (up rootU) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) 5 (up d) 6 (up vertex) 7 (up sigma) 8 (up otherLabel) (up diagrams) (up objImage) (up objects) (up maps) 9 (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder) (up selectorDomain) (up selector) 10
    hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hRange hHq hE hChain hCarrier hGroup hCohen hdd hRoot hFamily hType hMove hSigma hDiagrams hObj hObjects hCommon hRootFiber hOther hSelector hpi hClass hSelected hSigmaName).mp hInput
  have hPreliminaryB := (ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
    movedD movedVertex movedOther movedSigma).mp hAligned
  obtain ⟨r0,a0,U0,movedRoot,hCode0,hMovedCode,hr0,hMovedRoot,hComp⟩ := hMove
  obtain ⟨er,_,_⟩ := ConstructionComponentCarrier.code_injective hCode0 hCode
  have hMovedD := (ForcingLocalTransport.part_permutation hCohen).1.2 (env d) movedD hdd
  have hEqPreliminary := ForcingGermEquality.preliminary_eq_iff hM hChoice env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
    K B one mu history kappa mark H C incoming base zero vertices names rootIndex rootU group
    hw hMu hI hSmallD hMergers hRow hm hp hG hF hTop hChain hRoot hCarrier hOrder hRanks hFamily hTable
    hMovedD hMovedCode hPreliminaryA hPreliminaryB
  have hOrderRel (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (up (rho 0)) (up mul)) other x y ↔
      ForcingMapConditions.MapRel (ForcingProductSymmetry.orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,henv]
  have hReindex (dd rr tt ss : M.Carrier .set) :
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (up (rho 0)) (up mul)) other (env (rho 6)) dd rr tt ss ↔
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) dd rr tt ss := by
    simp only [ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hOrderRel]
  have hTransport := ForcingPersistentCovariance.eqF_transport_iff hM other (fun j => up (rho j)) (up mul) 4
    hm hp hInv hAct hCohen hdd hr0.1 hMovedRoot.1 hComp hTau hSigma
  have hSymmetry : ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) movedD movedRoot movedTau movedSigma ↔
      ForcingPrincipalFilter.EqF (ForcingProductSymmetry.orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env localRoot) (env tau) (env sigma) := by
    simpa only [er] using (hReindex movedD movedRoot movedTau movedSigma).symm.trans
      (hTransport.trans (hReindex (env d) r0 (env tau) (env sigma)))
  have hLabelsEqual : movedLabel = movedOther ↔ env label = env otherLabel := by
    constructor
    · intro hEq
      exact hInv.2.1 (env label) (env otherLabel) movedLabel hLabel (hEq.symm ▸ hOther)
    · intro hEq
      exact ForcingConditionGraphs.function_unique hInv.1.1 (hEq ▸ hLabel) hOther
  exact hSymmetry.symm.trans (hEqPreliminary.trans hLabelsEqual)

def equalitySentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
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
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex otherLabel sigma)
    (.iff (ForcingPrincipalFilter.eqF (ForcingProductSymmetry.orderFormula (rho 0) mul) id (rho 6) d localRoot tau sigma)
      (Project.Formula.extensionalEq (.bound label) (.bound otherLabel)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,
      ConstructionGermConditionSelector.selector_freeClosed,ForcingGermCorrected.corrected_freeClosed,
      ForcingOrdinalTable.table_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem equality_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
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
    ConstructionGermConditionSelector.selector_semantics hM,ForcingGermCorrected.corrected_semantics hM,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalTable.table_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact corrected_eq_iff hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma

theorem equality_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma))) := by
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
  apply ConstructibleGround.relative_models hM (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma)).mp
      (equality_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound zero root vertices chain names codes order group r rootIndex rootU ranks selection rankBound labelSet tab d vertex tau label diagrams objImage objects maps germGroup quotient nonidentity high detector patternOrder selectorDomain selector localRoot index U otherLabel sigma hL hChoice)


end PPAC.Migration.ForcingGermCorrectedEquality
