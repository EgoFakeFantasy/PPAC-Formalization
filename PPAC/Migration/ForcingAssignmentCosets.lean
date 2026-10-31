/- Pinned StableSelectors.CosetPredicate.shift_eq:348-357, specialized to the
actual four-coordinate Preliminary predicate. Build the actual difference
permutation and its complete action; consume proved tail invariance.
Consumer: StableSelectors.corrected_selected, not an abstract invariant oracle. -/
import PPAC.Migration.ForcingAssignmentInvariant
import PPAC.Migration.ConstructionGermSeparation

namespace PPAC.Migration.ForcingAssignmentCosets
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermPreliminary (Preliminary preliminary)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)
open ForcingConditionGraphs (Permutation InverseGraph CompositionGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Direct specialization of the existing entire Cohen action multiplication. -/
theorem cohen_composition (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi sigma product a b c : M.Carrier .set}
    (hp : ForcingProductFamily.Presentation D I K B w C S X Y P W)
    (hs : Permutation I sigma) (hprod : CompositionGraph I pi sigma product)
    (hA : ForcingLocalTransport.CohenPart C S X pi a)
    (hB : ForcingLocalTransport.CohenPart C S X sigma b)
    (hC : ForcingLocalTransport.CohenPart C S X product c) : CompositionGraph X a b c := by
  obtain ⟨f1,g1,_,hf1,_,hg1,ha,hga⟩ := hA
  obtain ⟨f2,g2,hf2,hfg2,hg2,hgg2,hb,hgb⟩ := hB
  obtain ⟨f3,g3,_,hf3,_,hg3,_,hgc⟩ := hC
  exact ForcingCohenActionLaws.permute_mul hM hp.2.2.1 hs.1 hf2.1 hg2.1 ha.1 hb.1 hprod
    hf1 hfg2 hf3 hg1 hgg2 hg3 hga hgb hgc

theorem shift_eq (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
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
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hGroup : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) (env group))
    (hSame : ConstructionGermCosets.Same (env w) (env (rho 0)) (env chain) (env sigma) (env pi))
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env inv) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env idx) (env U))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env inv) (env vertex) (env movedVertex))
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env ai) (env tau) (env movedTau))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hCommon : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hLabelMove : PureKuratowski.PairMember M (env label) (env movedLabel) (env inv))
    (hSigma : Permutation (env I) (env sigma))
    (hSigmaInv : Permutation (env I) (env sigmaInv))
    (hSigmaInverse : InverseGraph (env sigma) (env sigmaInv))
    (hSigmaAction : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) (env sigmaInv) (env sigmaAct))
    (hSigmaCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env sigmaInv) (env sigmaAc))
    (hSigmaD : PureKuratowski.PairMember M (env d) (env sigmaD) (env sigmaAc))
    (hSigmaMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env sigmaInv) (env vertex) (env sigmaVertex))
    (hSigmaTau : ForcingStabilizer.Action (env (rho 6)) (env sigmaAct) (env tau) (env sigmaTau))
    (hSigmaLabel : PureKuratowski.PairMember M (env label) (env sigmaLabel) (env sigmaInv))
    (hTauName : ForcingNames.IsName (env (rho 6)) (env tau)) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env movedD) (env movedVertex) (env movedLabel) (env movedTau) ↔
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env sigmaD) (env sigmaVertex) (env sigmaLabel) (env sigmaTau) := by
  obtain ⟨hp,hG,hPi,hInv,hInverse,_,_,hAct,hAI,hF⟩ := hData
  obtain ⟨diff,hDiff,hComp⟩ := ForcingConditionGraphs.exists_composition hM hSigmaInv hPi
  have hTail := (ConstructionGermCosets.same_iff_tail hChain hSigma hPi hSigmaInverse hComp).mp hSame
  obtain ⟨di,hdi,hDI⟩ := ForcingConditionGraphs.exists_inverse hM hDiff
  obtain ⟨dc,hdc,hDC⟩ := ForcingConjugationGraph.exists_graph hM hG hDiff hdi hDI
  obtain ⟨da,hDA⟩ := ForcingProductFamily.exists_action hM hp hDiff
  obtain ⟨dai,hDAI⟩ := ForcingProductFamily.exists_action hM hp hdi
  have hDataDiff : ForcingProductCovariance.SystemData (fun j => env (rho j))
      (env I) (env K) (env B) (env w) (env G) (env F) (env mu) diff di dc da dai :=
    ⟨hp,hG,hDiff,hdi,hDI,hdc,hDC,hDA,hDAI,hF⟩
  have hDiffGroup := (hGroup diff).mpr ⟨(hG diff).mpr hDiff,hTail⟩
  obtain ⟨dac,hDAC⟩ := ForcingLocalTransport.part_of_action hDA
  obtain ⟨pac,hPAC⟩ := ForcingLocalTransport.part_of_action hAct
  have hReverseD := ForcingAssignmentInvariant.cohen_inverse hp
    (fun x y => (hInverse y x).symm) hc hPAC hdd
  have hCohenComp := cohen_composition hM hp hPi hComp hSigmaCohen hPAC hDAC
  have hDiffD := (hCohenComp (env movedD) (env sigmaD)).mpr
    ⟨ForcingConditionGraphs.function_input (ForcingLocalTransport.part_permutation hPAC).1.1 hReverseD,
      env d,hReverseD,hSigmaD⟩
  have hReverseVertex := ForcingComponentMove.move_inverse hInv
    (fun x y => (hInverse y x).symm) hMove
  have hDiffVertex := ConstructionGermSeparation.move_composition hComp hReverseVertex hSigmaMove
  have hReverseLabel := (hInverse (env movedLabel) (env label)).mpr hLabelMove
  have hDiffLabel := (hComp (env movedLabel) (env sigmaLabel)).mpr
    ⟨ForcingConditionGraphs.function_input hPi.1.1 hReverseLabel,env label,hReverseLabel,hSigmaLabel⟩
  have hActionInverse := ForcingProductCovariance.inverse hM hp hPi hInverse hAct hAI
  have hReverseTau := ForcingNameConjugacy.inverse_action hM
    (ForcingProductFamily.action_permutation hAI).1 (ForcingProductFamily.action_permutation hAct).1
    (fun x y => (hActionInverse y x).symm) hTauName hTau
  have hActionComp := ForcingProductFamily.multiplication hM hp hPi hComp hSigmaAction hAct hDA
  have hDiffTau := ForcingNameConjugacy.composition hM
    (ForcingProductFamily.action_permutation hSigmaAction).1 (ForcingProductFamily.action_permutation hAct).1
    hActionComp hReverseTau hSigmaTau
  have hMovedName := ForcingNameConjugacy.name_preservation hM
    (ForcingProductFamily.action_permutation hAI).1 hTauName hTau
  let other : Fin (k+6) → M.Carrier .set :=
    Fin.cases diff (Fin.cases di (Fin.cases dc (Fin.cases da (Fin.cases dai (Fin.cases dac env)))))
  let up : Fin k → Fin (k+6) := fun j => j.succ.succ.succ.succ.succ.succ
  have henv (j : Fin k) : other (up j) = env j := by
    simp only [other,up,Fin.cases_succ]
  have hInvariant := ForcingAssignmentInvariant.preliminaryPoint_invariant hM hChoice other (fun j => up (rho j))
    (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) 0 1 2 3 4 (up zero) (up root) (up vertices) (up chain) (up names) (up codes) (up order) (up group) (up r) (up idx) (up U) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) 5 (up movedD) (up sigmaD) (up movedVertex) (up sigmaVertex) (up movedTau) (up sigmaTau) (up movedLabel) (up diagrams) (up objImage) (up objects) (up maps) (up sigmaLabel)
    hm hJ hDataDiff hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
    hq hA hHq hE hChain hCarrier hGroup hDiffGroup hDAC hDiffD hRoot hFamily hType hDiffVertex hDiffTau
    hDiagrams hObj hObjects hCommon hRootFiber hDiffLabel hMovedName
  have hLeft := ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
    (env movedD) (env movedVertex) (env movedLabel) (env movedTau)
  have hRight := ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
    (env sigmaD) (env sigmaVertex) (env sigmaLabel) (env sigmaTau)
  exact hLeft.symm.trans (hInvariant.symm.trans hRight)

def shiftSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
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
    (.imp (ConstructionGermCosets.same w (rho 0) chain sigma pi)
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) inv ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ForcingComponentMove.move (rho 0) I mul q inv vertex movedVertex)
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) ai tau movedTau))
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge inv label movedLabel))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I sigma))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I sigmaInv))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph sigma sigmaInv))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.action (rho 0) (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6) sigmaInv sigmaAct))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) sigmaInv sigmaAc))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge sigmaAc d sigmaD))
    (.imp (ForcingComponentMove.move (rho 0) I mul q sigmaInv vertex sigmaVertex)
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) sigmaAct tau sigmaTau))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge sigmaInv label sigmaLabel))
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) tau))
    (.iff (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id movedD movedVertex movedLabel movedTau)
      (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id sigmaD sigmaVertex sigmaLabel sigmaTau))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingComponentMove.move_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,ConstructionGermCosets.same_freeClosed]

theorem shift_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (shiftSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ForcingTailGroup.tailGroup_semantics hM,
    ForcingLocalTransport.cohenPart_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M),ForcingComponentMove.move_semantics hM,
    ForcingStabilizer.action_semantics (M := M),ForcingGermPreliminary.preliminary_semantics hM,ForcingNames.isName_semantics (M := M),
    Project.Formula.satisfies_iff_iff,ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ConstructionGermCosets.same_semantics hM,
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ForcingProductFamily.action_semantics (M := M)]
  exact shift_eq hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau

theorem shift_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (shiftSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau))) := by
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
  apply ConstructibleGround.relative_models hM (shiftSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (shiftSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau)).mp
      (shift_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel sigma sigmaInv sigmaAct sigmaAc sigmaD sigmaVertex sigmaLabel sigmaTau hL hChoice)

end PPAC.Migration.ForcingAssignmentCosets
