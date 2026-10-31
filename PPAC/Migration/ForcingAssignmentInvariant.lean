/- Pinned StableSelectors.preliminaryPoint_invariant:401-408.
Use actual inverse actions and the existing parameter-witness extension method
from ForcingCodeRanks.selected_reindex. The inverse conjugation and Cohen action
are constructed, not assumed. Consumer: Corrected representative independence. -/
import PPAC.Migration.ForcingAssignmentCovariance

namespace PPAC.Migration.ForcingAssignmentInvariant
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermPreliminary (Preliminary PreliminaryAt preliminary)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Reuse the same atomic recursion and selected predicate after adding witnesses. -/
theorem preliminary_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i)
    (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (d vertex label tau : M.Carrier .set) :
    Preliminary hM other (fun j => base (rho j)) (base I) (base G) (base F) (base mul)
      (base q) (base bound) (base labels) (base E) (base root) (base w) (base chain)
      (base codes) (base order) (base ranks) (base selection) (base top) (base rankBound)
      (base labelSet) (base tab) (base r) d vertex label tau ↔
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label tau := by
  have hR (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (base (rho 0)) (base mul)) other x y ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  simp only [Preliminary,PreliminaryAt,ForcingPairUnion.domain_semantics,
    ForcingCodeRanks.selected_reindex env other base he,ForcingCodeLinks.Links,
    ForcingPrincipalFilter.EqF,ForcingEquivariantMix.forces_order_congr hR,he]

/-- Reverse the same actual Cohen graph using the existing coordinate inverses. -/
theorem cohen_inverse {D I K B w C S X Y P W pi inv ac ai d e : M.Carrier .set}
    (hp : ForcingProductFamily.Presentation D I K B w C S X Y P W)
    (hi : ForcingConditionGraphs.InverseGraph pi inv)
    (hc : ForcingLocalTransport.CohenPart C S X pi ac)
    (hai : ForcingLocalTransport.CohenPart C S X inv ai)
    (hde : PureKuratowski.PairMember M d e ac) : PureKuratowski.PairMember M e d ai := by
  obtain ⟨f,t,hf,hfg,ht,htg,_,ha⟩ := hc
  obtain ⟨fi,ti,hfi,hfig,hti,htig,_,hai⟩ := hai
  have hfiInv := ForcingCohenCoordinates.inverse_graph hf.1 hfi.1 hi hfg hfig
  have htiInv := ForcingCohenCoordinates.inverse_graph ht.1 hti.1 hfiInv htg htig
  obtain ⟨hd,he,hImage⟩ := (ha d e).mp hde
  exact (hai e d).mpr ⟨he,hd,ForcingCohenOrderAction.reverse_image ht htiInv
    ((hp.2.2.1 d).mp hd).1 hImage⟩

theorem preliminaryPoint_invariant (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k)
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
    (hpiGroup : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env group))
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env idx) (env U))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) (env vertex) (env movedVertex))
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env act) (env tau) (env movedTau))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hCommon : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hLabelMove : PureKuratowski.PairMember M (env label) (env movedLabel) (env pi))
    (hTauName : ForcingNames.IsName (env (rho 6)) (env tau)) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env movedD) (env movedVertex) (env movedLabel) (env movedTau) ↔
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env d) (env vertex) (env label) (env tau) := by
  constructor
  · intro hPreliminary
    obtain ⟨hp,hG,hPi,hInv,hInverse,_,_,hAct,hAI,hF⟩ := hData
    obtain ⟨ci,hci,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hInv hPi
      (fun x y => (hInverse y x).symm)
    have hInverseData : ForcingProductCovariance.SystemData (fun j => env (rho j))
        (env I) (env K) (env B) (env w) (env G) (env F) (env mu)
        (env inv) (env pi) ci (env ai) (env act) :=
      ⟨hp,hG,hInv,hPi,(fun x y => (hInverse y x).symm),hci,hConj,hAI,hAct,hF⟩
    obtain ⟨aci,haci⟩ := ForcingLocalTransport.part_of_action hAI
    have hReverseD := cohen_inverse hp hInverse hc haci hdd
    have hReverseVertex := ForcingComponentMove.move_inverse hPi hInverse hMove
    have hReverseLabel := (hInverse (env label) (env movedLabel)).mp hLabelMove
    have hActionInverse := ForcingProductCovariance.inverse hM hp hPi hInverse hAct hAI
    have hReverseTau := ForcingNameConjugacy.inverse_action hM
      (ForcingProductFamily.action_permutation hAct).1
      (ForcingProductFamily.action_permutation hAI).1 hActionInverse hTauName hTau
    have hInvGroup := (hGroup (env inv)).mpr ⟨(hG (env inv)).mpr hInv,
      ForcingTailGroup.tail_inverse hInverse ((hGroup (env pi)).mp hpiGroup).2⟩
    let other : Fin (k+2) → M.Carrier .set := Fin.cases ci (Fin.cases aci env)
    let up : Fin k → Fin (k+2) := fun j => j.succ.succ
    have henv (j : Fin k) : other (up j) = env j := by
      simp only [other,up,Fin.cases_succ]
    have hInput := (preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
      (env movedD) (env movedVertex) (env movedLabel) (env movedTau)).mpr hPreliminary
    have hBack := ForcingAssignmentCovariance.preliminaryPoint_move hM hChoice other (fun j => up (rho j))
      (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up inv) (up pi) 0 (up ai) (up act) (up zero) (up root) (up vertices) (up chain) (up names) (up codes) (up order) (up group) (up r) (up idx) (up U) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) 1 (up movedD) (up d) (up movedVertex) (up vertex) (up movedTau) (up tau) (up movedLabel) (up diagrams) (up objImage) (up objects) (up maps) (up label)
      hm hJ hInverseData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
      hq hA hHq hE hChain hCarrier hGroup hInvGroup haci hReverseD hRoot hFamily hType hReverseVertex hReverseTau
      hDiagrams hObj hObjects hCommon hRootFiber hReverseLabel hInput
    exact (preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
      (env d) (env vertex) (env label) (env tau)).mp hBack
  · intro hPreliminary
    exact ForcingAssignmentCovariance.preliminaryPoint_move hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel
      hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
      hq hA hHq hE hChain hCarrier hGroup hpiGroup hc hdd hRoot hFamily hType hMove hTau
      hDiagrams hObj hObjects hCommon hRootFiber hLabelMove hPreliminary

def invarianceSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k) : Project.Sentence where
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
    (.imp (.mem (.bound pi) (.bound group))
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) pi ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi vertex movedVertex)
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) act tau movedTau))
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pi label movedLabel))
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) tau))
    (.iff (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id movedD movedVertex movedLabel movedTau)
      (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex label tau)))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingComponentMove.move_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed]

theorem invariance_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (invarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
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
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM]
  exact preliminaryPoint_invariant hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel

theorem invariance_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (invarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel))) := by
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
  apply ConstructibleGround.relative_models hM (invarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (invarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel)).mp
      (invariance_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel hL hChoice)

end PPAC.Migration.ForcingAssignmentInvariant
