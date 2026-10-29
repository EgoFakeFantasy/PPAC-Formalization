/- Pinned GermSelectors.preliminary_permute:143-157.
Move condition, vertex and HS name together; preserve the SAME ground label,
Selected code, rank/type names and table witnesses. No root-fixing premise. -/
import PPAC.Migration.ForcingGermPreliminary
import PPAC.Migration.ForcingCodeLinkCovariance

namespace PPAC.Migration.ForcingGermCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingGermPreliminary (Preliminary preliminary)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem preliminary_permute (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label : Fin k)
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
    (hPreliminary : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env d) (env vertex) (env label) (env tau)) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env movedD) (env movedVertex) (env label) (env movedTau) := by
  obtain ⟨hj,hTauHS,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := hPreliminary
  have hMovedHS := (ForcingPairUnion.domain_semantics env rho G F (env movedTau)).mpr
    (ForcingProductCovariance.hs_action hM hData (env tau)
      ((ForcingPairUnion.domain_semantics env rho G F (env tau)).mp hTauHS) (env movedTau) hTau)
  have hSelected := (ForcingCodeSelection.isSelected_covariance hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group a
    hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
    hq hA hHq hE hChain hCarrier ha hGroup hpiGroup hc hdd).mpr hSel
  refine ⟨hj,hMovedHS,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSelected,?_,?_,?_⟩
  · exact ForcingCodeLinkCovariance.tail_eq_permute_over hM hChoice env rho
      w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q A zero root vertices chain group ac d movedD r idx U
      (env selection) ntheta hw hMu hI hSmallD hMergers hRow hm hJ hData hq hA hChain hGroup hpiGroup hc hdd hRoot
      hType.2 (ForcingOrdinalRoot.check_supported hM (fun j => env (rho j)) hData.1 hTop hTheta) hEqT
  · exact ForcingCodeLinkCovariance.tail_eq_permute_over hM hChoice env rho
      w mu history kappa one mark H C incoming base I K B G F mul pi inv c act ai q A zero root vertices chain group ac d movedD r idx U
      na nbeta hw hMu hI hSmallD hMergers hRow hm hJ hData hq hA hChain hGroup hpiGroup hc hdd hRoot
      (hFamily a ha na hRank).2 (ForcingOrdinalRoot.check_supported hM (fun j => env (rho j)) hData.1 hTop hBeta) hEqR
  · exact ForcingCodeLinkCovariance.links_permute_over hM env rho
      I K B w G F mu pi inv c ai one mul act q zero root vertices chain bound names ac d movedD vertex movedVertex tau movedTau a
      hm hData hw hChain ((hCarrier a).mp ha) ((hGroup (env pi)).mp hpiGroup).2 hc hdd hMove hTau hLink


def covarianceSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label : Fin k) : Project.Sentence where
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
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex label tau)
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id movedD movedVertex label movedTau))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingComponentMove.move_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed]

theorem covariance_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label)).TrueIn M := by
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
    ForcingStabilizer.action_semantics (M := M),ForcingGermPreliminary.preliminary_semantics hM]
  exact preliminary_permute hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label

theorem covariance_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label))) := by
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
  apply ConstructibleGround.relative_models hM (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label)).mp
      (covariance_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label hL hChoice)

end PPAC.Migration.ForcingGermCovariance
