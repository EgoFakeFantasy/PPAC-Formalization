/- Pinned QuotientActions.Chain.tailFixer_fixes_label:327 and
StableSelectors.preliminaryPoint_move:392. Labels are actual raw label indices.
Reuse the existing common fibers and Preliminary covariance; no new quotient,
action, choice or completeness backend. Consumer: Corrected representative
independence under the simultaneous action on all four assignment coordinates. -/
import PPAC.Migration.ForcingGermCovariance
import PPAC.Migration.ForcingConcreteLabels

namespace PPAC.Migration.ForcingAssignmentCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)
open ForcingGermPreliminary (Preliminary preliminary)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The actual tail permutation fixes every member of the root label fiber. -/
theorem tail_fixes_label (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hCommon : ForcingConcreteLabels.CommonFibers D I mul objects maps)
    (hRootFiber : VertexFiber D mul objects maps root labelSet)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hTail : ForcingTailCovariance.TailFixes w D pi chain)
    (hLabel : (Project.FirstOrderSemantics.reduct M).mem label labelSet) :
    PureKuratowski.PairMember M label label pi := by
  obtain ⟨N,vertex,r,a,U,A,_,hNv,hCode,hA,hFix⟩ := hTail
  have hRelated := hChain.2.2.2.1 N vertex hNv
  have hv : ConstructionComponentCarrier.EncodedVertex D I mul q vertex := by
    obtain ⟨s,b,V,t,c,W,_,ht,_,hVertex,_⟩ := hRelated
    exact ⟨t,c,W,ht,hVertex⟩
  obtain ⟨X,hX⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj hv
  have hEqual := hCommon q root vertex labelSet X hRelated hRootFiber hX
  have hx : (Project.FirstOrderSemantics.reduct M).mem label X := hEqual ▸ hLabel
  obtain ⟨r',a',U',Or,hCode',hr,hFiber⟩ := hX
  obtain ⟨er,ea,eU⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
  subst r'
  have hOr := ((hObjects r Or).mp hr).2
  have eA := ForcingLabelSystem.range_unique hM hA hOr
  exact hFix label (eA.symm ▸ ((hFiber label).mp hx).1)

def tailLabelSentence {k : Nat} (w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily D diagrams objects)
    (.imp (ForcingConcreteLabels.commonFibers D I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber D mul objects maps root labelSet)
    (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain)
    (.imp (ForcingTailCovariance.tailFixes w D pi chain)
    (.imp (.mem (.bound label) (.bound labelSet))
    (ProjectSyntax.encode id (Source.SetLanguage.edge pi label label))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,
      ForcingComponentFibers.vertexFiber_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCovariance.tailFixes_freeClosed]

theorem tailLabel_models {k : Nat} (w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (tailLabelSentence w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,
    ForcingComponentFibers.vertexFiber_semantics hM,ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCovariance.tailFixes_semantics hM,KuratowskiZF.source_edge]
  exact tail_fixes_label hM

theorem tailLabel_kernel_certificate {k : Nat} (w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (tailLabelSentence w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label)) := by
  apply ModelTransfer.derives
  intro M hM
  exact tailLabel_models w D I mul q zero root vertices chain diagrams objImage objects maps labelSet pi label hM

theorem preliminaryPoint_move (hM : FirstOrder.Theory.Models M nativeZF)
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
    (hPreliminary : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env d) (env vertex) (env label) (env tau)) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env movedD) (env movedVertex) (env movedLabel) (env movedTau) := by
  have hFixed := tail_fixes_label hM hDiagrams hObj hObjects hCommon hRootFiber hChain
    ((hGroup (env pi)).mp hpiGroup).2 hPreliminary.1
  have he := ForcingConditionGraphs.function_unique hData.2.2.1.1.1 hLabelMove hFixed
  have hMoved := ForcingGermCovariance.preliminary_permute hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label
    hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
    hq hA hHq hE hChain hCarrier hGroup hpiGroup hc hdd hRoot hFamily hType hMove hTau hPreliminary
  exact he.symm ▸ hMoved

def covarianceSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k) : Project.Sentence where
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
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex label tau)
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id movedD movedVertex movedLabel movedTau))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingComponentMove.move_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed]

theorem covariance_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel)).TrueIn M := by
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
    ForcingStabilizer.action_semantics (M := M),ForcingGermPreliminary.preliminary_semantics hM,ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM]
  exact preliminaryPoint_move hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel

theorem covariance_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel))) := by
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
  apply ConstructibleGround.relative_models hM (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (covarianceSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel)).mp
      (covariance_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel hL hChoice)

end PPAC.Migration.ForcingAssignmentCovariance
