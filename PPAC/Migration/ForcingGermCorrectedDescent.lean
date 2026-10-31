/- Fixed StableSelectors.corrected_descend:519. Transport the actual local
name along the same inverse representative, preserving the exact target diagram
and range/fixing subgroup, then consume the proved Preliminary descent. -/
import PPAC.Migration.ForcingGermCorrected
import PPAC.Migration.ForcingGermLocality
import PPAC.Migration.ForcingLocalNameTransport

namespace PPAC.Migration.ForcingGermCorrectedDescent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermCorrected (Corrected corrected)
open ConstructionComponentCofinal (Chain EncodedArrow)
open ForcingTailCodes (Entry)
open ForcingConditionGraphs (Permutation InverseGraph CompositionGraph function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem corrected_descend (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k)
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
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env target) (env tau))
    (hArrow : EncodedArrow (env (rho 0)) (env I) (env mul) (env q) (env source) (env target) (env n))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env source) (env label) (env tau)) :
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env target) (env label) (env tau) := by
  obtain ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,oldD,oldSource,oldLabel,oldTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMove,hLabel,hTau,hPreliminary⟩ := h
  have hFix := ForcingDiagramCarrier.reverse hPi hq hInverse ((hGerm pi).mp hpi).2.1
  have hTarget : ConstructionComponentCarrier.EncodedVertex (env (rho 0)) (env I) (env mul) (env q) (env target) := by
    obtain ⟨r0,a0,U0,rt,atIdx,Ut,_,ht,_,hvt,_⟩ := hArrow
    exact ⟨rt,atIdx,Ut,ht,hvt⟩
  obtain ⟨oldTarget,hMoveTarget⟩ := ForcingComponentMove.exists_move hM hInv hFix hTarget
  have hMovedArrow := ForcingComponentMove.move_arrow hMove hMoveTarget hArrow
  have hReverse : InverseGraph inv pi := fun x y => (hInverse y x).symm
  obtain ⟨conj,hConjPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hInv hPi hReverse
  obtain ⟨forward,hForward⟩ := ForcingProductFamily.exists_action hM hp hPi
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j))
      (env I) (env K) (env B) (env w) (env G) (env F) (env mu) inv pi conj act forward :=
    ⟨hp,hG,hInv,hPi,hReverse,hConjPerm,hConj,hAct,hForward,hF⟩
  have hMovedEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) oldTarget oldTau := by
    obtain ⟨rt,atIdx,Ut,A,Hfix,hCode,hRange,hFixing,hLocal⟩ := hEntry
    obtain ⟨rt',atIdx',Ut',movedRoot,hCode',hMovedCode,hOriginal,hMovedRoot,hComp⟩ := hMoveTarget
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode' hCode
    have hSubset := ForcingTailGroup.range_subset hOriginal.1 hRange
    obtain ⟨movedRange,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM hInv.1 (J := A)
    obtain ⟨movedFixing,hMovedFixing⟩ := ForcingLabelPermutations.exists_fixing hM (env G) movedRange
    exact ⟨movedRoot,atIdx',Ut',movedRange,movedFixing,hMovedCode,
      ForcingLocalNameTransport.range_image hRange hComp hImage,hMovedFixing,
      ForcingLocalNameTransport.local_name_move hM hData hBound hSubset hImage hFixing hMovedFixing hLocal hTau⟩
  have hMovedD := (ForcingLocalTransport.part_permutation hCohen).1.2 (env d) oldD hdd
  let other : Fin (k+5) → M.Carrier .set := Fin.cases oldD (Fin.cases oldSource (Fin.cases oldTarget (Fin.cases oldTau (Fin.cases oldLabel env))))
  let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInput := (ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot oldD oldSource oldLabel oldTau).mpr hPreliminary
  have hDescend := ForcingGermLocality.preliminary_descend hM hChoice other (fun j => up (rho j)) (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base) (up I) (up K) (up B) (up G) (up F) (up mul) (up q) (up zero) (up root) (up vertices) (up chain) (up names) (up bound) 0 1 2 (up n) 3 (up labels) (up E) (up codes) (up order) (up ranks) (up selection) (up top) (up rankBound) (up labelSet) (up tab) (up initialRoot) 4
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hVertices hChain hMovedD hCarrier hMovedEntry hMovedArrow hInput
  have hOutput := (ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot oldD oldTarget oldLabel oldTau).mp hDescend
  exact ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,oldD,oldTarget,oldLabel,oldTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMoveTarget,hLabel,hTau,hOutput⟩

def descentSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailCodes.entry rho G F bound target tau)
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q source target n)
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder id d source label tau)
    (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder id d target label tau)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ConstructionComponentCofinal.encodedArrow_freeClosed,ConstructionGermCosets.carrier_freeClosed,
      ForcingGermCorrected.corrected_freeClosed]

theorem descent_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM,
    ForcingTailCodes.entry_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    ForcingSupportedNames.supported_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionGermCosets.carrier_semantics hM,ForcingGermCorrected.corrected_semantics hM]
  exact corrected_descend hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder

theorem descent_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder))) := by
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
  apply ConstructibleGround.relative_models hM (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder)).mp
      (descent_models rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder hL hChoice)


end PPAC.Migration.ForcingGermCorrectedDescent
