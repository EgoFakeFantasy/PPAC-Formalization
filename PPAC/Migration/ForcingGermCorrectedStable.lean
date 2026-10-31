/- Fixed OrbitAssignments.corrected_stable:30-40. Consume the already proved
Preliminary stability and StableAt permutation on the actual inverse representative.
No new forcing, locality or choice backend. -/
import PPAC.Migration.ForcingGermCorrectedDescent
import PPAC.Migration.ForcingStableAt

namespace PPAC.Migration.ForcingGermCorrectedStable
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermCorrected (Corrected corrected)
open ForcingStableAt (StableAt stableAt)
open ForcingProductSymmetry (orderFormula)
open ConstructionComponentCofinal (Chain)
open ForcingTailCodes (Entry)
open ForcingSupportSize (Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem stable_reindex {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i) (rho : Fin 7 → Fin k)
    (G F mul bound labels E : Fin k) (d vertex tau : M.Carrier .set) :
    StableAt (orderFormula (base (rho 0)) (base mul)) (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F))
      other (fun j => other (base (rho j))) (other (base G)) (other (base F)) (other (base mul))
      (other (base bound)) (other (base labels)) (other (base E)) d vertex tau ↔
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) d vertex tau := by
  have hR (x y : M.Carrier .set) :
      ForcingMapConditions.MapRel (orderFormula (base (rho 0)) (base mul)) other x y ↔
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env x y := by
    simp only [ForcingProductSymmetry.orderFormula_semantics,he]
  have hH (x : M.Carrier .set) :
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain (fun j => base (rho j)) (base G) (base F)) other x ↔
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env x := by
    simp only [ForcingPairUnion.domain_semantics,he]
  simp only [StableAt,he,ForcingSeparation.force_congr hR hH,
    ForcingForcedAvailability.Carrier,ForcingForcedAvailability.Available,ForcingPrincipalFilter.EqF,
    ForcingEquivariantMix.forces_order_congr hR]

theorem corrected_stable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k)
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
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) (env d) (env vertex) (env tau) := by
  obtain ⟨pi,cls,hpi,hClass,hSelected,inv,act,ac,oldD,oldVertex,oldLabel,oldTau,
    hPi,hInv,hInverse,hAct,hCohen,hdd,hMove,hLabel,hTau,hPreliminary⟩ := h
  have hReverse : ForcingConditionGraphs.InverseGraph inv pi := fun x y => (hInverse y x).symm
  obtain ⟨conj,hConjPerm,hConj⟩ := ForcingConjugationGraph.exists_graph hM hG hInv hPi hReverse
  obtain ⟨forward,hForward⟩ := ForcingProductFamily.exists_action hM hp hPi
  have hData : ForcingProductCovariance.SystemData (fun j => env (rho j))
      (env I) (env K) (env B) (env w) (env G) (env F) (env mu) inv pi conj act forward :=
    ⟨hp,hG,hInv,hPi,hReverse,hConjPerm,hConj,hAct,hForward,hF⟩
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hOmegaSmall := (ForcingSupportSize.native_small hM (env w) (env mu)).mpr hMu.2
  obtain ⟨hLabelsHS,hLabelsFix⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j))
    hp hG hNormal hF hw hOmegaSmall hLabelMap hTop hLabels
  have hBound := ForcingLocalNameTransport.bound_supported hM hp hG hLabelsHS hLabelsFix
    ((ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound)
  obtain ⟨r,index,U,A,Hfix,hCode,hRange,hFixing,hLocal⟩ := hEntry
  obtain ⟨r0,index0,U0,oldRoot,hCode0,hOldCode,hr,hOldRoot,hComp⟩ := hMove
  obtain ⟨er,ei,eU⟩ := ConstructionComponentCarrier.code_injective hCode hCode0
  subst r0; subst index0; subst U0
  obtain ⟨oldRange,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM hInv.1 (J := A)
  obtain ⟨oldFix,hOldFix⟩ := ForcingLabelPermutations.exists_fixing hM (env G) oldRange
  have hOldRange := ForcingLocalNameTransport.range_image hRange hComp hImage
  have hOldLocal := ForcingLocalNameTransport.local_name_move hM hData hBound
    (ForcingTailGroup.range_subset hr.1 hRange) hImage hFixing hOldFix hLocal hTau
  have hOldEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) oldVertex oldTau :=
    ⟨oldRoot,index,U,oldRange,oldFix,hOldCode,hOldRange,hOldFix,hOldLocal⟩
  obtain ⟨oldZ,hOldZ⟩ := ForcingSupportingRoot.exists_code hM oldD oldRoot
  have hOldD := (ForcingLocalTransport.part_permutation hCohen).1.2 (env d) oldD hdd
  let other : Fin (k+9) → M.Carrier .set := Fin.cases oldD (Fin.cases oldVertex (Fin.cases oldTau
    (Fin.cases oldLabel (Fin.cases oldRoot (Fin.cases index (Fin.cases U (Fin.cases oldZ (Fin.cases forward env))))))))
  let up : Fin k → Fin (k+9) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInput := (ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot oldD oldVertex oldLabel oldTau).mpr hPreliminary
  have hStable := ForcingGermLocality.preliminary_stable hM hChoice other (fun j => up (rho j))
    (up w) (up mu) (up history) (up kappa) (up one) (up mark) (up H) (up C) (up incoming) (up base)
    (up I) (up K) (up B) (up G) (up F) (up mul) (up labelMap) (up top) (up bit) (up labels) (up bound)
    (up E) (up q) (up Aq) (up Hq) (up zero) (up root) (up vertices) (up chain) (up names)
    1 4 5 6 0 2 7 (up codes) (up order) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) (up initialRoot) 3
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hChain
    hOldCode hOldD hOldZ hCarrier hOldEntry hInput
  have hOldStable : StableAt (orderFormula (up (rho 0)) (up mul)) (ForcingPairUnion.domain (fun j => up (rho j)) (up G) (up F))
      other (fun j => other (up (rho j))) (env G) (env F) (env mul) (env bound) (env labels) (env E) oldD oldVertex oldTau :=
    ⟨oldRoot,index,U,oldRange,oldFix,oldZ,hOldCode,hOldRange,hOldFix,hOldLocal,hOldZ,hStable⟩
  have hPiFix := ((hGerm pi).mp hpi).2.1
  have hPiHq : (Project.FirstOrderSemantics.reduct M).mem pi (env Hq) := by
    apply (hHq pi).mpr
    refine ⟨(hG pi).mpr hPi,?_⟩
    intro x hx
    obtain ⟨j,_,hjx⟩ := (hAq x).mp hx
    obtain ⟨_,y,hjy,hyx⟩ := (hPiFix j x).mp hjx
    have e : y = x := ForcingConditionGraphs.function_unique hq.1.1 hjy hjx
    exact e ▸ hyx
  obtain ⟨forwardConj,hForwardData⟩ := ForcingLocalNameTransport.reverse_data hM hData
  obtain ⟨forwardCohen,hForwardCohen⟩ := ForcingLocalTransport.part_of_action hForward
  have hBackD := ForcingAssignmentInvariant.cohen_inverse hp hReverse hCohen hForwardCohen hdd
  have hInverseAction := ForcingProductCovariance.inverse hM hp hInv hReverse hAct hForward
  have hBackTau := ForcingNameConjugacy.inverse_action hM (ForcingProductFamily.action_permutation hAct).1
    (ForcingProductFamily.action_permutation hForward).1 hInverseAction (ForcingHS.isName hLocal.1.1) hTau
  have hForwardRel := (ForcingProductFamily.mapRel_action (fun j => env (rho j)) pi forward).mpr hForward
  have hBackMove := ForcingComponentMove.move_inverse hInv hReverse
    (show ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) inv (env vertex) oldVertex from
      ⟨r,index,U,oldRoot,hCode,hOldCode,hr,hOldRoot,hComp⟩)
  have hResult := ForcingStableAt.permute hM other (fun j => up (rho j)) (up G) (up F) (up mul) 8
    hm hForwardData hNormal hBound
    (hLabelsFix pi ((hG pi).mpr hPi) forward hForwardRel) (hE pi hPiHq forward hForwardRel)
    hForwardCohen hBackD hBackMove hBackTau hOldStable
  exact (stable_reindex env other up henv rho G F mul bound labels E (env d) (env vertex) (env tau)).mp hResult

def stableSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul bound labels E d vertex tau)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingTailCodes.carrier_freeClosed,
      ForcingTailCodes.entry_freeClosed,ConstructionGermCosets.carrier_freeClosed,
      ForcingGermCorrected.corrected_freeClosed,ForcingStableAt.stableAt_freeClosed]

theorem stable_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
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
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ForcingTailCodes.entry_semantics hM,
    ConstructionGermCosets.carrier_semantics hM,ForcingGermCorrected.corrected_semantics hM,ForcingStableAt.stableAt_semantics hM]
  exact corrected_stable hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder

theorem stable_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder))) := by
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
  apply ConstructibleGround.relative_models hM (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder)).mp
      (stable_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex d tau codes order ranks selection rankBound labelSet tab initialRoot label germGroup quotient nonidentity high detector patternOrder hL hChoice)


end PPAC.Migration.ForcingGermCorrectedStable
