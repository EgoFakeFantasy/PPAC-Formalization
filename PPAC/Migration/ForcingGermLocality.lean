/- Pinned GermSelectors.preliminary_stable:115 and preliminary_descend:134.
Consume the existing Links producers with the SAME existential code and names;
keep all stronger internal conditions and the exact availability ideal. -/
import PPAC.Migration.ForcingGermPreliminary
import PPAC.Migration.ForcingLinkedStability
import PPAC.Migration.ForcingCodeLinkClosure

namespace PPAC.Migration.ForcingGermLocality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedArrow EncodedCommon)
open ForcingTailCodes (ChainCode At Entry Represents)
open ForcingGermPreliminary (Preliminary preliminary)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem preliminary_stable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label : Fin k)
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
    (hc : Code (env vertex) (env r) (env index) (env U))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env r))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hPreliminary : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot (env d) (env vertex) (env label) (env tau)) :
    ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) (env z) (ForcingEligibility.isClass 0 1 2) ∧
    ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset (env d) e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env index) (env tau) (env U) := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := hPreliminary
  exact ForcingLinkedStability.links_stable_over hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hChain hc hd hz ((hCarrier a).mp ha) hEntry hSel.1 hLink


theorem preliminary_descend (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label : Fin k)
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
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env target) (env tau))
    (hArrow : EncodedArrow (env (rho 0)) (env I) (env mul) (env q) (env source) (env target) (env n))
    (hPreliminary : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot (env d) (env source) (env label) (env tau)) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot (env d) (env target) (env label) (env tau) := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := hPreliminary
  refine ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,?_⟩
  exact ForcingCodeLinkClosure.links_descend_over hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau a
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hVertices hChain hd ((hCarrier a).mp ha) hEntry hArrow hLink

def stableSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label : Fin k) : Project.Sentence where
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
    (.imp (ConstructionComponentCarrier.code vertex r index U)
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d r))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot id d vertex label tau)
    (.conj (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (Source.SetLanguage.args3 tau labels E) (rho 6) z (ForcingEligibility.isClass 0 1 2))) (.forallE (.imp (.mem (.bound 0) (.bound (rho 3).succ)) (.imp (Project.Formula.subset (.bound d.succ) (.bound 0)) (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ index.succ tau.succ U.succ)))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed,ForcingForcedAvailability.carrier_freeClosed]


theorem stable_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOmega_iff,
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
    ConstructionComponentCarrier.code_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingTailCodes.carrier_semantics hM,ForcingTailCodes.entry_semantics hM,
    ForcingGermPreliminary.preliminary_semantics hM,ForcingFormula.formula_semantics (M := M),ForcingForcedAvailability.carrier_semantics hM]
  exact preliminary_stable hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label


theorem stable_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label))) := by
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
  apply ConstructibleGround.relative_models hM (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (stableSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label)).mp
      (stable_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z codes order ranks selection rankBound labelSet tab initialRoot label hL hChoice)


def descentSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label : Fin k) : Project.Sentence where
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
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailCodes.entry rho G F bound target tau)
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q source target n)
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot id d source label tau)
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab initialRoot id d target label tau)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCofinal.encodedArrow_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed]


theorem descent_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),



    ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCofinal.encodedArrow_semantics hM,ForcingTailCodes.carrier_semantics hM,
    ForcingTailCodes.entry_semantics hM,ForcingGermPreliminary.preliminary_semantics hM]
  exact preliminary_descend hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label


theorem descent_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label))) := by
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
  apply ConstructibleGround.relative_models hM (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (descentSentence rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label)).mp
      (descent_models rho w mu history kappa one mark H C incoming base I K B G F mul q zero root vertices chain names bound d source target n tau labels E codes order ranks selection top rankBound labelSet tab initialRoot label hL hChoice)

end PPAC.Migration.ForcingGermLocality
