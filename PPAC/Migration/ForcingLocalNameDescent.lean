/- Pinned LocalQuotients.localName_descent:374-395.
Consume the completed support_descent, normalize its actual witness into the
ground carrier, and preserve both original restricted forcing equalities. -/
import PPAC.Migration.ForcingSupportDescent
import PPAC.Migration.ForcingLocalNormalize

namespace PPAC.Migration.ForcingLocalNameDescent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (Injection Small)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingAtomicRelations (Forces)
open ForcingSupportedNames (Range Supported)
open ForcingSupportingRoot (Code code_mem exists_code code_le restricted_condition)
open ConstructionCohenCompatibility (Restricted)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem localName_descent (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v
      A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hFilter : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hp : Injection (env (rho 0)) I p) (hs0 : Injection (env (rho 0)) I s0)
    (hs1 : Injection (env (rho 0)) I s1) (hv : Injection (env (rho 0)) I v)
    (hs0p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s0 p)
    (hs1p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s1 p)
    (hInter : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) s0 s1 p)
    (hv0 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s0)
    (hv1 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s1)
    (hRange0 : Range (env (rho 0)) s0 A0) (hRange1 : Range (env (rho 0)) s1 A1)
    (hRangeP : Range (env (rho 0)) p Ap)
    (hFix0 : ForcingLabelPermutations.Fixing (env G) A0 fixing0)
    (hFix1 : ForcingLabelPermutations.Fixing (env G) A1 fixing1)
    (hFixP : ForcingLabelPermutations.Fixing (env G) Ap fixingP)
    (hn0 : ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) nameBound fixing0 sigma0)
    (hn1 : ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) nameBound fixing1 sigma1)
    (hd : ForcingCohenConditions.Condition (env (rho 2)) w d)
    (hRestr0 : Restricted A0 d d0) (hRestr1 : Restricted A1 d d1)
    (hz : Code z d v) (hz0 : Code z0 d0 s0) (hz1 : Code z1 d1 s1)
    (heq : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma0 sigma1 z)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c t b nameBound) :
    ∃ sigma, ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) nameBound fixingP sigma ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma sigma0 z0 ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma sigma1 z1 := by
  obtain ⟨nu,hnu,hfixed,he0,he1⟩ := ForcingSupportDescent.support_descent hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1
    hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hn0.1.1 hn1.1.1 hn0.2 hn1.2
    hd hRestr0 hRestr1 hz hz0 hz1 heq
  have hApI : ForcingPowerName.Subset Ap I := by
    intro j hj
    obtain ⟨i,_,hij⟩ := (hRangeP j).mp hj
    exact hp.1.2 i j hij
  obtain ⟨name,hn,hnEq⟩ := ForcingLocalNormalize.normalize_at_values hM env rho G F mul hw hMu hm hpres
    hG hFilter hc ht hLabels hBound hApI hFixP hnu hfixed
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have htW := (hpres.2.2.2.2.2 t).mpr (Or.inl ht)
  have hTop (q : M.Carrier .set) (_hq : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6))) :
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env q t :=
    (orderFormula_semantics env (rho 0) mul q t).mpr (Or.inl ht)
  have finish (p tau : M.Carrier .set)
      (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
      (hb : ForcingPowerName.Subset tau nameBound)
      (he : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) nu tau p) :
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) name tau p := by
    have hsub := ForcingLabelBound.normalized_subset hM (orderFormula (rho 0) mul)
      (ForcingPairUnion.domain rho G F) env hLabels hBound hb htW hTop (p := p)
    have hNuSub := (ForcingPowerName.subset_congr hM hpre he
      (ForcingAtomicBasic.eq_refl hM hpre labels p hpW)).mpr hsub
    exact ForcingAtomicLaws.eq_trans hM hpre
      (ForcingAtomicBasic.eq_symm hM (hnEq p hpW hNuSub)) he
  exact ⟨name,hn,
    finish z0 sigma0 (code_mem hpres (restricted_condition hM hd hRestr0) hs0 hz0) hn0.1.2 he0,
    finish z1 sigma1 (code_mem hpres (restricted_condition hM hd hRestr1) hs1 hz1) hn1.1.2 he1⟩

/-- A member of the exact ground LocalName carrier, with equality at both
original supporting roots. -/
def result {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul nameBound fixingP sigma0 sigma1 z0 z1 : Fin k) : Formula k :=
  .ex ((ForcingLocalNames.localName (ReplacementPredicates.paramsUp rho) G.castSucc F.castSucc
    nameBound.castSucc fixingP.castSucc (Fin.last k)).conj
    ((ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) (ReplacementPredicates.paramsUp id)
      (rho 6).castSucc (Fin.last k) sigma0.castSucc z0.castSucc).conj
      (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) (ReplacementPredicates.paramsUp id)
        (rho 6).castSucc (Fin.last k) sigma1.castSucc z1.castSucc)))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul nameBound fixingP sigma0 sigma1 z0 z1 : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (result rho G F mul nameBound fixingP sigma0 sigma1 z0 z1) ↔
    ∃ sigma, ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F)
      (env nameBound) (env fixingP) sigma ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma (env sigma0) (env z0) ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma (env sigma1) (env z1) := by
  simp only [result,Formula.Realize,ForcingLocalNames.localName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ReplacementPredicates.paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s0 (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s1 (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection v (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s0 p))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s1 p))
    (.imp (ConstructionDiagramPlacements.rangeIntersection (rho 0) s0 s1 p)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul v s0))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul v s1))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s0 A0))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s1 A1))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A0 fixing0))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A1 fixing1))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap fixingP))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.localName rho G F nameBound fixing0 sigma0))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.localName rho G F nameBound fixing1 sigma1))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ConstructionCohenCompatibility.restricted A0 d d0)
    (.imp (ConstructionCohenCompatibility.restricted A1 d d1)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d v))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 s0))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z1 d1 s1))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) sigma0 sigma1 z))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b nameBound))
    (ProjectSyntax.encode id (result rho G F mul nameBound fixingP sigma0 sigma1 z0 z1))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionDiagramPlacements.rangeIntersection_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.le_semantics (M := M),ConstructionDiagramPlacements.rangeIntersection_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingLocalNames.localName_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ConstructionCohenCompatibility.restricted_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    result_semantics (M := M),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hn0 hn1 hd hRestr0 hRestr1 hz hz0 hz1 heq hc ht hLabels hBound
  exact localName_descent hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hn0 hn1 hd hRestr0 hRestr1 hz hz0 hz1 heq hc ht hLabels hBound

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let zero := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => zero }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 c t b labels nameBound hL hChoice)

end PPAC.Migration.ForcingLocalNameDescent
