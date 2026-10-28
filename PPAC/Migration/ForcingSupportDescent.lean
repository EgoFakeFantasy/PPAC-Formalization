/- Pinned LocalQuotients.support_descent:132-202.
Construct the actual root-subgroup orbit mixture and prove both restricted
equalities for arbitrary-rank HS names. No supplied orbit family, coherence,
mixed-name witness, or extra Cohen compatibility hypothesis. -/
import PPAC.Migration.ForcingSupportOrbit

namespace PPAC.Migration.ForcingSupportDescent
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

theorem support_descent (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v
      A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 : M.Carrier .set}
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
    (hHS0 : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) sigma0)
    (hHS1 : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) sigma1)
    (hsup0 : Supported (fun i => env (rho i)) fixing0 sigma0)
    (hsup1 : Supported (fun i => env (rho i)) fixing1 sigma1)
    (hd : ForcingCohenConditions.Condition (env (rho 2)) w d)
    (hRestr0 : Restricted A0 d d0) (hRestr1 : Restricted A1 d d1)
    (hz : Code z d v) (hz0 : Code z0 d0 s0) (hz1 : Code z1 d1 s1)
    (heq : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma0 sigma1 z) :
    ∃ sigma, ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) sigma ∧
      Supported (fun i => env (rho i)) fixingP sigma ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma sigma0 z0 ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma sigma1 z1 := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hn0 := ForcingHS.isName hHS0
  have hn1 := ForcingHS.isName hHS1
  have hd0 := restricted_condition hM hd hRestr0
  have hz0W := code_mem hpres hd0 hs0 hz0
  have hzW := code_mem hpres hd hv hz
  obtain ⟨Av,hAv,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hv hD
  obtain ⟨fixingV,hFixV⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Av
  have hA0V : (Project.FirstOrderSemantics.reduct M).MemberSubset A0 Av :=
    fun i hi => (hAv i).mpr (ConstructionDescentPlacement.range_antitone hv0 ((hRange0 i).mp hi))
  have hA1V : (Project.FirstOrderSemantics.reduct M).MemberSubset A1 Av :=
    fun i hi => (hAv i).mpr (ConstructionDescentPlacement.range_antitone hv1 ((hRange1 i).mp hi))
  have hsupV0 := ForcingSupportedNames.supported_mono hFix0 hFixV hA0V hsup0
  have hsupV1 := ForcingSupportedNames.supported_mono hFix1 hFixV hA1V hsup1
  have hsupV : ∀ j : Fin 2, Supported (fun i => env (rho i)) fixingV (args2 sigma0 sigma1 j) := by
    intro j
    exact Fin.cases hsupV0 (fun j => Fin.cases hsupV1 (fun j => Fin.elim0 j) j) j
  obtain ⟨dv,hdv,hRestrV,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd Av
  obtain ⟨zv,hzv⟩ := exists_code hM dv v
  have heqV : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma0 sigma1 zv :=
    ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm
      hpres hG hFilter hv hv (ForcingDiagramPoset.le_refl hm hv) hd hAv hFixV hRestrV hz hzv
      (.equal (0 : Fin 2) 1) (args2 sigma0 sigma1) hsupV heq
  have hdRange : ConstructionDescentPlacement.WithinRange (env (rho 0)) v dv :=
    fun i j b he => (hAv i).mp ((ConstructionCohenCompatibility.restricted_entry hRestrV).mp he).2
  have hRestrDv0 : Restricted A0 dv d0 := by
    intro c
    constructor
    · intro hc
      obtain ⟨hcd,i,hl,hi⟩ := (hRestr0 c).mp hc
      exact ⟨(hRestrV c).mpr ⟨hcd,i,hl,hA0V i hi⟩,i,hl,hi⟩
    · rintro ⟨hcv,i,hl,hi⟩
      exact (hRestr0 c).mpr ⟨((hRestrV c).mp hcv).1,i,hl,hi⟩
  obtain ⟨Ap',hAp',hAp'I,hAp'Small⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hp hD
  have eAp := ForcingCohenOrderAction.image_unique hM hAp' hRangeP
  have hApI : (Project.FirstOrderSemantics.reduct M).MemberSubset Ap I := eAp ▸ hAp'I
  have hApSmall : Small Ap mu := eAp ▸ hAp'Small
  have hSubgroup := ForcingConjugationGraph.fixing_subgroup hM hG hFixP hApI
  have hMemFilter : (Project.FirstOrderSemantics.reduct M).mem fixingP (env F) :=
    (hFilter fixingP).mpr ⟨hSubgroup,Ap,fixingP,hApI,hApSmall,hFixP,fun _ h => h⟩
  obtain ⟨f,a,hf,ha⟩ := ForcingSupportOrbit.exists_families hM (fun i => env (rho i)) hpres hG hSubgroup.1 hz0W
    (sigma := sigma0)
  have hFamily := ForcingSupportOrbit.family_HS hM (fun i => env (rho i)) hpres hG hNormal hSubgroup.1 hHS0 hf
  have hPermutes := ForcingSupportOrbit.permutes hM (fun i => env (rho i)) hpres hG hSubgroup hz0W hf ha
  have hCoherent : ForcingMixLaws.Coherent (orderFormula (rho 0) mul) env (env (rho 6)) fixingP f a := by
    intro i j si sj t u r hi hj hfi hfj hai haj hr hrt hru
    have hiPerm := (hG i).mp (hSubgroup.1 i hi)
    have hjPerm := (hG j).mp (hSubgroup.1 j hj)
    obtain ⟨_,Ai,hAi,hsi⟩ := (hf i si).mp hfi
    obtain ⟨_,Aj,hAj,hsj⟩ := (hf j sj).mp hfj
    obtain ⟨_,Bi,hBi,hzi⟩ := (ha i t).mp hai
    obtain ⟨_,Bj,hBj,hzj⟩ := (ha j u).mp haj
    have ei := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp hBi) ((mapRel_action _ _ _).mp hAi)
    have ej := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp hBj) ((mapRel_action _ _ _).mp hAj)
    subst Bi
    subst Bj
    obtain ⟨di,spi,hspi,hdi,hspci,hti⟩ :=
      ForcingSupportOrbit.moved_coordinates hM (fun q => env (rho q)) hpres hiPerm hAi hd0 hs0 hz0 hzi
    obtain ⟨dj,spj,hspj,hdj,hspcj,htj⟩ :=
      ForcingSupportOrbit.moved_coordinates hM (fun q => env (rho q)) hpres hjPerm hAj hd0 hs0 hz0 hzj
    have hfiRoot : ConstructionDiagramPlacements.FixesRange (env (rho 0)) p i :=
      fun q hq => ((hFixP i).mp hi).2 q ((hRangeP q).mpr hq)
    have hfjRoot : ConstructionDiagramPlacements.FixesRange (env (rho 0)) p j :=
      fun q hq => ((hFixP j).mp hj).2 q ((hRangeP q).mpr hq)
    exact ForcingActiveEquality.active_equal hM hChoice env rho G F mul
      hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1
      hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hdv hdRange hzv heqV
      hiPerm hjPerm hfiRoot hfjRoot hspi hspj hspci hspcj hs0p hRestrDv0 hdi hdj hti htj
      hr ((orderFormula_semantics env (rho 0) mul r t).mp hrt)
      ((orderFormula_semantics env (rho 0) mul r u).mp hru) hAi hAj hsi hsj
  obtain ⟨sigma,hMix⟩ := ForcingMixName.exists_mix hM (orderFormula (rho 0) mul) env (env (rho 6)) fixingP f a
  obtain ⟨hHS,hFixed⟩ := ForcingEquivariantMix.fixed_and_HS hM env rho mul hpres hG hNormal
    hSubgroup hMemFilter hFamily hPermutes hMix
  obtain ⟨identity,hId,hIdF,hIdA⟩ :=
    ForcingSupportOrbit.identity_members hM (fun i => env (rho i)) hpres hG hSubgroup hn0 hz0W hf ha
  have he0 := ForcingMixLaws.eq_at hM hpre (ForcingSupportOrbit.activations ha) hMix hCoherent hId hIdF hIdA
  have heOrig0 := ForcingAtomicBasic.eq_mono hM hpre hzW
    ((orderFormula_semantics env (rho 0) mul z z0).mpr
      ((code_le hz hz0).mpr ⟨fun c hc => ((hRestr0 c).mp hc).1,hv0⟩)) he0
  have heOrig1 := ForcingAtomicLaws.eq_trans hM hpre heOrig0 heq
  have hAp1 : (Project.FirstOrderSemantics.reduct M).MemberSubset Ap A1 :=
    fun i hi => (hRange1 i).mpr (ConstructionDescentPlacement.range_antitone hs1p ((hRangeP i).mp hi))
  have hSupSigma1 : Supported (fun i => env (rho i)) fixing1 sigma :=
    ForcingSupportedNames.supported_mono hFixP hFix1 hAp1 hFixed
  have hsupFinal : ∀ j : Fin 2, Supported (fun i => env (rho i)) fixing1 (args2 sigma sigma1 j) := by
    intro j
    exact Fin.cases hSupSigma1 (fun j => Fin.cases hsup1 (fun j => Fin.elim0 j) j) j
  have he1 : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma sigma1 z1 :=
    ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm
      hpres hG hFilter hs1 hv hv1 hd hRange1 hFix1 hRestr1 hz hz1
      (.equal (0 : Fin 2) 1) (args2 sigma sigma1) hsupFinal heOrig1
  exact ⟨sigma,hHS,hFixed,he0,he1⟩

/-- Original support-descent conclusion: one HS root-supported name, with both
equalities at the original Cohen restrictions. -/
def result {k : Nat} (rho : Fin 7 → Fin k) (G F mul fixingP sigma0 sigma1 z0 z1 : Fin k) : Formula k :=
  .ex ((ForcingHS.hs actionFormula (ReplacementPredicates.paramsUp rho) G.castSucc (rho 6).castSucc
    F.castSucc (Fin.last k)).conj
    ((ForcingEquivariantMix.fixedAll (ReplacementPredicates.paramsUp rho) fixingP.castSucc (Fin.last k)).conj
      ((ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) (ReplacementPredicates.paramsUp id)
        (rho 6).castSucc (Fin.last k) sigma0.castSucc z0.castSucc).conj
        (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) (ReplacementPredicates.paramsUp id)
          (rho 6).castSucc (Fin.last k) sigma1.castSucc z1.castSucc))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul fixingP sigma0 sigma1 z0 z1 : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (result rho G F mul fixingP sigma0 sigma1 z0 z1) ↔
    ∃ sigma, ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) sigma ∧
      Supported (fun i => env (rho i)) (env fixingP) sigma ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma (env sigma0) (env z0) ∧
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma (env sigma1) (env z1) := by
  simp only [result,Formula.Realize,ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    ReplacementPredicates.paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 : Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F sigma0))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F sigma1))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing0 sigma0))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing1 sigma1))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ConstructionCohenCompatibility.restricted A0 d d0)
    (.imp (ConstructionCohenCompatibility.restricted A1 d d1)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d v))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 s0))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z1 d1 s1))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) sigma0 sigma1 z))
    (ProjectSyntax.encode id (result rho G F mul fixingP sigma0 sigma1 z0 z1))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionDiagramPlacements.rangeIntersection_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1)]
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
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ConstructionCohenCompatibility.restricted_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    result_semantics (M := M),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hHS0 hHS1 hsup0 hsup1 hd hRestr0 hRestr1 hz hz0 hz1 heq
  exact support_descent hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hs0p hs1p hInter hv0 hv1 hRange0 hRange1 hRangeP hFix0 hFix1 hFixP hHS0 hHS1 hsup0 hsup1 hd hRestr0 hRestr1 hz hz0 hz1 heq

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v A0 A1 Ap fixing0 fixing1 fixingP d d0 d1 z z0 z1 sigma0 sigma1 hL hChoice)

end PPAC.Migration.ForcingSupportDescent
