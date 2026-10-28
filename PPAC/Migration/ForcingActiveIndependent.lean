/- Pinned LocalQuotients.active_equal_independent:18.
Actual consumer: LocalQuotients.active_equal:111/114, then support_descent.
Reuse the constructed three-copy placement and literal supported-name equality.
All names have arbitrary rank; dense witnesses are constructed, not assumed. -/
import PPAC.Migration.ForcingSupportingRoot
import PPAC.Migration.ForcingAtomicLaws

namespace PPAC.Migration.ForcingActiveIndependent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (Injection Small)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingStabilizer (Action)
open ForcingCohenConditions (Condition)
open ForcingSupportingRoot (Code code_mem exists_code code_le moved_code)
open ConstructionDescentPlacement (ActualMoved WithinRange)
open ConstructionCohenCompatibility (Restricted)
open ForcingSupportedNames (Supported Range)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- A condition below an actual pair is itself an actual pair, including in
nonstandard models. This only unpacks the existing WithTop carrier/order. -/
theorem below_code {D I K B w C S X Y P W mul q z d s : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hz : Code z d s) (hle : ForcingWithTopAction.Le D mul q z) :
    ∃ c t, Condition S w c ∧ Injection D I t ∧ Code q c t := by
  obtain ⟨cz,hcz,hzs⟩ := hz
  rcases hle with he | ⟨cq,cz',hqs,hzs',_⟩
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hzs he)
  have hcq := ForcingProductPoset.coe_mem hp.2.2.2.2.2 hq hqs
  obtain ⟨c,hc,t,ht,hct⟩ := (hp.2.2.2.2.1 cq).mp hcq
  exact ⟨c,t,(hp.2.2.1 c).mp hc,(hp.2.2.2.1 t).mp ht,cq,hct,hqs⟩

/-- Lift an existing Product lower bound through the existing singleton code. -/
theorem lift_le (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul q t c c' d s a r : M.Carrier .set}
    (hq : Code q d s) (ht : Code t a r)
    (hc : PureKuratowski.Code M c d s) (hc' : PureKuratowski.Code M c' a r)
    (hle : ForcingProductAction.Le D mul c c') : ForcingWithTopAction.Le D mul q t := by
  obtain ⟨b,hb,hqb⟩ := hq
  obtain ⟨b',hb',htb⟩ := ht
  have e := KuratowskiZF.code_unique hM hb hc
  have e' := KuratowskiZF.code_unique hM hb' hc'
  exact Or.inr ⟨b,b',hqb,htb,e.symm ▸ e'.symm ▸ hle⟩

/-- Equality specialization of the already proved actual Product symmetry. -/
theorem eq_symmetry (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a p q x y x' y' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F)) (hpi : Permutation I pi)
    (hA : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hx : Action (env (rho 6)) a x x') (hy : Action (env (rho 6)) a y y')
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hpq : PureKuratowski.PairMember M p q a) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x y p ↔
      Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x' y' q := by
  have hv : ∀ j : Fin 2, Action (env (rho 6)) a
      (Source.SetLanguage.args2 x y j) (Source.SetLanguage.args2 x' y' j) := by
    intro j
    refine Fin.cases hx (fun j => ?_) j
    exact Fin.cases hy (fun j => Fin.elim0 j) j
  exact ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi hA
    (.equal (0 : Fin 2) 1) (Source.SetLanguage.args2 x y) (Source.SetLanguage.args2 x' y') hv hpW hpq

theorem active_equal_independent (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s0 s1 v alpha beta sa sb
      d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y : M.Carrier .set}
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
    (hInter : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) s0 s1 p)
    (hv0 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s0)
    (hv1 : ForcingDiagramOrder.Le (env (rho 0)) (env mul) v s1)
    (hRange0 : Range (env (rho 0)) s0 A0) (hRange1 : Range (env (rho 0)) s1 A1)
    (hFix0 : ForcingLabelPermutations.Fixing (env G) A0 fixing0)
    (hFix1 : ForcingLabelPermutations.Fixing (env G) A1 fixing1)
    (hn0 : ForcingNames.IsName (env (rho 6)) sigma0) (hn1 : ForcingNames.IsName (env (rho 6)) sigma1)
    (hsup0 : Supported (fun i => env (rho i)) fixing0 sigma0)
    (hsup1 : Supported (fun i => env (rho i)) fixing1 sigma1)
    (hd : Condition (env (rho 2)) w d) (hdRange : WithinRange (env (rho 0)) v d)
    (hz : Code z d v)
    (heq : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) sigma0 sigma1 z)
    (ha : Permutation I alpha) (hb : Permutation I beta)
    (hfa : ConstructionDiagramPlacements.FixesRange (env (rho 0)) p alpha)
    (hfb : ConstructionDiagramPlacements.FixesRange (env (rho 0)) p beta)
    (hsa : Injection (env (rho 0)) I sa) (hsb : Injection (env (rho 0)) I sb)
    (hsaComp : CompositionGraph (env (rho 0)) alpha s0 sa)
    (hsbComp : CompositionGraph (env (rho 0)) beta s0 sb)
    (hInd : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) sa sb p)
    (hRestr : Restricted A0 d delta)
    (hda : ActualMoved (env (rho 1)) (env (rho 2)) w alpha delta da)
    (hdb : ActualMoved (env (rho 1)) (env (rho 2)) w beta delta db)
    (hza : Code za da sa) (hzb : Code zb db sb)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)))
    (hra : ForcingWithTopAction.Le (env (rho 0)) (env mul) r za)
    (hrb : ForcingWithTopAction.Le (env (rho 0)) (env mul) r zb)
    (hActA : MapRel actionFormula (fun i => env (rho i)) alpha actA)
    (hActB : MapRel actionFormula (fun i => env (rho i)) beta actB)
    (hx : Action (env (rho 6)) actA sigma0 x) (hy : Action (env (rho 6)) actB sigma0 y) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x y r := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hdelta := ForcingSupportingRoot.restricted_condition hM hd hRestr
  apply ForcingAtomicBasic.eq_of_dense hM hpre hr
  intro q hq hqr
  have hqra := ForcingProductPoset.withtop_trans hm
    ((orderFormula_semantics env (rho 0) mul q r).mp hqr) hra
  have hqrb := ForcingProductPoset.withtop_trans hm
    ((orderFormula_semantics env (rho 0) mul q r).mp hqr) hrb
  obtain ⟨c,t,hc,ht,hqCode⟩ := below_code hpres hq hza hqra
  have hqa := (code_le hqCode hza).mp hqra
  have hqb := (code_le hqCode hzb).mp hqrb
  obtain ⟨pi,psi,out,hpi,hpsi,hPi0,hPsi0,shared,vP,vR,dP,dR,a,s,cT,pP,pR,
      hshared,hPi1,hPsi1,hvP,hPiV,hvR,hPsiV,hdP,hdR,haC,hs,outCode,cTCode,pPCode,pRCode,
      hOutQ,hOutP,hOutR⟩ :=
    ConstructionDescentPlacement.descent_comparison_placement hM hChoice hw hMu hI hD hMergers hRow hm
      ⟨hpres.1,hpres.2.1,hp,hs0,hs1,hv,hsa,hsb,ht,hInter,hv0,hv1,ha,hb,hfa,hfb,hsaComp,
       hsbComp,hInd,hd,hc,hdRange,hqa.2,hqb.2,A0,delta,da,db,hRange0,hdelta,hRestr,hda,hdb,hqa.1,hqb.1⟩
  obtain ⟨actP,hActP⟩ := ForcingProductFamily.exists_action hM hpres hpi
  obtain ⟨actR,hActR⟩ := ForcingProductFamily.exists_action hM hpres hpsi
  have hAP := (mapRel_action (fun i => env (rho i)) pi actP).mpr hActP
  have hAR := (mapRel_action (fun i => env (rho i)) psi actR).mpr hActR
  obtain ⟨xP,hxP⟩ := ForcingNameConjugacy.exists_action hM
    (ForcingProductFamily.action_permutation hActP).1 sigma0
  obtain ⟨yP,hyP⟩ := ForcingNameConjugacy.exists_action hM
    (ForcingProductFamily.action_permutation hActP).1 sigma1
  obtain ⟨xR,hxR⟩ := ForcingNameConjugacy.exists_action hM
    (ForcingProductFamily.action_permutation hActR).1 sigma0
  obtain ⟨yR,hyR⟩ := ForcingNameConjugacy.exists_action hM
    (ForcingProductFamily.action_permutation hActR).1 sigma1
  have ex : xP = x := ForcingSupportedNames.name_eq_of_same_diagram hM (fun i => env (rho i))
    hpres hG hFix0 hs0 hRange0 hn0 hsup0 hpi ha hPi0 hsaComp hAP hActA hxP hx
  have ey : xR = y := ForcingSupportedNames.name_eq_of_same_diagram hM (fun i => env (rho i))
    hpres hG hFix0 hs0 hRange0 hn0 hsup0 hpsi hb hPsi0 hsbComp hAR hActB hxR hy
  have es : yP = yR := ForcingSupportedNames.name_eq_of_same_diagram hM (fun i => env (rho i))
    hpres hG hFix1 hs1 hRange1 hn1 hsup1 hpi hpsi hPi1 hPsi1 hAP hAR hyP hyR
  obtain ⟨zP,hzP⟩ := exists_code hM dP vP
  obtain ⟨zR,hzR⟩ := exists_code hM dR vR
  have heP := (eq_symmetry hM env rho G F mul hpres hG hNormal hpi hAP hxP hyP
    (code_mem hpres hd hv hz) (moved_code hM hpres hActP hd hv hvP hdP hPiV hz hzP)).mp heq
  have heR := (eq_symmetry hM env rho G F mul hpres hG hNormal hpsi hAR hxR hyR
    (code_mem hpres hd hv hz) (moved_code hM hpres hActR hd hv hvR hdR hPsiV hz hzR)).mp heq
  obtain ⟨zT,hzT⟩ := exists_code hM a s
  have hzTW := code_mem hpres haC hs hzT
  have hTQ := lift_le hM hzT hqCode outCode cTCode hOutQ
  have hTP := (orderFormula_semantics env (rho 0) mul zT zP).mpr
    (lift_le hM hzT hzP outCode pPCode hOutP)
  have hTR := (orderFormula_semantics env (rho 0) mul zT zR).mpr
    (lift_le hM hzT hzR outCode pRCode hOutR)
  rw [ex,es] at heP
  rw [ey] at heR
  exact ⟨zT,hzTW,(orderFormula_semantics env (rho 0) mul zT q).mpr hTQ,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hzTW hTP heP)
      (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hzTW hTR heR))⟩

/-- Source :18 as a sentence over the same actual construction in internal L.
Range, restriction and moved-coordinate premises specify source operations;
the independent comparison and every dense witness are proved above. -/
def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y : Fin k) : Project.Sentence where
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
    (.imp (ConstructionDiagramPlacements.rangeIntersection (rho 0) s0 s1 p)
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul v s0))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul v s1))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s0 A0))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s1 A1))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A0 fixing0))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A1 fixing1))
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) sigma0))
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) sigma1))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing0 sigma0))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing1 sigma1))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ConstructionDescentPlacement.withinRange (rho 0) v d)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d v))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) sigma0 sigma1 z))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I alpha))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I beta))
    (.imp (ConstructionDiagramPlacements.fixesRange (rho 0) p alpha)
    (.imp (ConstructionDiagramPlacements.fixesRange (rho 0) p beta)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection sa (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection sb (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) alpha s0 sa))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) beta s0 sb))
    (.imp (ConstructionDiagramPlacements.rangeIntersection (rho 0) sa sb p)
    (.imp (ConstructionCohenCompatibility.restricted A0 d delta)
    (.imp (ConstructionDescentPlacement.actualMoved (rho 1) (rho 2) w alpha delta da)
    (.imp (ConstructionDescentPlacement.actualMoved (rho 1) (rho 2) w beta delta db)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code za da sa))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code zb db sb))
    (.imp (ProjectSyntax.encode id (Formula.mem r (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingWithTopAction.le (rho 0) mul r za))
    (.imp (ProjectSyntax.encode id (ForcingWithTopAction.le (rho 0) mul r zb))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel actionFormula rho alpha actA))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel actionFormula rho beta actB))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) actA sigma0 x))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) actB sigma0 y))
    (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) x y r))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionDiagramPlacements.rangeIntersection_freeClosed,
      ConstructionDiagramPlacements.fixesRange_freeClosed,ConstructionDescentPlacement.withinRange_freeClosed,
      ConstructionDescentPlacement.actualMoved_freeClosed,ConstructionCohenCompatibility.restricted_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y)]
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
    ConstructionDiagramPlacements.rangeIntersection_semantics hM,
    ForcingDiagramOrder.le_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingNames.isName_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ConstructionDescentPlacement.withinRange_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),
    ConstructionDiagramPlacements.fixesRange_semantics hM,
    ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ConstructionCohenCompatibility.restricted_semantics hM,ConstructionDescentPlacement.actualMoved_semantics hM,
    Formula.Realize,ForcingWithTopAction.le_semantics (M := M),
    ForcingMapConditions.rel_semantics (M := M),ForcingStabilizer.action_semantics (M := M),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1 hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hd hdRange hz heq ha hb hfa hfb hsa hsb hsaComp hsbComp hInd hRestr hda hdb hza hzb hr hra hrb hActA hActB hx hy
  exact active_equal_independent hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1 hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hd hdRange hz heq ha hb hfa hfb hsa hsb hsaComp hsbComp hInd hRestr hda hdb hza hzb hr hra hrb hActA hActB hx hy

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s0 s1 v alpha beta sa sb d A0 A1 fixing0 fixing1 delta da db za zb z r sigma0 sigma1 actA actB x y hL hChoice)

end PPAC.Migration.ForcingActiveIndependent
