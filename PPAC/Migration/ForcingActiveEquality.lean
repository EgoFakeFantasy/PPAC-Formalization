/- Pinned LocalQuotients.permute_le_root:58 and active_equal:67.
Actual consumer: support_descent:173. Arbitrary overlaps and name ranks retained.
Reuse existing compatible placement and independent active-copy equality. -/
import PPAC.Migration.ForcingActiveIndependent

namespace PPAC.Migration.ForcingActiveEquality
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

/-- Pinned LocalQuotients.permute_le_root:58. Reuse the existing diagram
order-equivariance proof and the same fixed-root composition from compatible placement. -/
theorem permute_le_root (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul p s pi sP : M.Carrier .set}
    (hp : Injection D I p) (hs : Injection D I s) (hpi : Permutation I pi)
    (hPerm : CompositionGraph D pi s sP)
    (hsp : ForcingDiagramOrder.Le D mul s p)
    (hFix : ConstructionDiagramPlacements.FixesRange D p pi) :
    ForcingDiagramOrder.Le D mul sP p := by
  have hPiP : CompositionGraph D pi p p := by
    intro x z
    constructor
    · intro hxz
      have hx := ForcingConditionGraphs.function_input hp.1.1 hxz
      exact ⟨hx,z,hxz,hFix z ⟨x,hx,hxz⟩⟩
    · rintro ⟨hx,y,hxy,hyz⟩
      have he := ForcingConditionGraphs.function_unique hpi.1.1 hyz (hFix y ⟨x,hx,hxy⟩)
      exact he.symm ▸ hxy
  exact (ForcingDiagramOrder.le_iff hM hpi hs hp hPerm hPiP).mp hsp

theorem active_equal (hM : FirstOrder.Theory.Models M nativeZF)
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
    (hs0p : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s0 p)
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
  have hdelta := ForcingSupportingRoot.restricted_condition hM hd hRestr
  have hsaRoot := permute_le_root hM hp hs0 ha hsaComp hs0p hfa
  have hsbRoot := permute_le_root hM hp hs0 hb hsbComp hs0p hfb
  apply ForcingAtomicBasic.eq_of_dense hM hpre hr
  intro q hq hqr
  have hqra := ForcingProductPoset.withtop_trans hm
    ((orderFormula_semantics env (rho 0) mul q r).mp hqr) hra
  have hqrb := ForcingProductPoset.withtop_trans hm
    ((orderFormula_semantics env (rho 0) mul q r).mp hqr) hrb
  obtain ⟨c,t,hc,ht,hqCode⟩ := ForcingActiveIndependent.below_code hpres hq hza hqra
  have hqa := (code_le hqCode hza).mp hqra
  have hqb := (code_le hqCode hzb).mp hqrb
  have htRoot := ForcingDiagramPoset.le_trans hm hqa.2 hsaRoot
  obtain ⟨Ap,hAp,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hp hD
  obtain ⟨cRoot,hcRoot,hcRestr,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hc Ap
  obtain ⟨deltaRoot,_,hdeltaRestr,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hdelta Ap
  have hRoot : ConstructionCohenCompatibility.Compatible cRoot deltaRoot := by
    apply ConstructionCohenCompatibility.compatible_of_entries hpres.1 hpres.2.1 hcRoot
    intro i j b b' heC heD
    have hec := (ConstructionCohenCompatibility.restricted_entry hcRestr).mp heC |>.1
    obtain ⟨hed,hi⟩ := (ConstructionCohenCompatibility.restricted_entry hdeltaRestr).mp heD
    have hmoved := (ConstructionDescentPlacement.actual_moved_condition hda).2
    have heda := (hmoved i j b').mpr ⟨i,hfa i ((hAp i).mp hi),hed⟩
    obtain ⟨a0,ha0,hca0⟩ := hec
    obtain ⟨a1,ha1,eda⟩ := heda
    have e01 := KuratowskiZF.code_unique hM ha1 ha0
    have eca : PureKuratowski.PairMember M a1 b' c := by
      obtain ⟨z,hz,hzd⟩ := eda
      exact ⟨z,hz,hqa.1 z hzd⟩
    exact hc.2.1 a0 b b' hca0 (e01 ▸ eca)
  obtain ⟨gamma,out,hgamma,hfgamma,sg,dg,a,s,cQ,cG,hsg,hsgComp,hInterTG,hdg,haC,hs,
      hOut,hCQ,hCG,hOutQ,hOutG⟩ :=
    ConstructionCompatiblePlacement.compatible_placement hM hChoice hw hMu hI hD hMergers hRow hm
      ⟨hpres.1,hpres.2.1,hp,ht,hs0,htRoot,hs0p,hc,hdelta,Ap,cRoot,deltaRoot,hAp,hcRestr,hdeltaRestr,hRoot⟩
  have hsgRoot := permute_le_root hM hp hs0 hgamma hsgComp hs0p hfgamma
  have hInterAG : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) sa sg p := by
    intro j
    constructor
    · rintro ⟨hjA,hjG⟩
      exact (hInterTG j).mp ⟨ConstructionDescentPlacement.range_antitone hqa.2 hjA,hjG⟩
    · intro hj
      exact ⟨ConstructionDescentPlacement.range_antitone hsaRoot hj,
        ConstructionDescentPlacement.range_antitone hsgRoot hj⟩
  have hInterBG : ConstructionDiagramPlacements.RangeIntersection (env (rho 0)) sb sg p := by
    intro j
    constructor
    · rintro ⟨hjB,hjG⟩
      exact (hInterTG j).mp ⟨ConstructionDescentPlacement.range_antitone hqb.2 hjB,hjG⟩
    · intro hj
      exact ⟨ConstructionDescentPlacement.range_antitone hsbRoot hj,
        ConstructionDescentPlacement.range_antitone hsgRoot hj⟩
  obtain ⟨actG,hActG⟩ := ForcingProductFamily.exists_action hM hpres hgamma
  have hAG := (mapRel_action (fun i => env (rho i)) gamma actG).mpr hActG
  obtain ⟨xG,hxG⟩ := ForcingNameConjugacy.exists_action hM
    (ForcingProductFamily.action_permutation hActG).1 sigma0
  obtain ⟨zG,hzG⟩ := exists_code hM dg sg
  obtain ⟨zT,hzT⟩ := exists_code hM a s
  have hzTW := code_mem hpres haC hs hzT
  have hTQ := ForcingActiveIndependent.lift_le hM hzT hqCode hOut hCQ hOutQ
  have hTG := ForcingActiveIndependent.lift_le hM hzT hzG hOut hCG hOutG
  have hTA := ForcingProductPoset.withtop_trans hm hTQ hqra
  have hTB := ForcingProductPoset.withtop_trans hm hTQ hqrb
  have hAGeq := ForcingActiveIndependent.active_equal_independent hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1
    hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hd hdRange hz heq
    ha hgamma hfa hfgamma hsa hsg hsaComp hsgComp hInterAG hRestr hda hdg
    hza hzG hzTW hTA hTG hActA hAG hx hxG
  have hBGeq := ForcingActiveIndependent.active_equal_independent hM hChoice env rho G F mul
    hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1
    hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hd hdRange hz heq
    hb hgamma hfb hfgamma hsb hsg hsbComp hsgComp hInterBG hRestr hdb hdg
    hzb hzG hzTW hTB hTG hActB hAG hy hxG
  exact ⟨zT,hzTW,(orderFormula_semantics env (rho 0) mul zT q).mpr hTQ,
    ForcingAtomicLaws.eq_trans hM hpre hAGeq (ForcingAtomicBasic.eq_symm hM hBGeq)⟩
/-- Source :67 as a sentence over the same actual construction in internal L.
Range, restriction and moved-coordinate premises specify source operations;
arbitrary overlaps are handled by constructing a third independent copy. -/
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
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s0 p))
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
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1 hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hd hdRange hz heq ha hb hfa hfb hsa hsb hsaComp hsbComp hs0p hRestr hda hdb hza hzb hr hra hrb hActA hActB hx hy
  exact active_equal hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hp hs0 hs1 hv hInter hv0 hv1 hRange0 hRange1 hFix0 hFix1 hn0 hn1 hsup0 hsup1 hd hdRange hz heq ha hb hfa hfb hsa hsb hsaComp hsbComp hs0p hRestr hda hdb hza hzb hr hra hrb hActA hActB hx hy

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

end PPAC.Migration.ForcingActiveEquality
