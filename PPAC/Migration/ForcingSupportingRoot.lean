/- Pinned ChoiceFailure.forces_at_supporting_root:279 and forces_iff_restrict:305.
Consumers: LocalQuotients.support_descent, AvailableRecords and OrdinalCodes.
Reuse actual compatible placement, Product formula symmetry, and regular forcing.
No assumed dense set, common lower bound, or action-invariance conclusion. -/
import PPAC.Migration.ConstructionCompatiblePlacement
import PPAC.Migration.ForcingSupportedNames
import PPAC.Migration.ForcingSeparation

namespace PPAC.Migration.ForcingSupportingRoot
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (Injection Small)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingCohenConditions (Condition)
open ForcingWithTopCarrier (Single)
open ConstructionCohenCompatibility (Restricted)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source coercion of the actual Cohen/diagram pair into WithTop. -/
def Code (z d s : M.Carrier .set) : Prop :=
  ∃ c, PureKuratowski.Code M c d s ∧ Single z c

theorem code_mem {D I K B w C S X Y P W z d s : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W) (hd : Condition S w d)
    (hs : Injection D I s) (hz : Code z d s) :
    (Project.FirstOrderSemantics.reduct M).mem z W := by
  obtain ⟨c,hc,hz⟩ := hz
  exact (hp.2.2.2.2.2 z).mpr (Or.inr ⟨c,
    (hp.2.2.2.2.1 c).mpr ⟨d,(hp.2.2.1 d).mpr hd,s,(hp.2.2.2.1 s).mpr hs,hc⟩,hz⟩)

theorem exists_code (hM : FirstOrder.Theory.Models M nativeZF) (d s : M.Carrier .set) :
    ∃ z, Code (M := M) z d s := by
  obtain ⟨c,hc⟩ := KuratowskiZF.exists_code hM d s
  obtain ⟨z,hz⟩ := ForcingWithTopCarrier.exists_single hM c
  exact ⟨z,c,hc,hz⟩

theorem code_le {D mul z t d s a r : M.Carrier .set} (hz : Code z d s) (ht : Code t a r) :
    ForcingWithTopAction.Le D mul z t ↔
      (Project.FirstOrderSemantics.reduct M).MemberSubset a d ∧ ForcingDiagramOrder.Le D mul s r := by
  obtain ⟨c,hc,hz⟩ := hz
  obtain ⟨c',hc',ht⟩ := ht
  rw [ForcingWithTopAction.le_coe hz ht]
  constructor
  · rintro ⟨d',s',a',r',hds,har,had,hsr⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hds hc
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective har hc'
    exact ⟨had,hsr⟩
  · rintro ⟨had,hsr⟩
    exact ⟨d,s,a,r,hc,hc',had,hsr⟩

theorem restricted_condition (hM : FirstOrder.Theory.Models M nativeZF)
    {S w A d r : M.Carrier .set} (hd : Condition S w d) (hr : Restricted A d r) :
    Condition S w r := by
  have hsub : (Project.FirstOrderSemantics.reduct M).MemberSubset r d := fun z hz => ((hr z).mp hz).1
  refine ⟨fun z hz => hd.1 z (hsub z hz),?_,ForcingSupportSize.small_subset hM hsub hd.2.2⟩
  intro x y z hxy hxz
  exact hd.2.1 x y z (by obtain ⟨t,ht,hm⟩ := hxy; exact ⟨t,ht,hsub t hm⟩)
    (by obtain ⟨t,ht,hm⟩ := hxz; exact ⟨t,ht,hsub t hm⟩)

/-- Identify the supplied exact moved coordinates with the existing actual action. -/
theorem moved_code (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W pi A d s d' s' z z' : M.Carrier .set}
    (hp : Presentation D I K B w C S X Y P W)
    (hA : ForcingProductFamily.Action D C S X Y P W pi A)
    (hd : Condition S w d) (hs : Injection D I s) (hs' : Injection D I s')
    (hMoved : ConstructionDescentPlacement.ActualMoved C S w pi d d')
    (hPerm : ForcingConditionGraphs.CompositionGraph D pi s s')
    (hz : Code z d s) (hz' : Code z' d' s') : PureKuratowski.PairMember M z z' A := by
  obtain ⟨f,g,ac,ad,r,hf,hfg,hg,hgg,_,hacg,_,hadg,_,hrg,_,hag⟩ := hA
  obtain ⟨f',g',hf',hfg',hg',hgg',hd',hImage,_⟩ := hMoved
  have ef : f = f' := ForcingConjugationGraph.endomap_ext hM hf.1 hf'.1
    (fun x y => (hfg x y).trans (hfg' x y).symm)
  subst f'
  have eg : g = g' := ForcingConjugationGraph.endomap_ext hM hg.1 hg'.1
    (fun x y => (hgg x y).trans (hgg' x y).symm)
  subst g'
  have hzW := code_mem hp hd hs hz
  obtain ⟨c,hc,hz⟩ := hz
  obtain ⟨c',hc',hz'⟩ := hz'
  have hdX := (hp.2.2.1 d).mpr hd
  have hsY := (hp.2.2.2.1 s).mpr hs
  have hcP := (hp.2.2.2.2.1 c).mpr ⟨d,hdX,s,hsY,hc⟩
  exact (hag z z').mpr ⟨hzW,Or.inr ⟨c,c',hz,hz',(hrg c c').mpr ⟨hcP,
    d,s,d',s',hc,(hacg d d').mpr ⟨hdX,(hp.2.2.1 d').mpr hd',hImage⟩,
    (hadg s s').mpr ⟨hsY,(hp.2.2.2.1 s').mpr hs',hPerm⟩,hc'⟩⟩⟩

theorem forces_at_supporting_root (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s d A fixing dR z zR : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hp : Injection (env (rho 0)) I p) (hs : Injection (env (rho 0)) I s)
    (hsp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s p) (hd : Condition (env (rho 2)) w d)
    (hRange : ForcingStabilizerTransport.Image p (env (rho 0)) A)
    (hFix : ForcingLabelPermutations.Fixing (env G) A fixing) (hR : Restricted A d dR)
    (hz : Code z d s) (hzR : Code zR dR p)
    (phi : Formula n) (v : Fin n → M.Carrier .set)
    (hsup : ∀ j, Supported (fun i => env (rho i)) fixing (v j))
    (hforce : Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v (env (rho 6)) z phi) :
    Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v (env (rho 6)) zR phi := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hdR := restricted_condition hM hd hR
  have hzW := code_mem hpres hd hs hz
  have hzRW := code_mem hpres hdR hp hzR
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  apply ForcingFormula.of_dense hM hpre phi v hzRW
  intro q hq hqR
  have hqLe := (orderFormula_semantics env (rho 0) mul q zR).mp hqR
  obtain ⟨cR,hcR,hzRc⟩ := hzR
  rcases hqLe with hEmpty | ⟨cq,cR',hqc,hzRc',hqprod⟩
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hzRc hEmpty)
  have hcReq := ForcingWithTopCarrier.single_injective hzRc' hzRc
  subst cR'
  have hcqP := ForcingProductPoset.coe_mem hpres.2.2.2.2.2 hq hqc
  obtain ⟨dq,hdqX,sq,hsqY,hcq⟩ := (hpres.2.2.2.2.1 cq).mp hcqP
  have hdq := (hpres.2.2.1 dq).mp hdqX
  have hsq := (hpres.2.2.2.1 sq).mp hsqY
  have hqCode : Code q dq sq := ⟨cq,hcq,hqc⟩
  have hqBounds := (code_le hqCode ⟨cR,hcR,hzRc⟩).mp (Or.inr ⟨cq,cR,hqc,hzRc,hqprod⟩)
  obtain ⟨dqR,_,hqRestr,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hdq A
  have hCompat : ConstructionCohenCompatibility.Compatible dqR dR := by
    intro a b c hab hac
    exact hdq.2.1 a b c
      (by obtain ⟨t,ht,hm⟩ := hab; exact ⟨t,ht,((hqRestr t).mp hm).1⟩)
      (by obtain ⟨t,ht,hm⟩ := hac; exact ⟨t,ht,hqBounds.1 t hm⟩)
  obtain ⟨pi,t,hpi,hFixRange,sP,dP,a,r,c0,c1,hsP,hPiS,hInter,hMove,ha,hr,ht,hc0,hc1,ht0,ht1⟩ :=
    ConstructionCompatiblePlacement.compatible_placement hM hChoice hw hMu hI hD hMergers hRow hm
      ⟨hpres.1,hpres.2.1,hp,hsq,hs,hqBounds.2,hsp,hdq,hd,A,dqR,dR,hRange,hqRestr,hR,hCompat⟩
  have hpiFix : (Project.FirstOrderSemantics.reduct M).mem pi fixing :=
    (hFix pi).mpr ⟨(hG pi).mpr hpi,fun x hx => hFixRange x ((hRange x).mp hx)⟩
  obtain ⟨action,hAction⟩ := ForcingProductFamily.exists_action hM hpres hpi
  obtain ⟨zP,hzP⟩ := exists_code hM dP sP
  have hdP := (ConstructionDescentPlacement.actual_moved_condition hMove).1
  have hzPW := code_mem hpres hdP hsP hzP
  have hActionRel := (mapRel_action (fun i => env (rho i)) pi action).mpr hAction
  have hsym := ForcingSeparation.symmetry hM env rho G F mul hpres hG hNormal hpi hActionRel
    phi v v (fun j => hsup j pi hpiFix action hActionRel) hzW
    (moved_code hM hpres hAction hd hs hsP hMove hPiS hz hzP)
  obtain ⟨zT,hzT⟩ := exists_code hM a r
  have hzTW := code_mem hpres ha hr hzT
  have eq0 := KuratowskiZF.code_unique hM hc0 hcq
  have hzTq : ForcingWithTopAction.Le (env (rho 0)) (env mul) zT q := by
    obtain ⟨ct,hct,hzTc⟩ := hzT
    have eqt := KuratowskiZF.code_unique hM hct ht
    exact Or.inr ⟨ct,cq,hzTc,hqc,eqt.symm ▸ eq0 ▸ ht0⟩
  have hzTP : ForcingWithTopAction.Le (env (rho 0)) (env mul) zT zP := by
    obtain ⟨ct,hct,hzTc⟩ := hzT
    obtain ⟨cp,hcp,hzPc⟩ := hzP
    have eqt := KuratowskiZF.code_unique hM hct ht
    have eqp := KuratowskiZF.code_unique hM hc1 hcp
    exact Or.inr ⟨ct,cp,hzTc,hzPc,eqt.symm ▸ eqp ▸ ht1⟩
  exact ⟨zT,hzTW,(orderFormula_semantics env (rho 0) mul zT q).mpr hzTq,
    ForcingFormula.mono hM hpre phi v hzPW hzTW
      ((orderFormula_semantics env (rho 0) mul zT zP).mpr hzTP) (hsym.mp hforce)⟩

/-- Source forces_iff_restrict, also retaining the stronger diagram allowed by :279. -/
theorem forces_iff_restrict (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p s d A fixing dR z zR : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hp : Injection (env (rho 0)) I p) (hs : Injection (env (rho 0)) I s)
    (hsp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s p) (hd : Condition (env (rho 2)) w d)
    (hRange : ForcingStabilizerTransport.Image p (env (rho 0)) A)
    (hFix : ForcingLabelPermutations.Fixing (env G) A fixing) (hR : Restricted A d dR)
    (hz : Code z d s) (hzR : Code zR dR p)
    (phi : Formula n) (v : Fin n → M.Carrier .set)
    (hsup : ∀ j, Supported (fun i => env (rho i)) fixing (v j))

    : Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v (env (rho 6)) z phi ↔
      Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v (env (rho 6)) zR phi := by
  constructor
  · exact forces_at_supporting_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm
      hpres hG hF hp hs hsp hd hRange hFix hR hz hzR phi v hsup
  · intro h
    have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
      hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
    exact ForcingFormula.mono hM hpre phi v (code_mem hpres (restricted_condition hM hd hR) hp hzR)
      (code_mem hpres hd hs hz)
      ((orderFormula_semantics env (rho 0) mul z zR).mpr
        ((code_le hz hzR).mpr ⟨fun t ht => ((hR t).mp ht).1,hsp⟩)) h

def code {k : Nat} (z d s : Fin k) : Formula k :=
  .ex ((PairSyntax.ordered (Fin.last k) d.castSucc s.castSucc).conj
    (ForcingWithTopCarrier.single z.castSucc (Fin.last k)))

theorem code_semantics {k : Nat} (env : Fin k → M.Carrier .set) (z d s : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (code z d s) ↔
      Code (env z) (env d) (env s) := by
  simp only [code,Code,Formula.Realize,KuratowskiZF.source_code,ForcingWithTopCarrier.single_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def tupleSupported {k n : Nat} (rho : Fin 7 → Fin k) (fixing : Fin k) (v : Fin n → Fin k) : Formula k :=
  ForcingSound.conjunction ((List.finRange n).map (fun j => ForcingEquivariantMix.fixedAll rho fixing (v j)))

theorem tupleSupported_semantics {k n : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (fixing : Fin k) (v : Fin n → Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (tupleSupported rho fixing v) ↔
      ∀ j, Supported (fun i => env (rho i)) (env fixing) (env (v j)) := by
  simp only [tupleSupported,ForcingTupleStabilizer.finite_conjunction,ForcingSupportedNames.supported_semantics (M := M)]

def constructionSentence {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR : Fin k) (v : Fin n → Fin k) (phi : Formula n) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound w) (.bound mu)) (.imp (ConstructionSaturationIndex.hartogs mu I) (.imp
    (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu)) (.imp (ConstructionSaturationMergers.allMergers
    w history kappa) (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e)) (.imp
    (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4)
    (rho 5) (rho 6))) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G)) (.imp
    (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.injection p (rho 0) I)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho
    0) I)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul s p)) (.imp (ProjectSyntax.encode id
    (ForcingCohenConditions.condition (rho 2) w d)) (.imp (ProjectSyntax.encode id
    (ForcingStabilizerTransport.image p (rho 0) A)) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing
    G A fixing)) (.imp (ConstructionCohenCompatibility.restricted A d dR) (.imp (ProjectSyntax.encode id (code z d
    s)) (.imp (ProjectSyntax.encode id (code zR dR p)) (.imp (ProjectSyntax.encode id
    (ForcingTupleStabilizer.tupleHS rho G (rho 6) F v)) (.imp (ProjectSyntax.encode id (tupleSupported rho fixing
    v)) (.iff (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain
    rho G F) id v (rho 6) z phi)) (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul)
    (ForcingPairUnion.domain rho G F) id v (rho 6) zR phi))))))))))))))))))))))))

  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionCohenCompatibility.restricted_freeClosed]

theorem construction_models {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR : Fin k) (v : Fin n → Fin k) (phi : Formula n)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.le_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingStabilizerTransport.image_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ConstructionCohenCompatibility.restricted_semantics hM,code_semantics (M := M),
    ForcingTupleStabilizer.tupleHS_semantics (M := M),tupleSupported_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hpres hG hF hp hs hsp hd hRange hFix hR hz hzR _hHS hsup
  exact forces_iff_restrict hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm
    hpres hG hF hp hs hsp hd hRange hFix hR hz hzR phi (fun i => bound (v i)) hsup

theorem construction_kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR : Fin k) (v : Fin n → Fin k) (phi : Formula n) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing dR z zR v phi hL hChoice)

end PPAC.Migration.ForcingSupportingRoot
