/- Pinned OrdinalCodes.forces_at_root:260, eq_at_root:271 and
ordinal_decide_at_root:287. Reuse actual supporting-root reflection and
ordinary ordinal decision; the full Cohen condition and SAME root remain. -/
import PPAC.Migration.ForcingOrdinalCoding
import PPAC.Migration.ForcingSupportingRoot

namespace PPAC.Migration.ForcingOrdinalRoot
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingSupportSize (Injection Small)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces forces)
open ForcingCohenConditions (Condition)
open ForcingSupportedNames (Supported)
open ForcingSupportingRoot (Code code code_mem code_le exists_code)
open ForcingCheckName (Checked checkName)
open ForcingRawRank (Rank Ordinal)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem check_supported (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w top x name fixing : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (ht : ForcingWithTopCarrier.Empty top) (hn : Checked top x name) : Supported v fixing name := by
  intro g _ act hact
  have ha := (mapRel_action v g act).mp hact
  have hr := (ForcingProductFamily.action_permutation ha).1
  have htP := (hp.2.2.2.2.2 top).mpr (Or.inl ht)
  obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM hr name
  have he := ForcingCheckNameLaws.action_fixed hM (args2 (v 6) act) (0 : Fin 2) 1 hr
    (Or.inl ⟨htP,ForcingProductFamily.top_fixed hp ht ha⟩) hn hout
  exact he ▸ hout

def RootDecision {k : Nat} (L : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (P S w top sigma root d rank : M.Carrier .set) : Prop :=
  ∃ e z beta nb, Condition S w e ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset d e ∧
    Code z e root ∧ Ordinal beta ∧ (beta = rank ∨ (Project.FirstOrderSemantics.reduct M).mem beta rank) ∧
      Checked top beta nb ∧ Forces true L env P sigma nb z

section Root
variable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B p A fixing : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hp : Injection (env (rho 0)) I p)
    (hRange : ForcingStabilizerTransport.Image p (env (rho 0)) A)
    (hFix : ForcingLabelPermutations.Fixing (env G) A fixing)
include hM hChoice hw hMu hI hD hMergers hRow hm hpres hG hF hp hRange hFix

theorem forces_at_root {n : Nat} {s d z zr : M.Carrier .set}
    (hs : Injection (env (rho 0)) I s) (hsp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s p)
    (hd : Condition (env (rho 2)) w d) (hz : Code z d s) (hzr : Code zr d p)
    (phi : Formula n) (v : Fin n → M.Carrier .set)
    (hsup : ∀ j, Supported (fun i => env (rho i)) fixing (v j))
    (hforce : Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v (env (rho 6)) z phi) :
    Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env v (env (rho 6)) zr phi := by
  obtain ⟨dR,hdR,hR,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hd A
  obtain ⟨zR,hzR⟩ := exists_code hM dR p
  have h := ForcingSupportingRoot.forces_at_supporting_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm
    hpres hG hF hp hs hsp hd hRange hFix hR hz hzR phi v hsup hforce
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  exact ForcingFormula.mono hM hpre phi v (code_mem hpres hdR hp hzR) (code_mem hpres hd hp hzr)
    ((orderFormula_semantics env (rho 0) mul zr zR).mpr ((code_le hzr hzR).mpr
      ⟨fun t ht => ((hR t).mp ht).1,ForcingDiagramPoset.le_refl hm hp⟩)) h

theorem eq_at_root {s d z zr tau sigma : M.Carrier .set}
    (hs : Injection (env (rho 0)) I s) (hsp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s p)
    (hd : Condition (env (rho 2)) w d) (hz : Code z d s) (hzr : Code zr d p)
    (htau : Supported (fun i => env (rho i)) fixing tau)
    (hsigma : Supported (fun i => env (rho i)) fixing sigma)
    (he : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau sigma z) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau sigma zr := by
  have hsup : ∀ j : Fin 2, Supported (fun i => env (rho i)) fixing (args2 tau sigma j) := by
    intro j
    refine Fin.cases htau (fun i => ?_) j
    exact Fin.cases hsigma (fun v => Fin.elim0 v) i
  exact forces_at_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF hp hRange hFix
    hs hsp hd hz hzr (.equal (0 : Fin 2) 1) (args2 tau sigma) hsup he

theorem ordinal_decide_at_root {d z top sigma rank : M.Carrier .set}
    (hd : Condition (env (rho 2)) w d) (hz : Code z d p) (ht : ForcingWithTopCarrier.Empty top)
    (hHS : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) sigma)
    (hsup : Supported (fun i => env (rho i)) fixing sigma) (hrank : Rank sigma rank)
    (ho : ForcingOrdinalTransitivity.OrdF (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      env (env (rho 6)) z sigma) :
    RootDecision (orderFormula (rho 0) mul) env (env (rho 6)) (env (rho 2)) w top sigma p d rank := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have htP := (hpres.2.2.2.2.2 top).mpr (Or.inl ht)
  have htop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q top :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q top).mpr (Or.inl ht)
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hdomain := fun s => ForcingPairUnion.domain_semantics env rho G F s
  have hcheck : ∀ x nx, Checked top x nx →
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env nx := by
    intro x nx hn
    exact (hdomain nx).mpr (ForcingInfinity.check_hs hM (fun i => env (rho i)) hpres hG hNormal ht hn)
  obtain ⟨q,hq,hqz,beta,hbeta,hbound,nb,hnb,he⟩ :=
    ForcingOrdinalDecision.ordF_eq_check_le hM hpre htP htop hdomain hcheck sigma z rank
      ((hdomain sigma).mpr hHS) (code_mem hpres hd hp hz) hrank ho
  obtain ⟨cz,hcz,hzs⟩ := hz
  rcases (orderFormula_semantics env (rho 0) mul q z).mp hqz with hzEmpty | ⟨cq,cz',hqs,hzs',hqprod⟩
  · exact False.elim (ForcingWithTopCarrier.single_nonempty hzs hzEmpty)
  · have hczEq := ForcingWithTopCarrier.single_injective hzs' hzs
    subst cz'
    have hcq := ForcingProductPoset.coe_mem hpres.2.2.2.2.2 hq hqs
    obtain ⟨de,hdeX,s,hsY,hcqs⟩ := (hpres.2.2.2.2.1 cq).mp hcq
    have hde := (hpres.2.2.1 de).mp hdeX
    have hs := (hpres.2.2.2.1 s).mp hsY
    have hqCode : Code q de s := ⟨cq,hcqs,hqs⟩
    have hb := (code_le hqCode ⟨cz,hcz,hzs⟩).mp (Or.inr ⟨cq,cz,hqs,hzs,hqprod⟩)
    obtain ⟨zr,hzr⟩ := exists_code hM de p
    exact ⟨de,zr,beta,nb,hde,hb.1,hzr,hbeta,hbound,hnb,
      eq_at_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF hp hRange hFix
        hs hb.2 hde hqCode hzr hsup (check_supported hM (fun i => env (rho i)) hpres ht hnb) he⟩
end Root

def rootDecision {k m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (P S w top sigma root d rank : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let de := (Fin.last m).castSucc.castSucc.castSucc
  let z := (Fin.last (m+1)).castSucc.castSucc
  let beta := (Fin.last (m+2)).castSucc
  let nb := Fin.last (m+3)
  .ex (.ex (.ex (.ex ((ForcingCohenConditions.condition (up S) (up w) de).conj
    ((Source.SetLanguage.subset (up d) de).conj ((code z de (up root)).conj
      ((OrdinalSyntax.ordinal beta).conj (((Formula.equal beta (up rank)).disj (.mem beta (up rank))).conj
        ((checkName (up top) beta nb).conj (forces true L (fun i => up (lp i)) (up P) (up sigma) nb z))))))))))

theorem rootDecision_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (lp : Fin k → Fin m) (P S w top sigma root d rank : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (rootDecision L lp P S w top sigma root d rank) ↔
      RootDecision L (fun i => env (lp i)) (env P) (env S) (env w) (env top) (env sigma) (env root) (env d) (env rank) := by
  simp only [rootDecision,RootDecision,Formula.Realize,ForcingCohenConditions.condition_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingRawRank.ordinal_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- The unchanged source ground-system inputs already used by supporting-root reflection. -/
def rootContext {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p A fixing : Fin k) : Project.Formula 1 k :=
  (.conj (Project.Formula.isOmega (.bound w))
    (.conj (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.conj (ConstructionSaturationIndex.hartogs mu I)
    (.conj (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.conj (ConstructionSaturationMergers.allMergers w history kappa)
    (.conj (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.conj (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.conj (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.conj (ProjectSyntax.encode id (ForcingStabilizerTransport.image p (rho 0) A))
    (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A fixing))))))))))))))

def formulaBody {k n : Nat} (rho : Fin 7 → Fin k) (I G F mul w p s d fixing z zr : Fin k)
    (v : Fin n → Fin k) (phi : Formula n) : Formula k :=
  (Source.SetLanguage.injection s (rho 0) I).imp
    ((ForcingDiagramOrder.le (rho 0) mul s p).imp ((ForcingCohenConditions.condition (rho 2) w d).imp
      ((code z d s).imp ((code zr d p).imp ((ForcingTupleStabilizer.tupleHS rho G (rho 6) F v).imp
        ((ForcingSupportingRoot.tupleSupported rho fixing v).imp
          ((ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id v (rho 6) z phi).imp
            (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id v (rho 6) zr phi))))))))

def decisionBody {k : Nat} (rho : Fin 7 → Fin k) (G F mul w p d fixing z top sigma rank : Fin k) : Formula k :=
  (ForcingWithTopCarrier.empty top).imp ((ForcingCohenConditions.condition (rho 2) w d).imp
    ((code z d p).imp ((ForcingHS.hs actionFormula rho G (rho 6) F sigma).imp
      ((ForcingEquivariantMix.fixedAll rho fixing sigma).imp ((LayerRankSyntax.rank sigma rank).imp
        ((ForcingOrdinalTransitivity.ordF (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (rho 6) z sigma).imp
          (rootDecision (orderFormula (rho 0) mul) id (rho 6) (rho 2) w top sigma p d rank)))))))

def constructionSentence {k n : Nat} (ordinal : Bool) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing z zr top sigma rank : Fin k)
    (v : Fin n → Fin k) (phi : Formula n) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp
    (rootContext rho w mu history kappa e mark H C incoming base I K B G F mul p A fixing)
    (ProjectSyntax.encode id (if ordinal then decisionBody rho G F mul w p d fixing z top sigma rank
      else formulaBody rho I G F mul w p s d fixing z zr v phi)))
  freeClosed := by
    simp -implicitDefEqProofs [rootContext,Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ProjectSyntax.freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed]

theorem construction_models {k n : Nat} (ordinal : Bool) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing z zr top sigma rank : Fin k)
    (v : Fin n → Fin k) (phi : Formula n) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence ordinal rho w mu history kappa e mark H C incoming base I K B G F mul
      p s d A fixing z zr top sigma rank v phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  cases ordinal <;> simp only [rootContext,formulaBody,decisionBody,Bool.false_eq_true,ite_false,ite_true,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    ForcingStabilizerTransport.image_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    Formula.Realize,ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.le_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingTupleStabilizer.tupleHS_semantics (M := M),ForcingSupportingRoot.tupleSupported_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingRawRank.rank_semantics (M := M),ForcingOrdinalTransitivity.ordF_semantics (M := M),
    rootDecision_semantics (M := M),Project.Term.eval_bound]
  · rintro ⟨hw,hMu,hI,hD,hMergers,hRow,hm,hpres,hG,hF,hp,hRange,hFix⟩ hs hsp hd hz hzr _hHS hsup hforce
    exact forces_at_root hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF hp hRange hFix
      hs hsp hd hz hzr phi (fun i => bound (v i)) hsup hforce
  · rintro ⟨hw,hMu,hI,hD,hMergers,hRow,hm,hpres,hG,hF,hp,hRange,hFix⟩ ht hd hz hHS hsup hrank ho
    exact ordinal_decide_at_root hM hChoice bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF hp hRange hFix
      hd hz ht hHS hsup hrank ho

/-- Same internal L and existing full ZFC/choice production as supporting-root reflection. -/
theorem construction_kernel_certificate {k n : Nat} (ordinal : Bool) (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing z zr top sigma rank : Fin k)
    (v : Fin n → Fin k) (phi : Formula n) : FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence ordinal rho w mu history kappa e mark H C incoming base
        I K B G F mul p s d A fixing z zr top sigma rank v phi))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence ordinal rho w mu history kappa e mark H C incoming base
    I K B G F mul p s d A fixing z zr top sigma rank v phi)
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL)
    (constructionSentence ordinal rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing z zr top sigma rank v phi)).mp
    (construction_models ordinal rho w mu history kappa e mark H C incoming base I K B G F mul p s d A fixing z zr top sigma rank v phi hL hChoice)

end PPAC.Migration.ForcingOrdinalRoot
