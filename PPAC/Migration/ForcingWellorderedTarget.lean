/- Pinned OrderedSections.wellorderable_target_injection:489-520.
Actually instantiate the accepted internal uniform family, then consume the
actual section graph. No given ordinal, support, choice family or final graph. -/
import PPAC.Migration.ForcingSectionInjection

namespace PPAC.Migration.ForcingWellorderedTarget
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingSupportSize (Injection Small)
open ForcingSupportedNames (Supported Range)
open ForcingCheckName (Checked)
open ForcingSupportingRoot (Code)
open ForcingHS (HS)
open ForcingClassEvaluation (Predicate)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem injection_mapsTo (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f X Y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.injection 0 1 2)) :
    Force R H env (args3 f X Y) P p (Source.SetLanguage.mapsTo 0 1 2) := by
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  exact hf.1


/-- Exactly [f,X,Y,J,check(i)] as an INTERNAL functional parameter relation. -/
def parameterFormula {k : Nat} (top f X Y J : Fin k) : Formula (k+1+5) :=
  let up : Fin k → Fin (k+1+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let i := (Fin.last k).castSucc.castSucc.castSucc.castSucc.castSucc
  let a0 := (Fin.last (k+1)).castSucc.castSucc.castSucc.castSucc
  let a1 := (Fin.last (k+2)).castSucc.castSucc.castSucc
  let a2 := (Fin.last (k+3)).castSucc.castSucc
  let a3 := (Fin.last (k+4)).castSucc
  let a4 := Fin.last (k+5)
  (Formula.equal a0 (up f)).conj ((Formula.equal a1 (up X)).conj ((Formula.equal a2 (up Y)).conj
    ((Formula.equal a3 (up J)).conj (ForcingCheckName.checkName (up top) i a4))))

theorem parameter_spec_iff {k : Nat} (env : Fin k → M.Carrier .set) (top f X Y J : Fin k)
    (i : M.Carrier .set) (v : Fin 5 → M.Carrier .set) :
    ForcingUniformMaximum.ParameterSpec env (parameterFormula top f X Y J) i v ↔
      v 0 = env f ∧ v 1 = env X ∧ v 2 = env Y ∧ v 3 = env J ∧ Checked (env top) i (v 4) := by
  change Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
    (Fin.lastCases (v 4) (Fin.lastCases (v 3) (Fin.lastCases (v 2) (Fin.lastCases (v 1)
      (Fin.lastCases (v 0) (Fin.lastCases i env)))))) (parameterFormula top f X Y J) ↔ _
  simp only [parameterFormula,Formula.Realize,ForcingCheckName.checkName_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

theorem parameter_exists (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (top f X Y J : Fin k) (i : M.Carrier .set) :
    ∃ v, ForcingUniformMaximum.ParameterSpec env (parameterFormula top f X Y J) i v := by
  obtain ⟨ci,hCi⟩ := ForcingCheckName.exists_checked hM (env top) i
  exact ⟨ForcingMapCalculus.five (env f) (env X) (env Y) (env J) ci,
    (parameter_spec_iff env top f X Y J i _).mpr ⟨rfl,rfl,rfl,rfl,hCi⟩⟩

theorem parameter_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (top f X Y J : Fin k) {i : M.Carrier .set} {v v' : Fin 5 → M.Carrier .set}
    (h : ForcingUniformMaximum.ParameterSpec env (parameterFormula top f X Y J) i v)
    (h' : ForcingUniformMaximum.ParameterSpec env (parameterFormula top f X Y J) i v') : v = v' := by
  obtain ⟨h0,h1,h2,h3,hCi⟩ := (parameter_spec_iff env top f X Y J i v).mp h
  obtain ⟨h0',h1',h2',h3',hCi'⟩ := (parameter_spec_iff env top f X Y J i v').mp h'
  funext j
  exact Fin.cases (h0.trans h0'.symm) (Fin.cases (h1.trans h1'.symm) (Fin.cases (h2.trans h2'.symm)
    (Fin.cases (h3.trans h3'.symm) (Fin.cases (ForcingCheckName.unique hM hCi hCi') (fun a => Fin.elim0 a))))) j

theorem parameter_fixed (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (top f X Y J : Fin k)
    {I K B w S i : M.Carrier .set} {v : Fin 5 → M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hf : Supported (fun a => env (rho a)) S (env f)) (hX : Supported (fun a => env (rho a)) S (env X))
    (hY : Supported (fun a => env (rho a)) S (env Y)) (hJ : Supported (fun a => env (rho a)) S (env J))
    (h : ForcingUniformMaximum.ParameterSpec env (parameterFormula top f X Y J) i v) :
    ∀ j, Supported (fun a => env (rho a)) S (v j) := by
  obtain ⟨h0,h1,h2,h3,hCi⟩ := (parameter_spec_iff env top f X Y J i v).mp h
  have hCiFixed : Supported (fun a => env (rho a)) S (v 4) := by
    intro pi _hpi act hAct
    exact ForcingLabelNames.checked_fixed hM (fun a => env (rho a)) hPres ht ((mapRel_action _ _ _).mp hAct) hCi
  intro j
  exact Fin.cases (h0.symm ▸ hf) (Fin.cases (h1.symm ▸ hX) (Fin.cases (h2.symm ▸ hY)
    (Fin.cases (h3.symm ▸ hJ) (Fin.cases hCiFixed (fun a => Fin.elim0 a))))) j

theorem parameter_forces_exists (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y J : Fin k)
    {i checkedA p : M.Carrier .set} {v : Fin 5 → M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hY : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env Y))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2))
    (hJ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) (env Y) checkedA) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2))
    (h : ForcingUniformMaximum.ParameterSpec env (parameterFormula top f X Y J) i v) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p (.ex ForcingOrderedSections.indexedSection) := by
  obtain ⟨h0,h1,h2,h3,hCi⟩ := (parameter_spec_iff env top f X Y J i v).mp h
  have hValues : v = ForcingMapCalculus.five (env f) (env X) (env Y) (env J) (v 4) := by
    funext j
    exact Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (Fin.cases h3 (Fin.cases rfl (fun a => Fin.elim0 a))))) j
  rw [hValues]
  apply ForcingOrderedSections.indexedSection_exists hM hpre hp (env f) (env X) (env Y) (env J) checkedA (v 4) (env Y)
    ((domain_semantics env rho G F _).mpr (ForcingSectionInjection.checked_hs hM (fun a => env (rho a)) hPres hG hF ht hCi))
    ((domain_semantics env rho G F _).mpr hY) hf hJ

theorem section_inputs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y J : Fin k)
    (S p A checkedA : M.Carrier .set)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hY : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env Y))
    (hFixf : Supported (fun a => env (rho a)) S (env f)) (hFixX : Supported (fun a => env (rho a)) S (env X))
    (hFixY : Supported (fun a => env (rho a)) S (env Y)) (hFixJ : Supported (fun a => env (rho a)) S (env J))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y)) (env (rho 6)) p (Source.SetLanguage.surjection 0 1 2))
    (hJ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) (env Y) checkedA) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2)) :
    ForcingUniformMaximum.Inputs env rho G F mul S p A (parameterFormula top f X Y J) ForcingOrderedSections.indexedSection := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i _hi
    exact parameter_exists hM env top f X Y J i
  · intro i _hi v v' hv hv'
    exact parameter_unique hM env top f X Y J hv hv'
  · intro i _hi v hv
    exact parameter_fixed hM env rho top f X Y J hPres ht hFixf hFixX hFixY hFixJ hv
  · intro i _hi v hv
    exact parameter_forces_exists hM env rho I K B w G F mul top f X Y J hPres hG hF ht hpre hY hp hf hJ hv


def Result {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (X Y p : M.Carrier .set) : Prop :=
  ∃ out, (Project.FirstOrderSemantics.reduct M).mem out (env (rho 6)) ∧
    MapRel (orderFormula (rho 0) mul) env out p ∧ ∃ graph,
      HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph Y X)
        (env (rho 6)) out (Source.SetLanguage.injection 0 1 2)

theorem wellorderable_target_injection (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index : Fin k)
    (top f X Y p : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul)
      (env unit) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env (rho 0)) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hfHS : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env f))
    (hXHS : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env X))
    (hYHS : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env Y))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hWo : Force (orderFormula (rho 0) mul) (domain rho G F) env (args1 (env Y))
      (env (rho 6)) (env p) (ForcingCheckOrdinal.wellorderable 0)) :
    Result env rho G F mul (env X) (env Y) (env p) := by
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun a => env (rho a)
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  obtain ⟨r,hr,hrp,beta,_hBeta,checked,hChecked,J,hJHS,hJ⟩ := ForcingOrderedSections.wellorderable_check_dense
    hM env rho I K B w G F mul top hPres hG hNormal ht hpre hp hWo (env p) hp (hpre.1 (env p) hp)
  let parents : Fin 4 → M.Carrier .set := Fin.cases (env f) (args3 (env X) (env Y) J)
  have hNames : ∀ a, HS actionFormula v7 (env G) W (env F) (parents a) := by
    intro a
    exact Fin.cases hfHS (Fin.cases hXHS (Fin.cases hYHS (Fin.cases
      ((domain_semantics env rho G F J).mp hJHS) (fun b => Fin.elim0 b)))) a
  obtain ⟨S,hS,hSF,hTuple⟩ := ForcingTupleStabilizer.exists_tuple hM v7 hPres hG hNormal parents hNames
  have hFixed (a : Fin 4) : Supported v7 S (parents a) := by
    intro pi hpi act hAct
    exact ForcingTupleStabilizer.fixed_action hM hTuple hpi hAct a
  let other : Fin (k+1) → M.Carrier .set := Fin.cases J env
  let up : Fin k → Fin (k+1) := Fin.succ
  let rr : Fin 7 → Fin (k+1) := fun a => up (rho a)
  have he (a : Fin k) : other (up a) = env a := rfl
  have hR (a b : M.Carrier .set) : MapRel R env a b ↔ MapRel (orderFormula (rr 0) (up mul)) other a b := by
    simp only [R,orderFormula_semantics,rr,he]
  have hH (a : M.Carrier .set) : Predicate Hdom env a ↔ Predicate (domain rr (up G) (up F)) other a := by
    simp only [Hdom,domain_semantics,rr,he]
  have hpre' : ForcingAtomicBasic.PreorderOn (orderFormula (rr 0) (up mul)) other W := by
    constructor
    · intro a ha
      exact (hR a a).mp (hpre.1 a ha)
    · intro a b c ha hb hc hab hbc
      exact (hR a c).mp (hpre.2 a b c ha hb hc ((hR a b).mpr hab) ((hR b c).mpr hbc))
  have hfr := ForcingFormula.mono hM hpre (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) hp hr hrp hf
  have hfr' := (ForcingSeparation.force_congr hR hH (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) W r).mp hfr
  have hJ' := (ForcingSeparation.force_congr hR hH (Source.SetLanguage.injection 0 1 2) (args3 J (env Y) checked) W r).mp hJ
  let Q := parameterFormula (up top) (up f) (up X) (up Y) (0 : Fin (k+1))
  have hInputs : ForcingUniformMaximum.Inputs other rr (up G) (up F) (up mul) S r beta Q ForcingOrderedSections.indexedSection := by
    apply section_inputs hM other rr (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up top) (up f) (up X) (up Y) 0 S r beta checked
    · simpa only [rr,he] using hPres
    · simpa only [he] using hG
    · simpa only [he] using hNormal
    · simpa only [he] using ht
    · simpa only [rr,he] using hpre'
    · simpa only [rr,he] using hYHS
    · simpa only [rr,he,parents,Fin.cases_zero] using hFixed 0
    · simpa only [rr,he,parents,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ 0)
    · simpa only [rr,he,parents,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ 0))
    · simpa only [rr,he,other,parents,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ (Fin.succ 0)))
    · simpa only [rr,he] using hr
    · simpa only [rr,he] using hfr'
    · simpa only [rr,he,other,Fin.cases_zero] using hJ'
  obtain ⟨out,Hq,choices,hOut,hOutR,hHq,hHqF,hChoices,hSelected⟩ := ForcingUniformMaximum.uniform_maximum_dense hM hChoice other rr
    (up w) (up mu) (up history) (up kappa) (up unit) (up mark) (up H) (up C) (up incoming) (up base)
    (up I) (up K) (up B) (up G) (up F) (up mul) (up index) Q ForcingOrderedSections.indexedSection S r beta
    (by simpa only [he] using hw) (by simpa only [he] using hMu) (by simpa only [he] using hI)
    (by simpa only [rr,he] using hD) (by simpa only [rr,he] using hCard) (by simpa only [he] using hMergers)
    (by simpa only [rr,he] using hRow) (by simpa only [rr,he] using hm) (by simpa only [rr,he] using hPres)
    (by simpa only [he] using hG) (by simpa only [he] using hFilter) (by simpa only [rr,he] using hMark)
    (by simpa only [rr,he] using hProbes) (by simpa only [he] using hIndex) (by simpa only [he] using hSF)
    (by simpa only [rr,he] using hr) hInputs
  have hOutW : (Project.FirstOrderSemantics.reduct M).mem out W := by simpa only [rr,he] using hOut
  have hOutR' := (hR out r).mpr hOutR
  have hOutP := hpre.2 out r (env p) hOutW hr hp hOutR' hrp
  have hHq' : ForcingConjugationGraph.Subgroup (env I) (env G) Hq := by simpa only [he] using hHq
  have hHqF' : (Project.FirstOrderSemantics.reduct M).mem Hq (env F) := by simpa only [he] using hHqF
  obtain ⟨common,hCommon⟩ := KP.intersection_exists_d (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) S Hq
  have hCommonGroup := ForcingSupportIntersection.subgroup_intersection hM hG hS hHq' hCommon
  have hCommonF := hNormal.2.2.1 S Hq common hSF hHqF' hCommon
  have hFixParent (a : Fin 4) : Supported v7 common (parents a) := by
    intro pi hpi act hAct
    exact hFixed a pi ((hCommon pi).mp hpi).1 act hAct
  have hFamily : ForcingCollectedHS.FamilyHS v7 (env G) W (env F) beta choices := by
    intro i nu _hi hNu
    simpa only [rr,he] using (hSelected i nu hNu).1
  have hFamilyFixed : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i beta → PureKuratowski.PairMember M i nu choices → Supported v7 common nu := by
    intro i nu _hi hNu pi hpi act hAct
    have hFix : Supported v7 Hq nu := by simpa only [rr,he] using (hSelected i nu hNu).2.1
    exact hFix pi ((hCommon pi).mp hpi).2 act hAct
  have hSections : ForcingSectionInjection.Sections R Hdom env W beta choices (env top) (env f) (env X) (env Y) J out := by
    intro i _hi nu hNu ci hCi
    let v := ForcingMapCalculus.five (other (up f)) (other (up X)) (other (up Y)) (other 0) ci
    have hSpec : ForcingUniformMaximum.ParameterSpec other Q i v :=
      (parameter_spec_iff other (up top) (up f) (up X) (up Y) 0 i v).mpr
        ⟨rfl,rfl,rfl,rfl,by change Checked (other (up top)) i ci; simpa only [he] using hCi⟩
    have hForce := (hSelected i nu hNu).2.2 v hSpec
    apply (ForcingSeparation.force_congr hR hH ForcingOrderedSections.indexedSection
      (Fin.lastCases nu (ForcingMapCalculus.five (env f) (env X) (env Y) J ci)) W out).mpr
    simpa only [v,he,rr,other,Fin.cases_zero] using hForce
  have hfOut := ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hOutW
    (ForcingFormula.mono hM hpre (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) hp hOutW hOutP hf)
  have hJOut := injection_mapsTo hM hpre hOutW
    (ForcingFormula.mono hM hpre (Source.SetLanguage.injection 0 1 2) (args3 J (env Y) checked) hr hOutW hOutR' hJ)
  let finalEnv : Fin (k+6) → M.Carrier .set := Fin.cases common (Fin.cases choices (Fin.cases out
    (Fin.cases beta (Fin.cases checked (Fin.cases J env)))))
  let b (a : Fin k) : Fin (k+6) := a.succ.succ.succ.succ.succ.succ
  let rr6 : Fin 7 → Fin (k+6) := fun a => b (rho a)
  let slot (a : Fin 6) : Fin (k+6) := ⟨a.val,by omega⟩
  have e6 (a : Fin k) : finalEnv (b a) = env a := rfl
  have e0 : finalEnv (slot 0) = common := rfl
  have e1 : finalEnv (slot 1) = choices := rfl
  have e2 : finalEnv (slot 2) = out := rfl
  have e3 : finalEnv (slot 3) = beta := rfl
  have e4 : finalEnv (slot 4) = checked := rfl
  have e5 : finalEnv (slot 5) = J := rfl
  have hR6 (a c : M.Carrier .set) : MapRel R env a c ↔ MapRel (orderFormula (rr6 0) (b mul)) finalEnv a c := by
    simp only [R,orderFormula_semantics,rr6,e6]
  have hH6 (a : M.Carrier .set) : Predicate Hdom env a ↔ Predicate (domain rr6 (b G) (b F)) finalEnv a := by
    simp only [Hdom,domain_semantics,rr6,e6]
  have hpre6 : ForcingAtomicBasic.PreorderOn (orderFormula (rr6 0) (b mul)) finalEnv W := by
    constructor
    · intro a ha
      exact (hR6 a a).mp (hpre.1 a ha)
    · intro a c d ha hc hd hac hcd
      exact (hR6 a d).mp (hpre.2 a c d ha hc hd ((hR6 a c).mpr hac) ((hR6 c d).mpr hcd))
  have hSec6 : ForcingSectionInjection.Sections (orderFormula (rr6 0) (b mul)) (domain rr6 (b G) (b F)) finalEnv
      W beta choices (env top) (env f) (env X) (env Y) J out := by
    intro i hi nu hNu ci hCi
    exact (ForcingSeparation.force_congr hR6 hH6 ForcingOrderedSections.indexedSection
      (Fin.lastCases nu (ForcingMapCalculus.five (env f) (env X) (env Y) J ci)) W out).mp (hSections i hi nu hNu ci hCi)
  obtain ⟨graph,_hGraph,hGraphHS,_hGraphFixed,hGraphForce⟩ := ForcingSectionInjection.construct hM finalEnv rr6
    (b I) (b K) (b B) (b w) (b G) (b F) (slot 0) (b mul) (b top) (b f) (b X) (b Y) (slot 5) (slot 3) (slot 4) (slot 1) (slot 2)
    (by simpa only [rr6,e6] using hPres) (by simpa only [e6] using hG) (by simpa only [e6] using hNormal)
    (by simpa only [e6,e0] using hCommonGroup) (by simpa only [e6,e0] using hCommonF) (by simpa only [e6] using ht)
    (by simpa only [rr6,e6] using hpre6) (by simpa only [rr6,e6] using hXHS) (by simpa only [rr6,e6] using hYHS)
    (by simpa only [rr6,e6,e0,parents,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hFixParent (Fin.succ 0))
    (by simpa only [rr6,e6,e0,parents,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hFixParent (Fin.succ (Fin.succ 0)))
    (by simpa only [rr6,e6,e0,e5,parents,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ] using hFixParent (Fin.succ (Fin.succ (Fin.succ 0))))
    (by simpa only [e3,e1] using hChoices) (by simpa only [rr6,e6,e3,e1] using hFamily)
    (by simpa only [rr6,e6,e0,e3,e1] using hFamilyFixed) (by simpa only [e6,e3,e4] using hChecked)
    (by simpa only [rr6,e6,e2] using hOutW)
    (by simpa only [rr6,e6,e2] using (ForcingSeparation.force_congr hR6 hH6 (Source.SetLanguage.mapsTo 0 1 2) (args3 (env f) (env X) (env Y)) W out).mp hfOut)
    (by simpa only [rr6,e6,e2,e4,e5] using (ForcingSeparation.force_congr hR6 hH6 (Source.SetLanguage.mapsTo 0 1 2) (args3 J (env Y) checked) W out).mp hJOut)
    (by simpa only [rr6,e6,e2,e3,e1,e5] using hSec6)
  refine ⟨out,hOutW,hOutP,graph,?_,?_⟩
  · simpa only [rr6,e6] using hGraphHS
  · apply (ForcingSeparation.force_congr hR6 hH6 (Source.SetLanguage.injection 0 1 2) (args3 graph (env Y) (env X)) W out).mpr
    simpa only [rr6,e6,e2] using hGraphForce


/-- A stronger internal condition and an actual HS reverse injection graph. -/
def resultFormula {k : Nat} (rho : Fin 7 → Fin k) (G F mul X Y p : Fin k) : Formula k :=
  let b : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let out := (Fin.last k).castSucc
  let graph := Fin.last (k+1)
  .ex (.ex ((Formula.mem out (b (rho 6))).conj
    ((ReplacementPredicates.rel (orderFormula (rho 0) mul) b out (b p)).conj
      ((ForcingHS.hs actionFormula (fun j => b (rho j)) (b G) (b (rho 6)) (b F) graph).conj
        (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) b
          (args3 graph (b Y) (b X)) (b (rho 6)) out (Source.SetLanguage.injection 0 1 2))))))

theorem resultFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul X Y p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (resultFormula rho G F mul X Y p) ↔
      Result env rho G F mul (env X) (env Y) (env p) := by
  have hTuple (out graph : M.Carrier .set) :
      (fun i => Fin.lastCases graph (Fin.lastCases out env)
        (args3 (Fin.last (k+1)) Y.castSucc.castSucc X.castSucc.castSucc i)) =
      args3 graph (env Y) (env X) := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun a => Fin.elim0 a))) i
    all_goals simp only [args3,args2,args1,Fin.cases_zero,Fin.cases_succ,Fin.lastCases_last,Fin.lastCases_castSucc]
  simp only [resultFormula,Result,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingHS.hs_semantics,ForcingFormula.formula_semantics,Fin.lastCases_last,Fin.lastCases_castSucc,hTuple]
  constructor
  · rintro ⟨out,graph,hOut,hRel,hHS,hForce⟩
    exact ⟨out,hOut,hRel,graph,hHS,hForce⟩
  · rintro ⟨out,hOut,hRel,graph,hHS,hForce⟩
    exact ⟨out,graph,hOut,hRel,hHS,hForce⟩


def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index top f X Y p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([Project.Formula.isOmega (.bound w),
      Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu),
      ConstructionSaturationIndex.hartogs mu I,
      ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu),
      ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu,
      ConstructionSaturationMergers.allMergers w history kappa,
      ConstructionTowerHistory.row history kappa (rho 0) mul unit mark H C incoming base kappa,
      ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul unit),
      ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F),
      .mem (.bound mark) (.bound (rho 0)),
      ForcingRootProbes.rootProbes index (rho 0) mul unit mark,
      .neg (ProjectSyntax.encode id (ForcingSupportSize.small index w)),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args1 Y) (rho 6) p (ForcingCheckOrdinal.wellorderable 0))].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (resultFormula rho G F mul X Y p)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingRootProbes.rootProbes_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index top f X Y p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index top f X Y p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingRootProbes.rootProbes_semantics hM,ForcingWithTopCarrier.empty_semantics,ForcingHS.hs_semantics,
    ForcingFormula.formula_semantics,resultFormula_semantics,id_eq]
  intro hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex ht hfHS hXHS hYHS hp hf hWo
  exact wellorderable_target_injection hM hChoice env rho w mu history kappa unit mark H C incoming base I K B G F mul index
    top f X Y p hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex ht hfHS hXHS hYHS hp hf hWo

/-- Existing internal L discharges the source ground Choice. The ordinary
nativeZF original kernel proves the SAME L-relative wellorderable-target theorem. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index top f X Y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index top f X Y p))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (models rho w mu history kappa unit mark H C incoming base I K B G F mul index top f X Y p hL hChoice)

end PPAC.Migration.ForcingWellorderedTarget
