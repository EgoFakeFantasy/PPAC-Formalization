/- Pinned Models/OrdinalChoice.indexedGraph_choiceForFamily and
ground_family_choice. Consume the actual indexed graph and completed
localized maximum; native Collection replaces the source host choose.
All families, indices, support graphs and names are internal sets. -/
import PPAC.Migration.ForcingIndexedGraph
import PPAC.Migration.ForcingLocalizedMaximum
import PPAC.Migration.ForcingOrdinalChoice

namespace PPAC.Migration.ForcingGroundFamilyChoice
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingSupportSize (Injection Small)
open ForcingSupportedNames (Supported Range)
open ForcingCohenConditions (Condition)
open ForcingConditionGraphs (FunctionOn)
open ForcingCheckName (Checked)
open ForcingSupportingRoot (Code)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem checked_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t x checked : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t) (hc : Checked t x checked) :
    ForcingHS.HS actionFormula v G (v 6) F checked := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  apply ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hF.1 htW ?_ x checked hc
  intro pi hpi
  obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG pi).mp hpi)
  exact ⟨act,(mapRel_action v pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
    Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ha⟩⟩

private theorem app_input_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set} {P p F x x' y : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (he : Forces true R env P x x' p) :
    Force R H env (args3 F x y) P p (Source.SetLanguage.edge 0 1 2) ↔
      Force R H env (args3 F x' y) P p (Source.SetLanguage.edge 0 1 2) := by
  apply ForcingFormula.tuple_congr hM hpre _ _ _ p hp
  intro j
  exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre F p hp)
    (Fin.cases he (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre y p hp) (fun i => Fin.elim0 i))) j

/-- Exact source indexedGraph_choiceForFamily: full internal choice graph,
including the source functionOn no-junk and unique-value conjuncts. -/
theorem indexedGraph_choiceForFamily (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul t : Fin k)
    {I K B w X f graph checkedX family p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hf : FunctionOn X f) (hChecked : Checked (env t) X checkedX)
    (hFamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) X f)
    (hGraph : ForcingIndexedGraph.Graph (env (rho 6)) X (env t) f graph)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hfun : Force (orderFormula (rho 0) mul) (domain rho G F) env (args2 family checkedX)
      (env (rho 6)) p (Source.SetLanguage.functionOn 0 1))
    (hEach : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i X → PureKuratowski.PairMember M i nu f →
      ∀ ci, Checked (env t) i ci → Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 family ci nu)
        (env (rho 6)) p ForcingOrdinalChoice.familyMember) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph checkedX family)
      (env (rho 6)) p (Source.SetLanguage.choiceForFamily 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  have htW := (hPres.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htop : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a W → MapRel R env a (env t) :=
    fun a _ => (orderFormula_semantics env (rho 0) mul a (env t)).mpr (Or.inl ht)
  apply (ForcingOrdinalChoice.forces_choiceForFamily hM hpre hp (args3 graph checkedX family) 0 1 2).mpr
  refine ⟨ForcingIndexedGraph.functionOn hM env rho G F mul t (args3 graph checkedX family) 0 1
    hPres hG hF ht hpre hf hChecked hFamily hGraph hp,?_⟩
  intro x _hx y hy q hq hqp hxmem r hr hrq hApp s hs hsr
  obtain ⟨a,ha,has,i,hi,ci,hci,he⟩ := (ForcingInfinity.mem_check hM hChecked htW htop hq).mp hxmem s hs
    (hpre.2 s r q hs hr hq hsr hrq)
  obtain ⟨nu,hif,_⟩ := hf.2 i hi
  have hNuHS := hFamily i nu hi hif
  have hCiHS := checked_hs hM (fun j => env (rho j)) hPres hG hF ht hci
  have hap := hpre.2 a s p ha hs hp has (hpre.2 s r p hs hr hp hsr (hpre.2 r q p hr hq hp hrq hqp))
  have har := hpre.2 a s r ha hs hr has hsr
  have hAppI := (app_input_congr hM hpre ha he).mp (ForcingFormula.mono hM hpre _ _ hr ha har hApp)
  have hMem' : Forces false R env W nu y a := ForcingOrdinalChoice.familyMember_mem hM hpre ha
    (args2 family checkedX) 0 1 (ForcingFormula.mono hM hpre _ _ hp ha hap hfun)
    ((domain_semantics env rho G F ci).mpr hCiHS) hy ((domain_semantics env rho G F nu).mpr hNuHS)
    (ForcingInfinity.check_mem_of_mem hM hpre hChecked hci hi htW htop ha) hAppI
    (ForcingFormula.mono hM hpre _ _ hp ha hap (hEach i nu hi hif ci hci))
  refine ⟨a,ha,has,nu,(domain_semantics env rho G F nu).mpr hNuHS,?_,hMem'⟩
  apply (app_input_congr hM hpre ha he).mpr
  exact ForcingIndexedGraph.app_at hM env rho G F mul t hPres hG hF ht hpre hGraph hFamily hi hci hif ha

def Selected {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → M.Carrier .set) (G F Hq top family zq i nu : M.Carrier .set) : Prop :=
  ForcingHS.HS actionFormula rho G (rho 6) F nu ∧ Supported rho Hq nu ∧
    ∃ ci, Checked top i ci ∧ Force R H env (args3 family ci nu) (rho 6) zq ForcingOrdinalChoice.familyMember

def selected {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F Hq top family zq i nu : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F nu))
    (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq nu))
      (.existsE (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName top.succ i.succ 0))
        (ProjectSyntax.encode id (ForcingFormula.formula R H (fun j => (base j).succ)
          (args3 family.succ 0 nu.succ) (rho 6).succ zq.succ ForcingOrdinalChoice.familyMember)))))

theorem selected_freeClosed {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F Hq top family zq i nu : Fin m) :
    (selected R H base rho G F Hq top family zq i nu).FreeClosed := by
  simp -implicitDefEqProofs [selected,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F Hq top family zq i nu : Fin m) :
    Project.Formula.satisfies env (selected R H base rho G F Hq top family zq i nu) ↔
      Selected R H (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound G) (env.bound F)
        (env.bound Hq) (env.bound top) (env.bound family) (env.bound zq) (env.bound i) (env.bound nu) := by
  simp only [selected,Selected,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingCheckName.checkName_semantics (M := M),
    ForcingFormula.formula_semantics (M := M)]
  simp only [SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero,id_eq]
  rfl

/-- The actual source host choose is replaced by Collection and the existing
bounded internal uniformization, applied to the precise selected-name formula. -/
theorem choose_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F Hq top family zq X : Fin k)
    (R : Formula (k+2)) (H : Formula (k+1))
    (hEach : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env X) → ∃ nu,
      Selected R H env (fun j => env (rho j)) (env G) (env F) (env Hq) (env top) (env family) (env zq) i nu) :
    ∃ f, FunctionOn (env X) f ∧ ∀ i nu, PureKuratowski.PairMember M i nu f →
      Selected R H env (fun j => env (rho j)) (env G) (env F) (env Hq) (env top) (env family) (env zq) i nu := by
  let schema : Project.BinarySchema k := {
    body := selected R H (fun j => j.succ.succ) (fun j => (rho j).succ.succ)
      G.succ.succ F.succ.succ Hq.succ.succ top.succ.succ family.succ.succ zq.succ.succ 1 0
    freeClosed := selected_freeClosed .. }
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => env X⟩
  have he i nu : schema.denote penv i nu ↔
      Selected R H env (fun j => env (rho j)) (env G) (env F) (env Hq) (env top) (env family) (env zq) i nu :=
    selected_semantics hM _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨names,hNames⟩ := ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM)
    schema penv (env X) (fun i hi => by obtain ⟨nu,hnu⟩ := hEach i hi; exact ⟨nu,(he i nu).mpr hnu⟩)
  obtain ⟨f,hf,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := env X) (Y := names) hNames
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hf).1,fun i nu h => (he i nu).mp (hSelect i nu h)⟩

private theorem code_unique (hM : FirstOrder.Theory.Models M nativeZF) {z z' d q : M.Carrier .set}
    (hz : Code z d q) (hz' : Code z' d q) : z = z' := by
  obtain ⟨c,hc,hs⟩ := hz
  obtain ⟨c',hc',hs'⟩ := hz'
  have eq := KuratowskiZF.code_unique hM hc' hc
  subst c'
  exact ForcingWithTopCarrier.single_unique hM hs hs'

theorem ground_family_choice (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 : Fin k)
    (top X checkedX family zq : Fin k)
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
    (hp : Injection (env (rho 0)) (env I) (env p)) (hq : Injection (env (rho 0)) (env I) (env q))
    (hSubQ : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hJp : Range (env (rho 0)) (env p) (env Jp)) (hHp : ForcingLabelPermutations.Fixing (env G) (env Jp) (env Hp))
    (hJq : Range (env (rho 0)) (env q) (env Jq)) (hHq : ForcingLabelPermutations.Fixing (env G) (env Jq) (env Hq))
    (hFixedFamily : Supported (fun i => env (rho i)) (env Hp) (env family))
    (hd0 : Condition (env (rho 2)) (env w) (env d0))
    (hd0q : ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) (env d0))
    (hz0 : Code (env z0) (env d0) (env p))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hChecked : Checked (env top) (env X) (env checkedX))
    (hzq : Code (env zq) (env d0) (env q))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args2 (env family) (env checkedX))
      (env (rho 6)) (env z0) (Source.SetLanguage.nonemptyFamily 0 1)) :
    ∃ graph, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun j => env (rho j)) (env Hq) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env checkedX) (env family))
        (env (rho 6)) (env zq) (Source.SetLanguage.choiceForFamily 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  let W := env (rho 6)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hz0W := ForcingSupportingRoot.code_mem hPres hd0 hp hz0
  have hzqW := ForcingSupportingRoot.code_mem hPres hd0 hq hzq
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTopLe : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a W → MapRel R env a (env top) :=
    fun a _ => (orderFormula_semantics env (rho 0) mul a (env top)).mpr (Or.inl ht)
  have hzq0 : MapRel R env (env zq) (env z0) :=
    (orderFormula_semantics env (rho 0) mul (env zq) (env z0)).mpr
      ((ForcingSupportingRoot.code_le hzq hz0).mpr ⟨fun _ h => h,env mark,hMark,hSubQ⟩)
  have hEach : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env X) → ∃ nu,
      Selected R Hdom env v7 (env G) (env F) (env Hq) (env top) (env family) (env zq) i nu := by
    intro i hi
    obtain ⟨ci,hci⟩ := ForcingCheckName.exists_checked hM (env top) i
    have hCiHS := checked_hs hM v7 hPres hG hNormal ht hci
    have hCiFixed : Supported v7 (env Hp) ci := by
      intro pi _hpi act hAct
      exact ForcingLabelNames.checked_fixed hM v7 hPres ht ((mapRel_action v7 pi act).mp hAct) hci
    let other : Fin (k+1) → M.Carrier .set := Fin.cases ci env
    let ra : Fin 7 → Fin (k+1) := fun j => (rho j).succ
    let tuple : Fin 2 → Fin (k+1) := args2 family.succ 0
    have hR (a b : M.Carrier .set) : MapRel R env a b ↔ MapRel (orderFormula (ra 0) mul.succ) other a b := by
      simp only [R,orderFormula_semantics,ra,other,Fin.cases_succ]
    have hH (a : M.Carrier .set) : ForcingClassEvaluation.Predicate Hdom env a ↔
        ForcingClassEvaluation.Predicate (domain ra G.succ F.succ) other a := by
      rw [domain_semantics,domain_semantics]
      rfl
    have hInput := ForcingOrdinalChoice.nonemptyFamily_member hM hpre hz0W (args2 (env family) (env checkedX)) 0 1 hf
      ((domain_semantics env rho G F ci).mpr hCiHS)
      (ForcingInfinity.check_mem_of_mem hM hpre hChecked hci hi htW hTopLe hz0W)
    have hv : ∀ j, Supported (fun a => other (ra a)) (other Hp.succ) (other (tuple j)) := by
      intro j
      exact Fin.cases hFixedFamily (Fin.cases hCiFixed (fun x => Fin.elim0 x)) j
    have hInput' := (ForcingSeparation.force_congr hR hH _ (args2 (env family) ci) W (env z0)).mp hInput
    obtain ⟨nu,out,hNu,hFix,hOut,hForce⟩ := ForcingLocalizedMaximum.localized_maximum hM hChoice other ra
      w.succ mu.succ history.succ kappa.succ unit.succ mark.succ H.succ C.succ incoming.succ base.succ
      I.succ K.succ B.succ G.succ F.succ mul.succ index.succ p.succ q.succ d0.succ
      Jp.succ Hp.succ Jq.succ Hq.succ z0.succ ForcingOrdinalChoice.familyMember tuple
      hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hSubQ
      hJp hHp hJq hHq hv hd0 hd0q hz0 hInput'
    have hvec : (Fin.lastCases nu (fun j => other (tuple j)) : Fin 3 → M.Carrier .set) = args3 (env family) ci nu := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun x => Fin.elim0 x))) j
    rw [hvec] at hForce
    have hOut' : Code out (env d0) (env q) := hOut
    have eq := code_unique hM hOut' hzq
    subst out
    exact ⟨nu,hNu,hFix,ci,hci,(ForcingSeparation.force_congr hR hH _ (args3 (env family) ci nu) W (env zq)).mpr hForce⟩
  obtain ⟨f,hfFn,hSelect⟩ := choose_family hM hChoice env rho G F Hq top family zq X R Hdom hEach
  have hFamily : ForcingCollectedHS.FamilyHS v7 (env G) W (env F) (env X) f :=
    fun i nu _ h => (hSelect i nu h).1
  have hFixed : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i (env X) →
      PureKuratowski.PairMember M i nu f → Supported v7 (env Hq) nu :=
    fun i nu _ h => (hSelect i nu h).2.1
  let envf : Fin (k+1) → M.Carrier .set := Fin.cases f env
  obtain ⟨pairs,graph,hPairs,hCollected,hGraph⟩ := ForcingIndexedGraph.exists_graph hM
    envf (rho 6).succ top.succ 0 (env X) hfFn
  obtain ⟨range,hRange,hRangeI,hRangeSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hD
  have hRangeEq : range = env Jq := (ModelTransfer.extensionality hM).eq_of_same_members range (env Jq)
    (fun x => (hRange x).trans (hJq x).symm)
  have hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset (env Jq) (env I) := hRangeEq ▸ hRangeI
  have hJSmall : Small (env Jq) (env mu) := hRangeEq ▸ hRangeSmall
  have hGroup := ForcingConjugationGraph.fixing_subgroup hM hG hHq hJI
  have hHF : (Project.FirstOrderSemantics.reduct M).mem (env Hq) (env F) :=
    (hFilter (env Hq)).mpr ⟨hGroup,env Jq,env Hq,hJI,hJSmall,hHq,fun _ h => h⟩
  obtain ⟨hGraphHS,hGraphFixed⟩ := ForcingIndexedGraph.hs_and_fixed hM v7 hPres hG hNormal
    hGroup hHF ht hFamily hFixed hPairs hCollected
  have hfun := (ForcingOrdinalChoice.forces_nonemptyFamily hM hpre hz0W (args2 (env family) (env checkedX)) 0 1).mp hf
  refine ⟨graph,hGraphHS,hGraphFixed,?_⟩
  apply indexedGraph_choiceForFamily hM env rho G F mul top
    hPres hG hNormal ht hpre hfFn hChecked hFamily hGraph hzqW
    (ForcingFormula.mono hM hpre _ _ hz0W hzqW hzq0 hfun.1)
  intro i nu _ hif ci hci
  obtain ⟨_,_,ci',hci',hForce⟩ := hSelect i nu hif
  have eq := ForcingCheckName.unique hM hci' hci
  exact eq ▸ hForce

def resultFormula {k : Nat} (rho : Fin 7 → Fin k) (G F Hq mul checkedX family zq : Fin k) : Project.Formula 1 k :=
  .existsE (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => (rho j).succ) G.succ (rho 6).succ F.succ 0))
    (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => (rho j).succ) Hq.succ 0))
      (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) (fun j => j.succ)
        (args3 0 checkedX.succ family.succ) (rho 6).succ zq.succ (Source.SetLanguage.choiceForFamily 0 1 2)))))

theorem resultFormula_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (G F Hq mul checkedX family zq : Fin k) :
    (resultFormula rho G F Hq mul checkedX family zq).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k) (G F Hq mul checkedX family zq : Fin k) :
    Project.Formula.satisfies env (resultFormula rho G F Hq mul checkedX family zq) ↔
      ∃ graph, ForcingHS.HS actionFormula (fun j => env.bound (rho j)) (env.bound G) (env.bound (rho 6)) (env.bound F) graph ∧
        Supported (fun j => env.bound (rho j)) (env.bound Hq) graph ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env.bound (args3 graph (env.bound checkedX) (env.bound family))
          (env.bound (rho 6)) (env.bound zq) (Source.SetLanguage.choiceForFamily 0 1 2) := by
  simp only [resultFormula,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingFormula.formula_semantics (M := M)]
  simp only [SetTheory.Env.push,Fin.cases_zero,Fin.cases_succ,id_eq]
  rfl

def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq : Fin k) :
    Project.Sentence where
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
      ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I),
      ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I),
      ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul q mark p),
      ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Jp),
      ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jp Hp),
      ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Jq),
      ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jq Hq),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hp family),
      ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0),
      ForcingLocalRecordPullback.supported (rho 0) q d0,
      ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 p),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingCheckName.checkName top X checkedX),
      ProjectSyntax.encode id (ForcingSupportingRoot.code zq d0 q),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args2 family checkedX) (rho 6) z0 (Source.SetLanguage.nonemptyFamily 0 1))].foldr Definitional.Formula.imp
      (resultFormula rho G F Hq mul checkedX family zq))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingRootProbes.rootProbes_freeClosed,
      ForcingLocalRecordPullback.supported_freeClosed,resultFormula_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq)).TrueIn M := by
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
    ForcingRootProbes.rootProbes_semantics hM,ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.sub_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingFormula.formula_semantics (M := M),resultFormula_semantics hM,id_eq]
  have hvec : (fun j => env (args2 family checkedX j)) = args2 (env family) (env checkedX) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  rw [hvec]
  exact ground_family_choice hM hChoice env rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq

/-- Native ZF's original kernel; the existing internal L interpretation
discharges ground Choice, and all original source background guards remain. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq))) := by
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
    (models rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 top X checkedX family zq hL hChoice)

end PPAC.Migration.ForcingGroundFamilyChoice
