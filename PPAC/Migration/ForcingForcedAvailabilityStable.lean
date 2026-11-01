/- Fixed GraphFusion.forcedAvailability_dense_stable:605-613 at its actual
AssignedGraphs.graphRelation_onto:236 consumer. The input is the normalized
local class supplied by existing actual_labelClass, including isClass at every
condition. Build its literal availability family; do not assume ideality or
stability. Reuse the existing principal-filter eligible system and source
height/cost stabilization. -/
import PPAC.Migration.ConstructionIdealStability
import PPAC.Migration.ForcingForcedAvailability
import PPAC.Migration.ForcingStableAt

namespace PPAC.Migration.ForcingForcedAvailabilityStable
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (Injection MapsTo)
open ForcingForcedAvailability (Carrier carrier carrier_freeClosed carrier_semantics)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem class_ideal (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau : Fin k)
    {d U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap)) (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hq : Injection (env (rho 0)) (env I) (env q)) (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))

    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hr : Injection (env (rho 0)) (env I) (env r))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hLocal : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env Hr) (env tau))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (hRoot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hForce : ∀ z, ForcingSupportingRoot.Code z d (env r) →
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2))
    (hU : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul)
      (env bound) d (env r) (env a) (env tau) U) :
    ConstructionIdealProbes.ConeIdeal (env (rho 0)) (env mul) (env a) U := by
  obtain ⟨g,hg⟩ := ForcingPrincipalFilter.exists_principal hM (env (rho 3)) d
  have hgf := ForcingPrincipalFilter.principal_filter hd hg
  let params : Fin (k+1) → M.Carrier .set := Fin.cases g env
  obtain ⟨oi,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family_over hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) params Fin.succ (fun j => (rho j).succ)
    G.succ F.succ mul.succ 0 q.succ bound.succ labels.succ E.succ I.succ (rho 4).succ hp.2.2.2.1
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM env (rho 0) mul (rho 4)
  obtain ⟨mi,maps,hMap,hMaps⟩ := ForcingEligibleMapFamily.exists_family_at_filter hM env rho G F mul
    I K B w one q bound labels E g S hm hp hgf hS
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound
    hgf hq hAq hHq hE hObj hS hMaps
  obtain ⟨Or,hrO,_⟩ := hObjMap.1.2 (env r) ((hp.2.2.2.1 (env r)).mpr hr)
  obtain ⟨Ar',Hr',X,Q,pr,hData⟩ := ((hObj (env r) Or).mp hrO).2
  have hArEq : Ar' = env Ar := (ModelTransfer.extensionality hM).eq_of_same_members _ _
    (fun j => (hData.1 j).trans (hAr j).symm)
  have hHrEq : Hr' = env Hr := ForcingLabelPermutations.fixing_unique hM (hArEq ▸ hData.2.1) hHr
  have hTau : (Project.FirstOrderSemantics.reduct M).mem (env tau) X :=
    (hData.2.2.1 (env tau)).mpr (hHrEq.symm ▸ hLocal)
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM d (env r)
  obtain ⟨x,fiber,_,hFiber,hx⟩ := ForcingForcedAvailability.exists_fiber_principal hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE
    hd hg hObjMap hObj hS hMap hMaps hrO hData hRoot hLabelBound ha hTau hz (hForce z hz) hU
  have hActual := (hFiber x).mp hx
  exact ForcingSystemAvailability.carrier_ideal hM hm hp.2.2.2.1 hObjMap hS hMap hSys
    hrO hActual.1 ha hActual.2

private theorem carrier_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w one d e r a tau bound U V : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)))
    (hr : Injection (env (rho 0)) I r) (hde : ConstructionRealCuts.Subset d e)
    (hU : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) bound d r a tau U)
    (hV : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul) bound e r a tau V) :
    ConstructionRealCuts.Subset U V := by
  intro n hn
  obtain ⟨hn,hna,s,A,H,sigma,hs,hSub,hA,hH,hLocal,hEq⟩ := (hU n).mp hn
  exact (hV n).mpr ⟨hn,hna,s,A,H,sigma,hs,hSub,hA,hH,hLocal,
    ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he hr hde hEq⟩

private theorem availability_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul bound r a tau : Fin k) :
    ∃ graph, ∀ d U, PureKuratowski.PairMember M d U graph ↔
      (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)) ∧
        Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul)
          (env bound) d (env r) (env a) (env tau) U := by
  let schema : Project.BinarySchema k := {
    body := carrier (orderFormula (rho 0) mul) (fun j => j.succ.succ) (fun j => (rho j).succ.succ)
      G.succ.succ F.succ.succ mul.succ.succ bound.succ.succ 1 r.succ.succ a.succ.succ tau.succ.succ 0
    freeClosed := carrier_freeClosed .. }
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k :=
    {bound := env,free := fun _ => env (rho 0)}
  have hRel d U : schema.denote penv d U ↔
      Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul)
        (env bound) d (env r) (env a) (env tau) U :=
    carrier_semantics hM ((penv.push d).push U) (orderFormula (rho 0) mul) (fun j => j.succ.succ)
      (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ mul.succ.succ bound.succ.succ 1 r.succ.succ a.succ.succ tau.succ.succ 0
  have ht : ∀ d, (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)) → ∃ U, schema.denote penv d U := by
    intro d _
    let params : Fin (k+1) → M.Carrier .set := Fin.cases d env
    obtain ⟨U,hU⟩ := ForcingForcedAvailability.exists_carrier hM (orderFormula (rho 0) mul)
      params Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ a.succ tau.succ
    exact ⟨U,(hRel d U).mpr hU⟩
  have hu : ∀ d, (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)) → ∀ U V,
      schema.denote penv d U → schema.denote penv d V → U = V := by
    intro d _ U V hU hV
    exact (ModelTransfer.extensionality hM).eq_of_same_members U V
      (fun n => ((hRel d U).mp hU n).trans ((hRel d V).mp hV n).symm)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImageOn hZF schema penv (env (rho 3)) ht hu
  obtain ⟨graph,_,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema penv ht hu (fun d U hd hU => (hImage U).mpr ⟨d,hd,hU⟩)
  exact ⟨graph,fun d U => (hGraph d U).trans (and_congr_right (fun _ => hRel d U))⟩

theorem class_dense_stable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap)) (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hq : Injection (env (rho 0)) (env I) (env q)) (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))

    (hQ : ConstructionFractionOrder.Carrier (env w) (env Qcuts))
    (hR : ConstructionRealCuts.CutCarrier hM (env w) (env Qcuts) (env Rcuts))
    (hTopCut : ConstructionRealCuts.Cut hM (env w) (env Qcuts) (env realTop))
    (hObj : ConstructionRoundFields.ObjectFields hM (env w) (env Qcuts) (env Rcuts) (env realTop)
      (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C))
    (hr : Injection (env (rho 0)) (env I) (env r))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hLocal : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env Hr) (env tau))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (hRoot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hForce : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6)) →
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2)) :
    ∃ e U, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) ∧ ConstructionRealCuts.Subset (env d) e ∧
      ConstructionIdealProbes.ConeIdeal (env (rho 0)) (env mul) (env a) U ∧
      ∀ f, (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)) → ConstructionRealCuts.Subset e f →
        Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul)
          (env bound) f (env r) (env a) (env tau) U := by
  obtain ⟨graph,hGraph⟩ := availability_family hM env rho G F mul bound r a tau
  have hIdeal e U (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)))
      (hU : Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F) (env mul)
        (env bound) e (env r) (env a) (env tau) U) : ConstructionIdealProbes.ConeIdeal (env (rho 0)) (env mul) (env a) U :=
    class_ideal hM hChoice env rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE hLabelBound
      hr hAr hHr hLocal ha hRoot he
      (fun z hz => hForce z (ForcingSupportingRoot.code_mem hp ((hp.2.2.1 e).mp he) hr hz)) hU
  have hFamily : ConstructionIdealStability.Family (env (rho 2)) (env w) (env (rho 0)) (env mul) (env a) graph := by
    refine ⟨?_,?_,?_⟩
    · intro e he
      let params : Fin (k+1) → M.Carrier .set := Fin.cases e env
      obtain ⟨U,hU⟩ := ForcingForcedAvailability.exists_carrier hM (orderFormula (rho 0) mul)
        params Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ a.succ tau.succ
      exact ⟨U,(hGraph e U).mpr ⟨(hp.2.2.1 e).mpr he,hU⟩⟩
    · intro e U he hU
      exact hIdeal e U ((hp.2.2.1 e).mpr he) ((hGraph e U).mp hU).2
    · intro e f U V _ hf hef hU hV
      exact carrier_mono hM env rho G F mul hm hp ((hp.2.2.1 f).mpr hf) hr hef
        ((hGraph e U).mp hU).2 ((hGraph f V).mp hV).2
  obtain ⟨e,he,hde,hStable⟩ := ConstructionIdealStability.dense_stable_ideal hM hChoice
    hw hQ hR hTopCut hObj hFamily ((hp.2.2.1 (env d)).mp hd)
  obtain ⟨U,heU⟩ := hFamily.1 e he
  have heX := (hp.2.2.1 e).mpr he
  refine ⟨e,U,heX,hde,hIdeal e U heX ((hGraph e U).mp heU).2,?_⟩
  intro f hf hef
  have hfC := (hp.2.2.1 f).mp hf
  obtain ⟨V,hfV⟩ := hFamily.1 f hfC
  have eUV := hStable f U V hfC hef heU hfV
  exact eUV.symm ▸ ((hGraph f V).mp hfV).2

theorem class_dense_vertex (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap)) (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hq : Injection (env (rho 0)) (env I) (env q)) (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))

    (hQ : ConstructionFractionOrder.Carrier (env w) (env Qcuts))
    (hR : ConstructionRealCuts.CutCarrier hM (env w) (env Qcuts) (env Rcuts))
    (hTopCut : ConstructionRealCuts.Cut hM (env w) (env Qcuts) (env realTop))
    (hObj : ConstructionRoundFields.ObjectFields hM (env w) (env Qcuts) (env Rcuts) (env realTop)
      (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C))
    (hr : Injection (env (rho 0)) (env I) (env r))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hLocal : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env Hr) (env tau))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (hRoot : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hForce : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6)) →
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2)) :
    ∃ e U vertex, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) ∧
      ConstructionRealCuts.Subset (env d) e ∧ ConstructionComponentCarrier.Code vertex (env r) (env a) U ∧
      ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env r) (env a) U ∧
      ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertex (env tau) ∧
      ForcingStableAt.StableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (fun j => env (rho j)) (env G) (env F) (env mul) (env bound) (env labels) (env E) e vertex (env tau) := by
  obtain ⟨e,U,he,hde,hIdeal,hStable⟩ := class_dense_stable hM hChoice env rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE hLabelBound
    hQ hR hTopCut hObj hr hAr hHr hLocal ha hRoot hd hForce
  obtain ⟨vertex,hCode⟩ := ConstructionComponentCarrier.code_total hM (env r) (env a) U
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM e (env r)
  have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 e).mp he) hr hz
  exact ⟨e,U,vertex,he,hde,hCode,⟨hr,hRoot,hIdeal⟩,
    ⟨env r,env a,U,env Ar,env Hr,hCode,hAr,hHr,hLocal⟩,
    ⟨env r,env a,U,env Ar,env Hr,z,hCode,hAr,hHr,hLocal,hz,hForce z hzW,hStable⟩⟩

def stabilitySentence {k : Nat} (rho : Fin 7 → Fin k) (G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ConstructionFractionOrder.carrier w Qcuts)
    (.imp (ConstructionRealCuts.cutCarrier w Qcuts Rcuts)
    (.imp (ConstructionRealCuts.cut w Qcuts realTop)
    (.imp (ConstructionRoundStepSyntax.objectFields w Qcuts Rcuts realTop (rho 0) mul one mark H C)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.localName rho G F bound Hr tau))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (.forallE (.imp (.mem (.bound 0) (.bound (rho 6).succ))
      (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
        Fin.succ (Source.SetLanguage.args3 tau.succ labels.succ E.succ) (rho 6).succ 0 (ForcingEligibility.isClass 0 1 2)))))
      (.existsE (.existsE (.existsE
        (.conj (.mem (.bound 2) (.bound (rho 3).succ.succ.succ))
        (.conj (Project.Formula.subset (.bound d.succ.succ.succ) (.bound 2))
        (.conj (ConstructionComponentCarrier.code 0 r.succ.succ.succ a.succ.succ.succ 1)
        (.conj (ConstructionComponentVertices.vertex (rho 0).succ.succ.succ I.succ.succ.succ mul.succ.succ.succ
          q.succ.succ.succ r.succ.succ.succ a.succ.succ.succ 1)
        (.conj (ForcingTailCodes.entry (fun j => (rho j).succ.succ.succ) G.succ.succ.succ F.succ.succ.succ bound.succ.succ.succ 0 tau.succ.succ.succ)
          (ForcingStableAt.stableAt (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
            (fun j => j.succ.succ.succ) (fun j => (rho j).succ.succ.succ)
            G.succ.succ.succ F.succ.succ.succ mul.succ.succ.succ bound.succ.succ.succ labels.succ.succ.succ E.succ.succ.succ
            2 0 tau.succ.succ.succ)))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionRealCuts.cut_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.subset,
      ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed,
      ForcingTailCodes.entry_freeClosed,ForcingStableAt.stableAt_freeClosed]

theorem stability_models {k : Nat} (rho : Fin 7 → Fin k) (G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (stabilitySentence rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ForcingLocalNames.localName_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),ConstructionComponentCarrier.code_semantics hM,
    ConstructionComponentVertices.vertex_semantics hM,ForcingTailCodes.entry_semantics hM,ForcingStableAt.stableAt_semantics hM]
  exact class_dense_vertex hM hChoice env rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop

theorem stability_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (stabilitySentence rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (stabilitySentence rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (stabilitySentence rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop)).mp
      (stability_models rho G F mul w mu history kappa one mark H C incoming base I K B labelMap top bit labels bound E q Aq Hq Ar Hr r a tau d Qcuts Rcuts realTop hL hChoice)

end PPAC.Migration.ForcingForcedAvailabilityStable
