/- Pinned Models/OrdinalChoice.ground_family_choice_dense / forces_ACwo.
Reuse actual family choice, support extraction/coverage and ordinal decision.
All conditions, name supports, ground index sets and choice graphs are internal. -/
import PPAC.Migration.ForcingGroundFamilyChoice
import PPAC.Migration.ForcingOrdinalDecision
import PPAC.Migration.ConstructionDiagramCoverage

namespace PPAC.Migration.ForcingActualOrdinalChoice
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
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1800000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem ground_family_choice_dense (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index : Fin k)
    (top : Fin k) {X checkedX family start : M.Carrier .set}
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
    (hChecked : Checked (env top) X checkedX)
    (hFamily : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) family)
    (hStart : (Project.FirstOrderSemantics.reduct M).mem start (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args2 family checkedX)
      (env (rho 6)) start (Source.SetLanguage.nonemptyFamily 0 1)) :
    ∃ out, (Project.FirstOrderSemantics.reduct M).mem out (env (rho 6)) ∧
      MapRel (orderFormula (rho 0) mul) env out start ∧ ∃ graph,
        ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) graph ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph checkedX family)
          (env (rho 6)) out (Source.SetLanguage.choiceForFamily 0 1 2) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  let W := env (rho 6)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hLarge : ¬ Small (env I) (env mu) := fun h => hI.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    ((ForcingSupportSize.native_small hM _ _).mp h)
  obtain ⟨idMu,hIdMu⟩ := ZF.exists_inclusionInjection hZF pair (fun _ h => h :
    (Project.FirstOrderSemantics.reduct M).MemberSubset (env mu) (env mu))
  have hMuI := (hI.2 (env mu) hMu.1.1).mpr ⟨idMu,hIdMu⟩
  obtain ⟨muToI,hMuToI⟩ := ZF.exists_inclusionInjection hZF pair
    (fun x hx => hI.1.transitive (env mu) hMuI x hx)
  obtain ⟨toMu,hToMu⟩ := (ForcingSupportSize.native_small hM _ _).mp hD
  obtain ⟨root,hRoot⟩ := ZF.exists_compositionInjection hZF pair hToMu hMuToI
  have hRoot' := (ForcingSupportSize.native_injection hM _ _ root).mpr hRoot
  obtain ⟨d,s,z,hDcond,hS,hZ,hZStart⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hRoot' hStart
  have hZW := ForcingSupportingRoot.code_mem hPres hDcond hS hZ
  have hZStart' := (orderFormula_semantics env (rho 0) mul z start).mpr hZStart
  obtain ⟨stabilizer,hStabilizer,hStabilizerF⟩ := ForcingHS.symmetric_of_hs hFamily
  obtain ⟨_,J,HJ,hJI,hJSmall,hFixJ,hIncluded⟩ := (hFilter stabilizer).mp hStabilizerF
  have hFamilyJ : Supported v7 HJ family := by
    intro pi hpi act hAct
    obtain ⟨a,ha,hFixed⟩ := ((hStabilizer pi).mp (hIncluded pi hpi)).2
    have eq := ForcingProductFamily.unique hM ((mapRel_action _ _ _).mp ha) ((mapRel_action _ _ _).mp hAct)
    exact eq ▸ hFixed
  obtain ⟨V,hV,hVI,hVSmall⟩ := ConstructionCohenCompatibility.exists_support hM hw hPres.1 hPres.2.1 hDcond
  have hVSmallMu : Small V (env mu) := by
    obtain ⟨toW,hToW⟩ := (ForcingSupportSize.native_small hM _ _).mp hVSmall
    obtain ⟨omegaToMu,hOmegaToMu⟩ := hMu.2
    exact (ForcingSupportSize.native_small hM _ _).mpr (ZF.exists_compositionInjection hZF pair hToW hOmegaToMu)
  obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) J V
  have hUI : (Project.FirstOrderSemantics.reduct M).MemberSubset U (env I) :=
    fun x hx => ((hU x).mp hx).elim (hJI x) (hVI x)
  have hUSmall : Small U (env mu) := (ForcingSupportSize.native_small hM _ _).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
      ((ForcingSupportSize.native_small hM _ _).mp hJSmall) ((ForcingSupportSize.native_small hM _ _).mp hVSmallMu) hU)
  obtain ⟨p,hp,hPs,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hS hUI hUSmall
  obtain ⟨empty,hEmpty⟩ := ForcingWithTopCarrier.exists_empty hM
  obtain ⟨q,hq,hQp,_⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 (env mark) hMark) hp (fun x hx => (hEmpty x hx).elim) (ForcingSupportSize.small_empty hM (env mu) hEmpty)
  have hqp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) q p := ⟨env mark,hMark,hQp⟩
  have hps : ForcingDiagramOrder.Le (env (rho 0)) (env mul) p s := ⟨env mark,hMark,hPs⟩
  obtain ⟨Jp,hJp,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hp hD
  obtain ⟨Hp,hHp⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Jp
  obtain ⟨Jq,hJq,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hD
  obtain ⟨Hq,hHq⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Jq
  have hFamilyP : Supported v7 Hp family := ForcingSupportedNames.supported_mono hFixJ hHp
    (fun x hx => (hJp x).mpr (hCover x ((hU x).mpr (Or.inl hx)))) hFamilyJ
  have hDq : ForcingLocalRecordPullback.Supported (env (rho 0)) q d := by
    intro i coordinate bit he
    have hiV := (hV i).mpr ⟨coordinate,bit,he⟩
    exact ConstructionDescentPlacement.range_antitone hqp (hCover i ((hU i).mpr (Or.inr hiV)))
  obtain ⟨zp,hZp⟩ := ForcingSupportingRoot.exists_code hM d p
  obtain ⟨zq,hZq⟩ := ForcingSupportingRoot.exists_code hM d q
  have hZpW := ForcingSupportingRoot.code_mem hPres hDcond hp hZp
  have hZqW := ForcingSupportingRoot.code_mem hPres hDcond hq hZq
  have hZpz := (orderFormula_semantics env (rho 0) mul zp z).mpr
    ((ForcingSupportingRoot.code_le hZp hZ).mpr ⟨fun _ h => h,hps⟩)
  have hZpStart := hpre.2 zp z start hZpW hZW hStart hZpz hZStart'
  have hZqp := (orderFormula_semantics env (rho 0) mul zq zp).mpr
    ((ForcingSupportingRoot.code_le hZq hZp).mpr ⟨fun _ h => h,hqp⟩)
  have hZqStart := hpre.2 zq zp start hZqW hZpW hStart hZqp hZpStart
  let other : Fin (k+12) → M.Carrier .set := Fin.cases zq (Fin.cases zp (Fin.cases Hq (Fin.cases Jq
    (Fin.cases Hp (Fin.cases Jp (Fin.cases q (Fin.cases p (Fin.cases d (Fin.cases X (Fin.cases checkedX (Fin.cases family env)))))))))))
  let up : Fin k → Fin (k+12) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let ra : Fin 7 → Fin (k+12) := fun j => up (rho j)
  have hR (a b : M.Carrier .set) : MapRel R env a b ↔ MapRel (orderFormula (ra 0) (up mul)) other a b := by
    simp only [R,orderFormula_semantics,ra,up,other,Fin.cases_succ]
  have hH (a : M.Carrier .set) : ForcingClassEvaluation.Predicate Hdom env a ↔
      ForcingClassEvaluation.Predicate (domain ra (up G) (up F)) other a := by
    rw [domain_semantics,domain_semantics]
    rfl
  have hInput := ForcingFormula.mono hM hpre _ _ hStart hZpW hZpStart hf
  have hInput' := (ForcingSeparation.force_congr hR hH _ (args2 family checkedX) W zp).mp hInput
  obtain ⟨graph,hGraphHS,_,hForce⟩ := ForcingGroundFamilyChoice.ground_family_choice hM hChoice other ra
    (up w) (up mu) (up history) (up kappa) (up unit) (up mark) (up H) (up C) (up incoming) (up base)
    (up I) (up K) (up B) (up G) (up F) (up mul) (up index) 7 6 8 5 4 3 2 1 (up top) 9 10 11 0
    hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hQp hJp hHp hJq hHq
    hFamilyP hDcond hDq hZp ht hChecked hZq hInput'
  exact ⟨zq,hZqW,hZqStart,graph,hGraphHS,(ForcingSeparation.force_congr hR hH _ (args3 graph checkedX family) W zq).mpr hForce⟩

theorem dense_choice (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index : Fin k)
    (top : Fin k)
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
 : ForcingOrdinalChoice.DenseChoice (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) := by
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  let W := env (rho 6)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTopLe : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hCheck : ∀ x nx, Checked (env top) x nx → ForcingClassEvaluation.Predicate Hdom env nx := by
    intro x nx hnx
    apply (domain_semantics env rho G F nx).mpr
    apply ForcingHSCheck.check_hs hM actionFormula v7 (env G) W (env F) (env top) hNormal.1 htW ?_ x nx hnx
    intro pi hpi
    obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hPres ((hG pi).mp hpi)
    exact ⟨act,(mapRel_action v7 pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
      Or.inl ⟨htW,ForcingProductFamily.top_fixed hPres ht ha⟩⟩
  intro p hp eta hEta family hFamily ho hf
  obtain ⟨rank,hRank⟩ := ForcingRawRank.exists_rank hM eta
  obtain ⟨q,hq,hqp,beta,_,_,checkedBeta,hCheckedBeta,hEq⟩ := ForcingOrdinalDecision.forces_ordinal_decide hM
    hpre htW hTopLe (fun x => domain_semantics env rho G F x) hCheck (args1 eta) 0 hEta hp hRank ho p hp (hpre.1 p hp)
  have hInput : Force R Hdom env (args2 family checkedBeta) W q (Source.SetLanguage.nonemptyFamily 0 1) := by
    apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.nonemptyFamily 0 1)
      (args2 family eta) (args2 family checkedBeta) q hq ?_).mp (ForcingFormula.mono hM hpre _ _ hp hq hqp hf)
    intro j
    exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre family q hq) (Fin.cases hEq (fun x => Fin.elim0 x)) j
  obtain ⟨out,hOut,hOutQ,graph,hGraph,hForce⟩ := ground_family_choice_dense hM hChoice env rho
    w mu history kappa unit mark H C incoming base I K B G F mul index top
    hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex ht hCheckedBeta
    ((domain_semantics env rho G F family).mp hFamily) hq hInput
  refine ⟨out,hOut,hpre.2 out q p hOut hq hp hOutQ hqp,graph,(domain_semantics env rho G F graph).mpr hGraph,?_⟩
  apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.choiceForFamily 0 1 2)
    (args3 graph checkedBeta family) (args3 graph eta family) out hOut ?_).mp hForce
  intro j
  exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre graph out hOut)
    (Fin.cases (ForcingAtomicBasic.eq_symm hM (ForcingAtomicBasic.eq_mono hM hpre hOut hOutQ hEq))
      (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre family out hOut) (fun x => Fin.elim0 x))) j

theorem forces_ACwo (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index : Fin k)
    (top : Fin k)
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
    (p : M.Carrier .set) (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env Fin.elim0 (env (rho 6)) p Source.SetLanguage.ACwo := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  exact ForcingOrdinalChoice.forces_ACwo_of_dense hM hpre
    (dense_choice hM hChoice env rho w mu history kappa unit mark H C incoming base I K B G F mul index top
      hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex ht) hp

/-- The SAME actual forty-set Core. The probe index is saturation mu=13;
Cohen kappa remains the separate slot14. No supplied system or dense oracle. -/
theorem on_core (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) (env : Fin 40 → M.Carrier .set)
    (hCore : ForcingConcreteSystem.Core hM env) :
    ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env 33) →
      Force (orderFormula (ForcingConcreteSystem.forcingRho 0) 18) (domain ForcingConcreteSystem.forcingRho 34 35)
        env Fin.elim0 (env 33) p Source.SetLanguage.ACwo := by
  have hProbes := ForcingRootProbes.on_core hM env hCore
  obtain ⟨_,hm,_,hPres,hG,hFilter,hw,hMu,hI,hD,hMergers,hRow,_,ht,_,_,_,hMark,hCard,_⟩ := hCore
  intro p hp
  exact forces_ACwo hM hChoice env ForcingConcreteSystem.forcingRho
    39 13 16 14 19 20 21 22 23 24 27 14 3 34 35 18 13 1
    hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes.1 hProbes.2 ht p hp

/-- Full original ACwo, at EVERY internal condition of the SAME actual system. -/
def outcomeFormula : Project.Formula 1 40 :=
  ForcingOrdinalChoice.allACwo (orderFormula (ForcingConcreteSystem.forcingRho 0) 18)
    (domain ForcingConcreteSystem.forcingRho 34 35) id 33

theorem outcomeFormula_freeClosed : outcomeFormula.FreeClosed := by
  simp -implicitDefEqProofs [outcomeFormula,ForcingOrdinalChoice.allACwo,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem outcomeFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF)
    (env : Env (Project.FirstOrderSemantics.reduct M) 40) :
    Project.Formula.satisfies env outcomeFormula ↔
      ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env.bound 33) →
        Force (orderFormula (ForcingConcreteSystem.forcingRho 0) 18) (domain ForcingConcreteSystem.forcingRho 34 35)
          env.bound Fin.elim0 (env.bound 33) p Source.SetLanguage.ACwo :=
  ForcingOrdinalChoice.allACwo_semantics hM env _ _ id 33

def sentence : Project.Sentence where
  formula := .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj ForcingConcreteSystem.coreFormula (.conj ForcingConcreteSystem.outcomeFormula (.conj ForcingNonwellorderableImage.imageOutcomeFormula (.conj ForcingChoiceFailure.outcomeFormula (.conj ForcingRootProbes.outcomeFormula outcomeFormula)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ForcingConcreteSystem.coreFormula_freeClosed,ForcingConcreteSystem.outcomeFormula_freeClosed,ForcingNonwellorderableImage.imageOutcomeFormula_freeClosed,ForcingChoiceFailure.outcomeFormula_freeClosed,ForcingRootProbes.outcomeFormula_freeClosed,outcomeFormula_freeClosed]

theorem models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence sentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  change Project.Formula.satisfies ({bound := Fin.elim0,free := free} :
    SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0) sentence.formula
  obtain ⟨w,hw⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome⟩ := ForcingConcreteSystem.construct hM hOrder hChoice hw
  have hImages := ForcingNonwellorderableImage.on_core hM _ hCore hOutcome
  have hNotChoice := ForcingChoiceFailure.on_core hM hChoice _ hCore
  have hProbes := ForcingRootProbes.on_core hM _ hCore
  have hACwo := on_core hM hChoice _ hCore
  simp only [sentence,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingConcreteSystem.coreFormula_semantics hM,ForcingConcreteSystem.outcomeFormula_semantics hM,ForcingNonwellorderableImage.imageOutcomeFormula_semantics hM,ForcingChoiceFailure.outcomeFormula_semantics hM,ForcingRootProbes.outcomeFormula_semantics hM,outcomeFormula_semantics hM]
  exact ⟨w,bound,labels,labelMap,F,G,W,Product,Y,X,CS,CC,I,outerF,P,base,incoming,C,H,mark,one,mul,D,history,stageBound,K,mu,continuum,Power,groundTop,u,seedC,seedH,values,Q,three,B,high,zero,seedMul,hCore,hOutcome,hImages,hNotChoice,hProbes,hACwo⟩

theorem kernel_certificate :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sentence))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => witness }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sentence)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sentence)).mp
      (models hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ForcingActualOrdinalChoice
