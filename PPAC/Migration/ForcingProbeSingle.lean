/- Pinned CodeCardinals.ordinalType_lower_count.single:254-283.
Equal ordinal witnesses at compatible conditions force the same selected code.
Existing Links and Outside exclusion rule out independent actual probe copies. -/
import PPAC.Migration.ForcingProbeTotal

namespace PPAC.Migration.ForcingProbeSingle
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedArrow EncodedCommon)
open ForcingTailCodes (ChainCode At Entry Represents)
open ForcingPrincipalFilter (EqF)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem incompatible_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p t b Ap Hp XP ordinal enum list J delta : Fin k)
    (s0 s1 m0 m1 rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1 : M.Carrier .set)
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
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hs0I : Injection (env (rho 0)) (env I) s0)
    (hs1I : Injection (env (rho 0)) (env I) s1)
    (hm0 : (Project.FirstOrderSemantics.reduct M).mem m0 (env (rho 0)))
    (hm1 : (Project.FirstOrderSemantics.reduct M).mem m1 (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hSub0 : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) m0 s0)
    (hSub1 : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) m1 s1)
    (hSubP : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hSub0P : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s0 (env b) (env p))
    (hSub1P : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) s1 (env b) (env p))
    (hCones : ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m0 m1 (env t))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hCopy0 : ForcingOutsideCopies.Copy (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) s0 rec0)
    (hRec0 : PureKuratowski.Code M rec0 d0 tau0)
    (hCopy1 : ForcingOutsideCopies.Copy (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) s1 rec1)
    (hRec1 : PureKuratowski.Code M rec1 d1 tau1)
    (hD0f : ForcingPowerName.Subset d0 f)
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hc0 : (Project.FirstOrderSemantics.reduct M).mem c0 (env codes))
    (hc1 : (Project.FirstOrderSemantics.reduct M).mem c1 (env codes))
    (hRank0 : PureKuratowski.PairMember M c0 rn0 (env ranks))
    (hRank1 : PureKuratowski.PairMember M c1 rn1 (env ranks))
    (hSel0 : ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order c0 f)
    (hSel1 : ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order c1 g)
    (hLinks0 : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) f (env root) tau0 c0)
    (hLinks1 : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) g (env root) tau1 c1)
    (hCheck0 : ForcingCheckName.Checked (env top) beta nb0)
    (hCheck1 : ForcingCheckName.Checked (env top) beta nb1)
    (hEq0 : EqF (orderFormula (rho 0) mul) env (env (rho 6)) f (env r) rn0 nb0)
    (hEq1 : EqF (orderFormula (rho 0) mul) env (env (rho 6)) g (env r) rn1 nb1) :
    ¬ ∃ c, (Project.FirstOrderSemantics.reduct M).mem c (env (rho 3)) ∧
      ForcingPowerName.Subset f c ∧ ForcingPowerName.Subset g c := by
  rintro ⟨c,hc,hfc,hgc⟩
  have hEq0c := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hc hrI hfc hEq0
  have hEq1c := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp hc hrI hgc hEq1
  have hCheckEq := ForcingCheckName.unique hM hCheck0 hCheck1
  rw [← hCheckEq] at hEq1c
  obtain ⟨z,hz,hRankEq⟩ := ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hc hrI
    hEq0c (ForcingPrincipalFilter.eqF_symm hM hEq1c)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have htP := (hp.2.2.2.2.2 (env top)).mpr (Or.inl hTop)
  have htop : ∀ v, (Project.FirstOrderSemantics.reduct M).mem v (env (rho 6)) →
      ForcingMapConditions.MapRel (orderFormula (rho 0) mul) env v (env top) :=
    fun v _ => (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul v (env top)).mpr (Or.inl hTop)
  have hdomain := fun name => ForcingPairUnion.domain_semantics env rho G F name
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hcheck : ∀ x nx, ForcingCheckName.Checked (env top) x nx →
      ForcingClassEvaluation.Predicate (ForcingPairUnion.domain rho G F) env nx := by
    intro x nx hn
    exact (hdomain nx).mpr (ForcingInfinity.check_hs hM (fun j => env (rho j)) hp hG hNormal hTop hn)
  let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
  have hRa := (ForcingCohenSelection.mapRel_lift R id env (rho 0) I (rho 2) w c0 z).mpr
    ((ForcingCohenSelection.lift_coe ((hp.2.2.1 c).mp hc) hrI hz).mpr
      ((ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order c0 c).mpr
        (ForcingCodeSelection.isSelected_mono hfc hSel0)))
  have hRb := (ForcingCohenSelection.mapRel_lift R id env (rho 0) I (rho 2) w c1 z).mpr
    ((ForcingCohenSelection.lift_coe ((hp.2.2.1 c).mp hc) hrI hz).mpr
      ((ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order c1 c).mpr
        (ForcingCodeSelection.isSelected_mono hgc hSel1)))
  have hCodes := (ForcingOrdinalCoding.selectedRank_eq_iff hM hpre htP htop hdomain hcheck hOrder hRanks
    hc0 hc1 hRank0 hRank1 ((hdomain rn0).mpr (hFamily c0 hc0 rn0 hRank0).1)
    ((hdomain rn1).mpr (hFamily c1 hc1 rn1 hRank1).1)
    (ForcingSupportingRoot.code_mem hp ((hp.2.2.1 c).mp hc) hrI hz) hRa hRb).mp hRankEq
  have hL0 := ForcingCodeLinks.links_mono hM env rho mul hm hp hc hfc hLinks0
  have hL1 := ForcingCodeLinks.links_mono hM env rho mul hm hp hc hgc hLinks1
  rw [← hCodes] at hL1
  have hCode0 := (hCarrier c0).mp hc0
  have hSame := ForcingPersistentCodes.same_refl hM env rho mul hm hp hw hChain hCode0.1 hc
  have hNamesEq := (ForcingCodeLinks.links_eq_iff_same hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hChain hc hRoot hCode0 hCode0 hL0 hL1).mpr hSame
  obtain ⟨d0',tau0',A0,H0,z0,hRec0',hd0,_,_,hA0,hH0,hn0,hz0,_,hout0⟩ := hCopy0
  obtain ⟨ed0,et0⟩ := PureKuratowski.code_injective hRec0 hRec0'
  subst d0'; subst tau0'
  obtain ⟨d1',tau1',A1,H1,z1,hRec1',_,_,_,hA1,hH1,hn1,_,_,_⟩ := hCopy1
  obtain ⟨ed1,et1⟩ := PureKuratowski.code_injective hRec1 hRec1'
  subst d1'; subst tau1'
  obtain ⟨filter,hFilter⟩ := ForcingPrincipalFilter.exists_principal hM (env (rho 3)) c
  have hgf := ForcingPrincipalFilter.principal_filter hc hFilter
  have hd0g := (hFilter d0).mpr ⟨(hp.2.2.1 d0).mpr hd0,fun x hx => hfc x (hD0f x hx)⟩
  have hInter := ConstructionDiagramPlacements.range_inter_sub hrI hSub0 hSub1 hSubP hCones
  exact ForcingClassProfile.outside_not_eqG_common hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hpI hs0I hs1I hrI
    ⟨env b,hb,hSub0P⟩ ⟨env b,hb,hSub1P⟩ hInter ⟨m0,hm0,hSub0⟩ ⟨m1,hm1,hSub1⟩
    hA0 hA1 hAp hH0 hH1 hHp hn0 hn1 hLabelMap hTop hLabels hLabelBound hgf hXP hEnum hList hd0g hz0 hout0
    ((ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hc hrI hFilter).mpr hNamesEq)

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1 : Fin k)
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
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hs0I : Injection (env (rho 0)) (env I) (env s0))
    (hs1I : Injection (env (rho 0)) (env I) (env s1))
    (hm0 : (Project.FirstOrderSemantics.reduct M).mem (env m0) (env (rho 0)))
    (hm1 : (Project.FirstOrderSemantics.reduct M).mem (env m1) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hSub0 : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env m0) (env s0))
    (hSub1 : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env m1) (env s1))
    (hSubP : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hSub0P : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s0) (env b) (env p))
    (hSub1P : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s1) (env b) (env p))
    (hCones : ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) (env m0) (env m1) (env t))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hCopy0 : ForcingOutsideCopies.Copy (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env s0) (env rec0))
    (hRec0 : PureKuratowski.Code M (env rec0) (env d0) (env tau0))
    (hCopy1 : ForcingOutsideCopies.Copy (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env s1) (env rec1))
    (hRec1 : PureKuratowski.Code M (env rec1) (env d1) (env tau1))
    (hD0f : ForcingPowerName.Subset (env d0) (env f))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hc0 : (Project.FirstOrderSemantics.reduct M).mem (env c0) (env codes))
    (hc1 : (Project.FirstOrderSemantics.reduct M).mem (env c1) (env codes))
    (hRank0 : PureKuratowski.PairMember M (env c0) (env rn0) (env ranks))
    (hRank1 : PureKuratowski.PairMember M (env c1) (env rn1) (env ranks))
    (hSel0 : ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order (env c0) (env f))
    (hSel1 : ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order (env c1) (env g))
    (hLinks0 : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env f) (env root) (env tau0) (env c0))
    (hLinks1 : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env g) (env root) (env tau1) (env c1))
    (hCheck0 : ForcingCheckName.Checked (env top) (env beta) (env nb0))
    (hCheck1 : ForcingCheckName.Checked (env top) (env beta) (env nb1))
    (hEq0 : EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env f) (env r) (env rn0) (env nb0))
    (hEq1 : EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env g) (env r) (env rn1) (env nb1)) :
    ¬ ∃ c, (Project.FirstOrderSemantics.reduct M).mem c (env (rho 3)) ∧
      ForcingPowerName.Subset (env f) c ∧ ForcingPowerName.Subset (env g) c := by
  exact incompatible_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p t b Ap Hp XP ordinal enum list J delta (env s0) (env s1) (env m0) (env m1) (env rec0) (env rec1) (env d0) (env tau0) (env d1) (env tau1) (env f) (env g) (env c0) (env c1) (env rn0) (env rn1) (env beta) (env nb0) (env nb1) hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hrI hpI hs0I hs1I hm0 hm1 hb hSub0 hSub1 hSubP hSub0P hSub1P hCones hAp hHp hXP hEnum hList hCopy0 hRec0 hCopy1 hRec1 hD0f hChain hRoot hCarrier hOrder hRanks hFamily hc0 hc1 hRank0 hRank1 hSel0 hSel1 hLinks0 hLinks1 hCheck0 hCheck1 hEq0 hEq1

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1 : Fin k) : Project.Sentence where
  formula :=
    let R := ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order
    let L := ForcingCohenSelection.liftRelation R id (rho 0) I (rho 2) w
    Project.Formula.forallClosure k
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
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s0 (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s1 (rho 0) I))
    (.imp (.mem (.bound m0) (.bound (rho 0)))
    (.imp (.mem (.bound m1) (.bound (rho 0)))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r m0 s0))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r m1 s1))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s0 b p))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s1 b p))
    (.imp (ConstructionDiagramPlacements.coneEquality (rho 0) mul m0 m1 t)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap Hp))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hp XP))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ForcingOutsideCopies.copyRecord (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F w bound labels E J delta list s0 rec0)
    (.imp (ProjectSyntax.encode id (PairSyntax.ordered rec0 d0 tau0))
    (.imp (ForcingOutsideCopies.copyRecord (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F w bound labels E J delta list s1 rec1)
    (.imp (ProjectSyntax.encode id (PairSyntax.ordered rec1 d1 tau1))
    (.imp (Project.Formula.subset (.bound d0) (.bound f))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r a U)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (.mem (.bound c0) (.bound codes))
    (.imp (.mem (.bound c1) (.bound codes))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ranks c0 rn0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ranks c1 rn1))
    (.imp (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order id c0 f)
    (.imp (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order id c1 g)
    (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain f root tau0 c0)
    (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain g root tau1 c1)
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top beta nb0))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top beta nb1))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) f r rn0 nb0)
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) g r rn1 nb1)
    (.neg (.existsE (.conj (.mem (.bound 0) (.bound (rho 3).succ))
      (.conj (Project.Formula.subset (.bound f.succ) (.bound 0))
        (Project.Formula.subset (.bound g.succ) (.bound 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionDiagramPlacements.coneEquality_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
      ForcingOutsideCopies.copyRecord_freeClosed,ForcingCodeSelection.selected_freeClosed,
      ForcingCodeLinks.links_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1 : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ConstructionDiagramPlacements.coneEquality_semantics hM,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingLocalNames.carrier_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingOutsideCopies.copyRecord_semantics hM,KuratowskiZF.source_code,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingTailCodes.carrier_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),KuratowskiZF.source_edge,
    ForcingCodeSelection.selected_semantics hM,ForcingCodeLinks.links_semantics hM,
    ForcingCheckName.checkName_semantics (M := M),ForcingPrincipalFilter.eqF_semantics hM]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1 : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q zero root vertices chain names codes order ranks group r a U p s0 s1 m0 m1 t b Ap Hp XP ordinal enum list J delta rec0 rec1 d0 tau0 d1 tau1 f g c0 c1 rn0 rn1 beta nb0 nb1 hL hChoice)




end PPAC.Migration.ForcingProbeSingle
