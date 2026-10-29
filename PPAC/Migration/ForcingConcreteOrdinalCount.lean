/- Pinned ConcreteQuotients.code_ordinalType_cardinal and the OrdinalCount
consumer in GermSelectors. Reuse both actual counts and native Hartogs arithmetic. -/
import PPAC.Migration.ForcingProbeRows
import PPAC.Migration.ForcingCodeCardinals

namespace PPAC.Migration.ForcingConcreteOrdinalCount
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo Injection)
open ForcingPrincipalFilter (EqF)
open ConstructionComponentCofinal (Chain)
open ConstructionComponentCarrier (Code)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The source final contradiction: a Hartogs successor cannot fit in a
product of two sets bounded by its predecessor. All injections are internal. -/
theorem lower_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w Power continuum mu A theta Power' nu W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hPower : (Project.FirstOrderSemantics.reduct M).IsPowerSetOf Power w)
    (hContinuum : (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) continuum Power)
    (hInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w continuum)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) mu continuum)
    (hA : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) A mu)
    (hTheta : (Project.FirstOrderSemantics.reduct M).IsOrdinal theta)
    (hPower' : (Project.FirstOrderSemantics.reduct M).IsPowerSetOf Power' w)
    (hNu : (Project.FirstOrderSemantics.reduct M).IsCardinalOf (KuratowskiZF.interpretation hM) nu Power')
    (hW : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) W theta nu)
    (hCount : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) A W) :
    (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) mu theta := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  let pair := KuratowskiZF.interpretation hM
  have hPowerEq := hZF.1.eq_of_same_members Power' Power (fun x => (hPower' x).trans (hPower x).symm)
  subst Power'
  have hNuEq := hNu.eq hZF pair hContinuum
  subst nu
  rcases Structure.IsOrdinal.trichotomy hZF.1 hMu.1 hTheta
      (KP.difference_exists_d hKP) (KP.intersection_exists_d hKP mu theta) with he | hmt | htm
  · have heq := hZF.1.eq_of_same_members mu theta he
    subst theta
    obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF pair mu
    exact ⟨id,hId.1⟩
  · exact ZF.exists_inclusionInjection hZF pair (hTheta.transitive.memberSubset hmt)
  · have hSmall := (hMu.2 theta hTheta).mp htm
    obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF pair continuum
    obtain ⟨p,hp⟩ := ExistingCardinalBounds.infinite_product_l pair hZF hw hInfinite hSmall ⟨id,hId.1⟩ hW
    obtain ⟨a,ha⟩ := hA.symm hZF pair
    obtain ⟨b,hb⟩ := hCount
    obtain ⟨ab,hab⟩ := ZF.exists_compositionInjection hZF pair ha.1 hb
    exact False.elim (hMu.not_cardinalLessOrEqual hKP (ZF.exists_compositionInjection hZF pair hab hp))

theorem count_with_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P Power continuum coordS localS labelSet : Fin k)
    (targets copies multipliers : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hIncl : ForcingPowerName.Subset (env Hr) (env group))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hP : ForcingCohenCoordinates.Cartesian (env A) (env A) (env P))
    (hA : ¬ ForcingSupportSize.Small (env A) (env w))
    (hCopies : ForcingOutsideCopies.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env P) targets copies)
    (hTargets : ForcingOutsideCopies.Targets (env (rho 0)) (env I) (env mul) (env r) (env b) (env p) (env P) multipliers targets)
    (hMultipliers : MapsTo (env P) (env (rho 0)) multipliers)
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m multipliers → ForcingDiagramOrder.Product (env mul) m (env b) (env t))
    (hGeometry : ∀ i m, PureKuratowski.PairMember M i m multipliers → ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) m (env t) (env U))
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m multipliers → PureKuratowski.PairMember M j n multipliers →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n (env t))
    (hRangeJ : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS))
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hIndexCard : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env A) (env mu))
    (hLabelCard : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env labelSet) (env mu)) :
    ForcingGermDensity.OrdinalCount hM env rho mul w top selection r labelSet (env delta) := by
  intro f hf hdf theta ntheta htheta hntheta hEq
  obtain ⟨_,Power',nu,W,_,hPower',hNu,hW,hLower⟩ := ForcingProbeRows.count_with_family hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers
    theta ntheta f
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI
    hAp hHp hXP ha he hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hAr hHr ((hp.2.2.1 f).mpr hf)
    hCarrier hOrder hRanks hSelection hFamily hIncl hntheta hEq hTwo hP hA hCopies hTargets hMultipliers hProducts hGeometry hIndependent hRangeJ hdf
  obtain ⟨hPower,hContinuum,hInfinite,_,hHartogs,_,_,hMuPow,_⟩ := hParameters
  have hMuTheta := lower_bound hM hw hPower hContinuum hInfinite hHartogs hIndexCard
    (ForcingGermDensity.ordinal_native htheta) hPower' hNu hW hLower
  obtain ⟨z,hz,hForce⟩ := hEq
  have hUpper := ForcingCodeCardinals.cardinal_le_at hM hChoice (ConstructionDirectedCardinality.models_zfc hM hChoice) env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U coordS localS codes order Ar Hr group ranks selection
    f z theta ntheta
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
    hVertices hChain hf hRoot hCard hmark hEHS hCoord hLocal hCarrier hAr hHr hIncl hFamily hSelection hz hntheta hForce
    hOrder hRanks.1 hMuPow hK hTwo
  exact hLabelCard.trans (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (ZF.equinumerous_of_cardinalLessOrEqual (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hMuTheta hUpper)

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) (env order) (env codes))
    (hRanks : ForcingOrdinalRanks.Ranks
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env order) (env (rho 6)) (env ranks))
    (hSelection : ForcingCollectedName.Collected
      (ForcingCohenSelection.liftRelation (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id (rho 0) I (rho 2) w)
      env (env codes) (env ranks) (env (rho 6)) (env selection))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hIncl : ForcingPowerName.Subset (env Hr) (env group))
    (hTwo : ∃ o, (Project.FirstOrderSemantics.reduct M).IsOrdinalOne o ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf (env B) o)
    (hP : ForcingCohenCoordinates.Cartesian (env A) (env A) (env P))
    (hA : ¬ ForcingSupportSize.Small (env A) (env w))
    (hCopies : ForcingOutsideCopies.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env P) (env targets) (env copies))
    (hTargets : ForcingOutsideCopies.Targets (env (rho 0)) (env I) (env mul) (env r) (env b) (env p) (env P) (env multipliers) (env targets))
    (hMultipliers : MapsTo (env P) (env (rho 0)) (env multipliers))
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) → ForcingDiagramOrder.Product (env mul) m (env b) (env t))
    (hGeometry : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) → ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) m (env t) (env U))
    (hIndependent : ∀ i j m n, PureKuratowski.PairMember M i m (env multipliers) → PureKuratowski.PairMember M j n (env multipliers) →
      i ≠ j → ConstructionDiagramPlacements.ConeEquality (env (rho 0)) (env mul) m n (env t))
    (hRangeJ : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS))
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hIndexCard : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env A) (env mu))
    (hLabelCard : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env labelSet) (env mu)) :
    ForcingGermDensity.OrdinalCount hM env rho mul w top selection r labelSet (env delta) := by
  exact count_with_family hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P Power continuum coordS localS labelSet (env targets) (env copies) (env multipliers) hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hAp hHp hXP ha he hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hAr hHr hCarrier hOrder hRanks hSelection hFamily hIncl hTwo hP hA hCopies hTargets hMultipliers hProducts hGeometry hIndependent hRangeJ hVertices hCard hmark hEHS hCoord hLocal hK hParameters hIndexCard hLabelCard

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet : Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap Hp))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hp XP))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (.mem (.bound e) (.bound (rho 0)))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a e t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero))
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r a U)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (Project.Formula.subset (.bound Hr) (.bound group))
    (.imp (ForcingProductParameters.two B)
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian A A P))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small A w)))
    (.imp (ForcingOutsideCopies.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F w bound labels E J delta list P targets copies)
    (.imp (ForcingOutsideCopies.targets (rho 0) I mul r b p P multipliers targets)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo multipliers P (rho 0)))
    (.imp (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ 0 b.succ.succ t.succ.succ)))))
    (.imp (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0)) (ForcingClassProfile.geometry (rho 0).succ.succ mul.succ.succ a.succ.succ 0 t.succ.succ U.succ.succ))))
    (.imp (ForcingProbeRowHits.independent (rho 0) mul t multipliers)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p J))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (.mem (.bound mark) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 0) K coordS))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coordS B localS))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound K) (.bound mu))
    (.imp (ConstructionConcreteCardinals.parameters w Power continuum mu)
    (.imp (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound A) (.bound mu))
    (.imp (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound labelSet) (.bound mu))
    (ForcingGermDensity.ordinalCount rho mul w top selection r labelSet id delta)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingClassProfile.geometry_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
      ForcingOutsideCopies.family_freeClosed,ForcingOutsideCopies.targets_freeClosed,
      ForcingProbeRowHits.independent_freeClosed,ForcingProductParameters.two_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed,
      ConstructionConcreteCardinals.parameters_freeClosed,ForcingGermDensity.ordinalCount_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingTailCodes.candidates_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    KuratowskiZF.source_edge,ForcingLocalNames.carrier_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingClassProfile.geometry_semantics hM,
    ForcingTailCodes.carrier_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOutsideCopies.family_semantics hM,ForcingOutsideCopies.targets_semantics hM,
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingProbeRowHits.independent_semantics hM,ForcingProductParameters.two_semantics (M := M),
    ConstructionComponentCarrier.carrier_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingHS.hs_semantics (M := M),ConstructionConcreteCardinals.parameters_semantics hM,
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingGermDensity.ordinalCount_semantics hM]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet))) := by
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
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group A P targets copies multipliers Power continuum coordS localS labelSet hL hChoice)

end PPAC.Migration.ForcingConcreteOrdinalCount
