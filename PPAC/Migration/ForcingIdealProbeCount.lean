/- Pinned ConcreteQuotients.code_ordinalType_cardinal: consume actual ideal
probes and outsideClass_copies before applying the full internal OrdinalCount. -/
import PPAC.Migration.ForcingConcreteOrdinalCount
import PPAC.Migration.ConstructionIdealProbes
import PPAC.Migration.ForcingLocalList

namespace PPAC.Migration.ForcingIdealProbeCount
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

/-- Reindex the existing internal ideal probes by the actual square of mu.
The native composition graph preserves the edges needed by outsideClass_copies. -/
theorem square_multipliers (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu P D mul one mark a b t U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hP : ForcingCohenCoordinates.Cartesian mu mu P)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D)
    (hU : ConstructionIdealProbes.ConeIdeal D mul a U)
    (ht : ForcingDiagramOrder.Product mul a mark t)
    (hProbes : ConstructionIdealProbes.IdealProbes mu D mul mark a b U) :
    ∃ multipliers, MapsTo P D multipliers ∧
      (∀ i m, PureKuratowski.PairMember M i m multipliers → ForcingDiagramOrder.Product mul m b t) ∧
      (∀ i m, PureKuratowski.PairMember M i m multipliers → ForcingClassProfile.Geometry D mul a m t U) ∧
      (∀ i j m n, PureKuratowski.PairMember M i m multipliers → PureKuratowski.PairMember M j n multipliers →
        i ≠ j → ConstructionDiagramPlacements.ConeEquality D mul m n t) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF pair mu
  obtain ⟨index,hIndex⟩ := ExistingCardinalBounds.infinite_product_l pair hZF hw hMu ⟨id,hId.1⟩ ⟨id,hId.1⟩ hP
  obtain ⟨probes,hProbes,hProfiles,hIndependent⟩ := hProbes
  obtain ⟨multipliers,hMuls,hEdge⟩ := ZF.exists_compositionFunction hZF pair hIndex.1
    ((ForcingSupportSize.native_mapsTo hM _ _ _).mp hProbes.1)
  have exit_eq {exit} (hExit : ForcingDiagramOrder.Product mul a mark exit) : exit = t :=
    (hm.2.1 a hU.2.1).2.1 mark exit t hmark hExit ht
  refine ⟨multipliers,(ForcingSupportSize.native_mapsTo hM _ _ _).mpr hMuls,?_,?_,?_⟩
  · intro i m him
    obtain ⟨_,k,_,hkm⟩ := (hEdge i m).mp him
    obtain ⟨exit,_,hExit,hProduct,_⟩ := hProfiles k m hkm
    exact exit_eq hExit ▸ hProduct
  · intro i m him
    obtain ⟨_,k,_,hkm⟩ := (hEdge i m).mp him
    obtain ⟨exit,_,hExit,_,_,hDiv,hJoin⟩ := hProfiles k m hkm
    have eq := exit_eq hExit
    subst exit
    refine ⟨fun x => ⟨fun hx => ⟨hU.1 x hx,(hDiv x (hU.1 x hx)).mpr hx⟩,
      fun hx => (hDiv x hx.1).mp hx.2⟩,hJoin⟩
  · intro i j m n him hjn hij
    obtain ⟨_,k,hik,hkm⟩ := (hEdge i m).mp him
    obtain ⟨_,l,hjl,hln⟩ := (hEdge j n).mp hjn
    have hkl : k ≠ l := by
      intro eq
      subst l
      exact hij (hIndex.2 i j k hik hjl)
    obtain ⟨exit,hExit,hJoin⟩ := hIndependent k l m n hkm hln hkl
    exact exit_eq hExit ▸ hJoin

/-- Apply the existing collected-name fixedness proof to the SAME supplied
local-name enumeration, without choosing a second list. -/
theorem local_list_fixed (hM : FirstOrder.Theory.Models M nativeZF)
    (v : Fin 7 → M.Carrier .set) {I K B w mu G F bound r A H X ordinal enum list : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hp : ForcingProductFamily.Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingSupportFilter.Filter I G mu F)
    (hr : Injection (v 0) I r) (hSmall : ForcingSupportSize.Small (v 0) mu)
    (hRange : ForcingSupportedNames.Range (v 0) r A) (hFix : ForcingLabelPermutations.Fixing G A H)
    (hX : ForcingLocalNames.Carrier v G F bound H X)
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) enum ordinal X)
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (v 6) list) :
    ForcingOrdinalFixed.Fixed v G F H list := by
  obtain ⟨A',hA',hAI,hASmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hr hSmall
  have hAA := ForcingCohenOrderAction.image_unique hM hRange hA'
  subst A'
  have hGroup := ForcingConjugationGraph.fixing_subgroup hM hG hFix hAI
  have hHF := (hF H).mpr ⟨hGroup,A,H,hAI,hASmall,hFix,fun _ h => h⟩
  have hFamily : ForcingOrdinalFixed.FixedFamily v G F H ordinal enum := by
    intro i hi name hin
    have hn := (hX name).mp (hEnum.1.1.output_mem_of_pairMember hin)
    exact ⟨hn.1.1,hn.2⟩
  exact ForcingOrdinalFixed.collected_fixed hM ForcingPowerName.trueTest Fin.elim0 v hp hG
    (ForcingNormalFilter.is_normal hM hw hMu hG hF) hGroup hHF hFamily
    (fun _ _ _ _ _ _ _ _ _ _ _ => fun h => h) hList

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {k : Nat}
    (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k)
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
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env mark) (env t))
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
    (hP : ForcingCohenCoordinates.Cartesian (env mu) (env mu) (env P))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hmark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hEHS : ForcingHS.HS ForcingProductFamily.actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env E))
    (hCoord : ForcingCohenCoordinates.Cartesian (env (rho 0)) (env K) (env coordS))
    (hLocal : ForcingCohenCoordinates.Cartesian (env coordS) (env B) (env localS))
    (hK : (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) (env K) (env mu))
    (hParameters : ConstructionConcreteCardinals.Parameters hM (env w) (env Power) (env continuum) (env mu))
    (hLabelCard : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) (env labelSet) (env mu))
    (hAllIdeals : ConstructionIdealProbes.AllIdeals (env mu) (env history) (env kappa))
    (hbNe : env b ≠ env one)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env Hp) (env E))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env b) (env p))
    (hd : ForcingCohenConditions.Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : ConstructionCohenCompatibility.Restricted (env Ap) (env d) (env delta))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env s))
    (hj : ConstructionPlacementTriple.ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : ForcingRelationClassMove.Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env labelMap) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : ForcingOutsideLocal.Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list)) :
    ForcingGermDensity.OrdinalCount hM env rho mul w top selection r labelSet (env delta) := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hIdeal := (ForcingTailGroup.root_vertex hChain hRoot).2.2
  have hProbes := hAllIdeals (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base)
    (env a) (env b) (env U) hRow hb hbNe hIdeal
  obtain ⟨multipliers,hMultipliers,hProducts,hGeometry,hIndependent⟩ := square_multipliers hM hw hMu hP hm hmark hIdeal hae hProbes
  have hLarge : ¬ ForcingSupportSize.Small (env I) (env mu) := by
    intro h
    exact hI.not_cardinalLessOrEqual (ZF.modelsKP hZF) ((ForcingSupportSize.native_small hM _ _).mp h)
  have hFixed := local_list_fixed hM (fun i => env (rho i)) hw hMu hp hG hF hpI hSmall hAp hHp hXP hEnum hList
  obtain ⟨targets,copies,hTargets,hCopies⟩ := ForcingOutsideCopies.source_family_at hM hChoice env rho
    G F mul I K B w mu one labelMap top bit labels E j sigma bound Ap Hp list s p b d delta z P r t multipliers
    hp hG hF hw hMu hLarge hSmall hm hLabelMap hTop hLabels hLabelBound hEHS hAp hHp hEf hFixed hs hb hSub hd hSupp hRestr hz hj hSigma hOut hrI hpI hSubp hMultipliers hProducts
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF pair (env mu)
  have hA : ¬ ForcingSupportSize.Small (env mu) (env w) := by
    intro h
    obtain ⟨f,hf⟩ := (ForcingSupportSize.native_small hM _ _).mp h
    obtain ⟨g,hg⟩ := hParameters.2.2.1.2
    exact hParameters.2.2.2.2.1.not_cardinalLessOrEqual (ZF.modelsKP hZF)
      (ZF.exists_compositionInjection hZF pair hf hg)
  exact ForcingConcreteOrdinalCount.count_with_family hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p mark b t Ap Hp XP ordinal enum list Ap delta zero root vertices chain names Ar Hr codes order ranks selection group mu P Power continuum coordS localS labelSet targets copies multipliers
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hAp hHp hXP ha hmark hb hae hSuba hSubp hEnum hList hJ hzero hNames hChain hRoot hAr hHr hCarrier hOrder hRanks hSelection hFamily hIncl hTwo hP hA hCopies hTargets hMultipliers hProducts hGeometry hIndependent hAp hVertices hCard hmark hEHS hCoord hLocal hK hParameters ⟨id,hId⟩ hLabelCard

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k) : Project.Sentence where
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
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a mark t))
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
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian mu mu P))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (.mem (.bound mark) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs ForcingProductFamily.actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (rho 0) K coordS))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coordS B localS))
    (.imp (Project.Formula.cardinalLessOrEqual PureKuratowskiProject.convention (.bound K) (.bound mu))
    (.imp (ConstructionConcreteCardinals.parameters w Power continuum mu)
    (.imp (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound labelSet) (.bound mu))
    (.imp (ConstructionIdealProbes.allIdeals mu history kappa)
    (.imp (.neg (Project.Formula.extensionalEq (.bound b) (.bound one)))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hp E))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b p))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d)
    (.imp (ConstructionCohenCompatibility.restricted Ap d delta)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
    (.imp (ConstructionPlacementTriple.imageAt s (rho 0) j)
    (.imp (ProjectSyntax.encode id (ForcingRelationClassMove.value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F I K labelMap top bit labels E j sigma))
    (.imp (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
    (ForcingGermDensity.ordinalCount rho mul w top selection r labelSet id delta)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
      
      ForcingProductParameters.two_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionSaturationCardinals.cardinalsF_freeClosed,
      ConstructionConcreteCardinals.parameters_freeClosed,ForcingGermDensity.ordinalCount_freeClosed,ConstructionIdealProbes.allIdeals_freeClosed,
      Project.Formula.extensionalEq,ForcingLocalRecordPullback.supported_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed,ConstructionPlacementTriple.imageAt_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
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
    ForcingLocalNames.carrier_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),
    ForcingTailCodes.carrier_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    
    ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingProductParameters.two_semantics (M := M),
    ConstructionComponentCarrier.carrier_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ForcingHS.hs_semantics (M := M),ConstructionConcreteCardinals.parameters_semantics hM,
    Project.Formula.satisfies_cardinalLessOrEqual_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingGermDensity.ordinalCount_semantics hM,
    ConstructionIdealProbes.allIdeals_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ConstructionCohenCompatibility.restricted_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ConstructionPlacementTriple.imageAt_semantics hM,ForcingRelationClassMove.value_semantics (M := M),
    ForcingOutsideLocal.outside_semantics (M := M)]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z))) := by
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
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p b t Ap Hp XP ordinal enum list delta zero root vertices chain names Ar Hr codes order ranks selection group P Power continuum coordS localS labelSet s j sigma d z hL hChoice)

end PPAC.Migration.ForcingIdealProbeCount
