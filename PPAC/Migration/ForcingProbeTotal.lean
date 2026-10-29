/- Pinned CodeCardinals.ordinalType_lower_count.total:233-253.
Consume actual outside-copy work codes, the EXISTING dense selector and rank
decision. Preserve the SAME copy name through selected-code Links. -/
import PPAC.Migration.ForcingProbeStable
import PPAC.Migration.ForcingGermDensity

namespace PPAC.Migration.ForcingProbeTotal
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

theorem witness_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta : Fin k)
    (sm m record d tau f z : M.Carrier .set)
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
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hsmI : Injection (env (rho 0)) (env I) sm)
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hmb : ForcingDiagramOrder.Product (env mul) m (env b) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubm : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) m sm)
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hCopy : ForcingOutsideCopies.Copy (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) sm record)
    (hRecord : PureKuratowski.Code M record d tau)
    (hGeom : ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) m (env t) (env U))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hf : (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)))
    (hdf : ForcingPowerName.Subset d f)
    (hz : ForcingSupportingRoot.Code z f (env r))
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
    (hChecked : ForcingCheckName.Checked (env top) (env theta) (env ntheta))
    (hTheta : EqF (orderFormula (rho 0) mul) env (env (rho 6)) f (env r) (env selection) (env ntheta)) :
    ∃ g beta selected rankName nbeta,
      (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) ∧
      ForcingPowerName.Subset f g ∧ ForcingPowerName.Subset d g ∧
      ForcingRawRank.Ordinal beta ∧ (Project.FirstOrderSemantics.reduct M).mem beta (env theta) ∧
      (Project.FirstOrderSemantics.reduct M).mem selected (env codes) ∧
      PureKuratowski.PairMember M selected rankName (env ranks) ∧ ForcingCheckName.Checked (env top) beta nbeta ∧
      ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order selected g ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) g (env root) tau selected ∧
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) g (env r) rankName nbeta := by
  obtain ⟨_,code,hCode,hWorks,hEntries⟩ := ForcingProbeStable.working_at hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr sm m record d tau f z
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hsmI hAp hHp hXP ha he hmD hb hae hmb hSuba hSubm hSubp hEnum hList hCopy hRecord hGeom hJ hzero hNames hChain hRoot hAr hHr hf hdf hz
  have hLinks : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w)
      (env (rho 0)) (env I) (env mul) (env q) (env chain) f (env root) tau code := by
    have hzW := ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1
    refine ⟨env r,env a,env U,hRoot,env zero,hzW,?_⟩
    intro i hi hzi
    obtain ⟨vertex,hv,_⟩ := hChain.1.1.2 i hi
    obtain ⟨sigma,hs,_⟩ := hCode.1.1.2 i hi
    obtain ⟨n,hn⟩ := hChain.2.2.1 (env zero) i (env root) vertex hzi hChain.2.1 hv
    exact ⟨vertex,sigma,n,hv,hs,hn,hEntries i sigma hs⟩
  obtain ⟨e',he',hfe,selected,hSelected,hSel,hSame⟩ := ForcingGermDensity.existing_dense_selected hM env rho
    I K B w one G F mul q bound labels E root zero vertices chain names codes order
    f code hm hp hw hChain hCarrier hOrder hf ((hCarrier code).mpr hCode) hWorks
  have hSelectedLinks := ForcingCodeLinks.links_same hM env rho mul hm hp hw hChain he' hCode.1
    (ForcingCodeLinks.links_mono hM env rho mul hm hp he' hfe hLinks) hSame
  have hThetaE := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he' hrI hfe hTheta
  obtain ⟨ze,hze,hTypeEq⟩ := hThetaE
  obtain ⟨rankName,hRankName,_⟩ := hRanks.1.2 selected hSelected
  have hRa := (ForcingCodeSelection.mapRel_relation hM env rho I G F mul q bound labels E root w chain codes order selected e').mpr hSel
  obtain ⟨g,zg,beta,nbeta,hg,heg,hzg,hBeta,hBetaTheta,hNbeta,hRankEq⟩ :=
    ForcingCohenRankConsumers.rank_decide hM hChoice env rho G F mul I w
      (ForcingCodeSelection.relation rho I G F mul q bound labels E root w chain codes order) id
      hw hMu hI hSmall hMergers hRow hm hp hG hF hrI hAr hHr hTop hOrder hRanks hSelection hFamily hIncl
      ((hp.2.2.1 e').mp he') hze hSelected hRankName hRa hChecked hTypeEq
  have hgP := (hp.2.2.1 g).mpr hg
  exact ⟨g,beta,selected,rankName,nbeta,hgP,(fun x hx => heg x (hfe x hx)),
    (fun x hx => heg x (hfe x (hdf x hx))),hBeta,hBetaTheta,hSelected,hRankName,hNbeta,
    ForcingCodeSelection.isSelected_mono heg hSel,
    ForcingCodeLinks.links_mono hM env rho mul hm hp hgP heg hSelectedLinks,⟨zg,hzg,hRankEq⟩⟩

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta : Fin k)
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
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hAq : ForcingSupportedNames.Range (env (rho 0)) (env q) (env Aq))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env Aq) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hrI : Injection (env (rho 0)) (env I) (env r))
    (hpI : Injection (env (rho 0)) (env I) (env p))
    (hsmI : Injection (env (rho 0)) (env I) (env sm))
    (hAp : ForcingSupportedNames.Range (env (rho 0)) (env p) (env Ap))
    (hHp : ForcingLabelPermutations.Fixing (env G) (env Ap) (env Hp))
    (hXP : ForcingLocalNames.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env Hp) (env XP))
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env (rho 0)))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 0)))
    (hmD : (Project.FirstOrderSemantics.reduct M).mem (env m) (env (rho 0)))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hae : ForcingDiagramOrder.Product (env mul) (env a) (env e) (env t))
    (hmb : ForcingDiagramOrder.Product (env mul) (env m) (env b) (env t))
    (hSuba : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env a) (env q))
    (hSubm : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env m) (env sm))
    (hSubp : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env t) (env p))
    (hEnum : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) (env enum) (env ordinal) (env XP))
    (hList : ForcingCollectedName.Collected ForcingPowerName.trueTest Fin.elim0 (env ordinal) (env enum) (env (rho 6)) (env list))
    (hCopy : ForcingOutsideCopies.Copy (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env sm) (env record))
    (hRecord : PureKuratowski.Code M (env record) (env d) (env tau))
    (hGeom : ForcingClassProfile.Geometry (env (rho 0)) (env mul) (env a) (env m) (env t) (env U))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hf : (Project.FirstOrderSemantics.reduct M).mem (env f) (env (rho 3)))
    (hdf : ForcingPowerName.Subset (env d) (env f))
    (hz : ForcingSupportingRoot.Code (env z) (env f) (env r))
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
    (hChecked : ForcingCheckName.Checked (env top) (env theta) (env ntheta))
    (hTheta : EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env f) (env r) (env selection) (env ntheta)) :
    ∃ g beta selected rankName nbeta,
      (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) ∧
      ForcingPowerName.Subset (env f) g ∧ ForcingPowerName.Subset (env d) g ∧
      ForcingRawRank.Ordinal beta ∧ (Project.FirstOrderSemantics.reduct M).mem beta (env theta) ∧
      (Project.FirstOrderSemantics.reduct M).mem selected (env codes) ∧
      PureKuratowski.PairMember M selected rankName (env ranks) ∧ ForcingCheckName.Checked (env top) beta nbeta ∧
      ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order selected g ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) g (env root) (env tau) selected ∧
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) g (env r) rankName nbeta := by
  exact witness_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p e b t Ap Hp XP ordinal enum list J delta zero root vertices chain names Ar Hr codes order ranks selection group theta ntheta (env sm) (env m) (env record) (env d) (env tau) (env f) (env z) hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hsmI hAp hHp hXP ha he hmD hb hae hmb hSuba hSubm hSubp hEnum hList hCopy hRecord hGeom hJ hzero hNames hChain hRoot hAr hHr hf hdf hz hCarrier hOrder hRanks hSelection hFamily hIncl hChecked hTheta

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+5) := fun j => j.succ.succ.succ.succ.succ
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
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection sm (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Ap))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ap Hp))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.carrier rho G F bound Hp XP))
    (.imp (.mem (.bound a) (.bound (rho 0)))
    (.imp (.mem (.bound e) (.bound (rho 0)))
    (.imp (.mem (.bound m) (.bound (rho 0)))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul a e t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul m b t))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r a q))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r m sm))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r t p))
    (.imp (Project.Formula.isBijectionFromTo PureKuratowskiProject.convention (.bound enum) (.bound ordinal) (.bound XP))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected ForcingPowerName.trueTest Fin.elim0 ordinal enum (rho 6) list))
    (.imp (ForcingOutsideCopies.copyRecord (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F w bound labels E J delta list sm record)
    (.imp (ProjectSyntax.encode id (PairSyntax.ordered record d tau))
    (.imp (ForcingClassProfile.geometry (rho 0) mul a m t U)
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero))
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r a U)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (.mem (.bound f) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound f))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z f r))
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound codes))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalRanks.ranks L id codes order (rho 6) ranks))
    (.imp (ProjectSyntax.encode id (ForcingCollectedName.collected L id codes ranks (rho 6) selection))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (Project.Formula.subset (.bound Hr) (.bound group))
    (.imp (ProjectSyntax.encode id (ForcingCheckName.checkName top theta ntheta))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) f r selection ntheta)
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4) (.bound (up (rho 3))))
      (.conj (Project.Formula.subset (.bound (up f)) (.bound 4))
      (.conj (Project.Formula.subset (.bound (up d)) (.bound 4))
      (.conj (ProjectSyntax.encode id (OrdinalSyntax.ordinal 3))
      (.conj (.mem (.bound 3) (.bound (up theta)))
      (.conj (.mem (.bound 2) (.bound (up codes)))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up ranks) 2 1))
      (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName (up top) 3 0))
      (.conj (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order up 2 4)
      (.conj (ForcingCodeLinks.links (orderFormula (rho 0) mul) up (up (rho 6)) (up w) (up (rho 0)) (up I) (up mul) (up q) (up chain) 4 (up root) (up tau) 2)
      (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) up (up (rho 6)) 4 (up r) 1 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,
      ForcingOutsideCopies.copyRecord_freeClosed,ForcingClassProfile.geometry_freeClosed,
      ForcingTailCodes.carrier_freeClosed,Project.Formula.isSetCodedWellOrder_freeClosed,
      ForcingCodeSelection.selected_freeClosed,ForcingCodeLinks.links_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_isOmega_iff,
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
    ForcingSupportingRoot.code_semantics (M := M),
    KuratowskiZF.source_edge,ForcingPrincipalFilter.eqF_semantics hM,
    ForcingLocalNames.carrier_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingOutsideCopies.copyRecord_semantics hM,
    KuratowskiZF.source_code,ForcingClassProfile.geometry_semantics hM,
    ForcingTailCodes.carrier_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingCheckName.checkName_semantics (M := M),ForcingRawRank.ordinal_semantics (M := M),
    ForcingCodeSelection.selected_semantics hM,ForcingCodeLinks.links_semantics hM]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta))) := by
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
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z codes order ranks selection group theta ntheta hL hChoice)



end PPAC.Migration.ForcingProbeTotal
