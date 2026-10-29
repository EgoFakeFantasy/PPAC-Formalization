/- Pinned CodeCardinals.ordinalType_lower_count:212-236.
The SAME actual outside copy supplies stable profiles and persistent working codes
at every stronger internal condition. No supplied stable conclusion or System. -/
import PPAC.Migration.ForcingStableCodes
import PPAC.Migration.ForcingOutsideCopies
import PPAC.Migration.ForcingClassProfile

namespace PPAC.Migration.ForcingProbeStable
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

theorem stable_of_copy (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau : Fin k)
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
    (f : M.Carrier .set) (hf : (Project.FirstOrderSemantics.reduct M).mem f (env (rho 3)))
    (hdf : ForcingPowerName.Subset (env d) f) :
    ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
      (env mul) (env bound) f (env r) (env a) (env tau) (env U) := by
  obtain ⟨d',tau',Am,Hm,z,hRecord',hd,_,_,hAm,hHm,hLocal,hz,hClass,hOutside⟩ := hCopy
  obtain ⟨ed,etau⟩ := PureKuratowski.code_injective hRecord hRecord'
  subst d'
  subst tau'
  obtain ⟨g,hg⟩ := ForcingPrincipalFilter.exists_principal hM (env (rho 3)) f
  have hgf := ForcingPrincipalFilter.principal_filter hf hg
  have hdg := (hg (env d)).mpr ⟨(hp.2.2.1 (env d)).mpr hd,hdf⟩
  obtain ⟨oi,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family_over hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (Fin.lastCases g env)
    Fin.castSucc (fun j => (rho j).castSucc) G.castSucc F.castSucc mul.castSucc (Fin.last k)
    q.castSucc bound.castSucc labels.castSucc E.castSucc I.castSucc (rho 4).castSucc
    (by simpa only [Fin.lastCases_castSucc] using hp.2.2.2.1)
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last] at hObjMap hObj
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM env (rho 0) mul (rho 4)
  obtain ⟨mi,maps,hMap,hMaps⟩ := ForcingEligibleMapFamily.exists_family_at_filter hM env rho G F mul
    I K B w one q bound labels E g S hm hp hgf hS
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hgf hq hAq hHq hE hObj hS hMaps
  obtain ⟨Or,hr,_⟩ := hObjMap.1.2 (env r) ((hp.2.2.2.1 (env r)).mpr hrI)
  obtain ⟨OP,hP,_⟩ := hObjMap.1.2 (env p) ((hp.2.2.2.1 (env p)).mpr hpI)
  obtain ⟨Om,hSm,_⟩ := hObjMap.1.2 (env sm) ((hp.2.2.2.1 (env sm)).mpr hsmI)
  obtain ⟨Ar,Hr,XR,QR,prR,hDR⟩ := ((hObj (env r) Or).mp hr).2
  obtain ⟨Ap',Hp',XP',QP,prP,hDP⟩ := ((hObj (env p) OP).mp hP).2
  obtain ⟨Am',Hm',XM,QM,prM,hDM⟩ := ((hObj (env sm) Om).mp hSm).2
  have eAp := (ModelTransfer.extensionality hM).eq_of_same_members (env Ap) Ap' (fun x => (hAp x).trans (hDP.1 x).symm)
  subst Ap'
  have eHp := ForcingLabelPermutations.fixing_unique hM hHp hDP.2.1
  subst Hp'
  have eXP := (ModelTransfer.extensionality hM).eq_of_same_members (env XP) XP' (fun x => (hXP x).trans (hDP.2.2.1 x).symm)
  subst XP'
  have eAm := (ModelTransfer.extensionality hM).eq_of_same_members Am Am' (fun x => (hAm x).trans (hDM.1 x).symm)
  subst Am'
  have eHm := ForcingLabelPermutations.fixing_unique hM hHm hDM.2.1
  subst Hm'
  have hel : ForcingEligibility.EligibleName (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (env (rho 6)) g (env sm) (env labels) (env E) (env tau) :=
    ⟨env d,z,hdg,hz,hClass z (ForcingSupportingRoot.code_mem hp hd hsmI hz)⟩
  obtain ⟨xr,hxr,hpr,hProfile⟩ := ForcingClassProfile.construct hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hgf
    hObjMap hObj hS hMap hMaps hSys hr hP hSm hDP hDM hDR hq ha he hmD hb hae hmb hSuba hSubm hSubp
    hLocal hel hEnum hList hdg hz hOutside hGeom
  intro n
  constructor
  · intro hnU
    obtain ⟨hn,hna,hAvail⟩ := (hProfile n).mp hnU
    exact ⟨hn,hna,(ForcingForcedAvailability.actual_available_iff hM hChoice env rho G F mul
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE
      hf hg hObjMap hObj hS hMap hMaps hSys hr hDR hSuba hpr hxr hn hna).mp hAvail⟩
  · rintro ⟨hn,hna,hAvail⟩
    exact (hProfile n).mpr ⟨hn,hna,(ForcingForcedAvailability.actual_available_iff hM hChoice env rho G F mul
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE
      hf hg hObjMap hObj hS hMap hMaps hSys hr hDR hSuba hpr hxr hn hna).mpr hAvail⟩

/-- Source hel/stable and the first total producer: an actual persistent code,
with every entry equal to the SAME copied name, at any stronger input condition. -/
theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z : Fin k)
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
    (hz : ForcingSupportingRoot.Code (env z) (env f) (env r)) :
    (∀ g, (Project.FirstOrderSemantics.reduct M).mem g (env (rho 3)) → ForcingPowerName.Subset (env d) g →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) g (env r) (env a) (env tau) (env U)) ∧
    ∃ code, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code ∧
      ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env f) code ∧
      ∀ i sigma, PureKuratowski.PairMember M i sigma code →
        EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env f) (env r) sigma (env tau) := by
  have hStable := stable_of_copy hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hrI hpI hsmI hAp hHp hXP ha he hmD hb hae hmb hSuba hSubm hSubp hEnum hList hCopy hRecord hGeom
  refine ⟨hStable,?_⟩
  obtain ⟨d',tau',Am,Hm,z',hRecord',_,_,_,hAm,hHm,hLocal,_,hClass,_⟩ := hCopy
  obtain ⟨ed,etau⟩ := PureKuratowski.code_injective hRecord hRecord'
  subst d'
  subst tau'
  have hRange : ForcingPowerName.Subset Am (env Ar) := fun x hx => (hAr x).mpr
    (ConstructionDescentPlacement.range_antitone ⟨env m,hmD,hSubm⟩ ((hAm x).mp hx))
  have hTau : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env Hr) (env tau) :=
    ⟨hLocal.1,ForcingSupportedNames.supported_mono hHm hHr hRange hLocal.2⟩
  exact ForcingStableCodes.exists_working_code_of_stable hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
    zero root vertices chain names r a U Ar Hr f tau z
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
    hzero hNames hChain hRoot hAr hHr hTau hf hz
    (hClass (env z) (ForcingSupportingRoot.code_mem hp ((hp.2.2.1 (env f)).mp hf) hrI hz))
    (fun g hg hfg => hStable g hg (fun x hx => hfg x (hdf x hx)))

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
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
    (.conj (.forallE (.imp (.mem (.bound 0) (.bound (rho 3).succ))
      (.imp (Project.Formula.subset (.bound d.succ) (.bound 0))
        (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ a.succ tau.succ U.succ))))
    (.existsE (.conj
      (ForcingTailCodes.chainCode (fun j => (rho j).succ) G.succ F.succ bound.succ w.succ names.succ chain.succ 0)
      (.conj (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.succ (fun j => (rho j).succ)
        I.succ G.succ F.succ mul.succ q.succ bound.succ labels.succ E.succ root.succ w.succ chain.succ f.succ 0)
        (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))
          (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) up (up (rho 6)) (up f) (up r) 0 (up tau)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingForcedAvailability.carrier_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingPersistentWorks.works_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,
      ForcingOutsideCopies.copyRecord_freeClosed,ForcingClassProfile.geometry_freeClosed]


theorem source_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_subset_iff,
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
    ForcingForcedAvailability.carrier_semantics hM,
    ForcingTailCodes.chainCode_semantics hM,ForcingPersistentWorks.works_semantics hM,
    KuratowskiZF.source_edge,ForcingPrincipalFilter.eqF_semantics hM,
    ForcingLocalNames.carrier_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    Project.Formula.satisfies_isBijectionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ForcingCollectedName.collected_semantics (M := M),ForcingOutsideCopies.copyRecord_semantics hM,
    KuratowskiZF.source_code,ForcingClassProfile.geometry_semantics hM]
  exact source_construct hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z))) := by
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
  apply ConstructibleGround.relative_models hM (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (sourceSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z)).mp
      (source_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq r a U p sm e m b t Ap Hp XP ordinal enum list J delta record d tau f zero root vertices chain names Ar Hr z hL hChoice)


end PPAC.Migration.ForcingProbeStable
