/- Pinned CodeLinks.links_stable:313-345. Use the SAME literal linked name
at every stronger internal condition; exact fibers and eligibility are existing. -/
import PPAC.Migration.ForcingForcedAvailability
import PPAC.Migration.ForcingCodeLinkRepresentation

namespace PPAC.Migration.ForcingLinkedStability
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

/-- Same existing stability proof, accepting internally constructed conditions and names. -/
theorem links_stable_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
      zero root vertices chain names vertex r index U : Fin k) (d tau z a : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
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
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hc : Code (env vertex) (env r) (env index) (env U))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hz : ForcingSupportingRoot.Code z d (env r))
    (ha : ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) a)
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) tau)
    (hWorks : ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) d a)
    (hLinks : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) d (env vertex) tau a) :
    ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 tau (env labels) (env E)) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2) ∧
    ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset d e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env index) tau (env U) := by
  have hCommon := ForcingCodeLinks.links_common hM env rho mul hw hChain hLinks
  have hVertex : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env r) (env index) (env U) := by
    obtain ⟨_,_,_,r',index',U',_,hc',_,hv,_⟩ := hCommon
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
    exact hv
  have hall e (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)))
      (hde : ForcingPowerName.Subset d e) ze (hze : ForcingSupportingRoot.Code ze e (env r)) :
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (Source.SetLanguage.args3 tau (env labels) (env E)) (env (rho 6)) ze (ForcingEligibility.isClass 0 1 2) ∧
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env index) tau (env U) := by
    obtain ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hb,hRep⟩ := hWorks e he hde
    obtain ⟨hObjMap,hObj,hS,hMap,hMaps,hP,hGlue,hQ,hProjection⟩ := hBundle
    have hgf := ForcingPrincipalFilter.principal_filter he hg
    have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hgf hq hAq hHq hE hObj hS hMaps
    have hCoh := ForcingComponentFibers.coherent_of_system hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys (q := env q)
    obtain ⟨hAll,hComm⟩ := ForcingComponentGluing.gluing_laws hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys hP hGlue hQ hProjection
    have hAt := ForcingCodeLinkRepresentation.at_of_represents_links hM (ForcingPairUnion.domain rho G F) env rho mul
      hm hp hp.2.2.2.1 hObjMap hObj hMaps hCoh hAll hComm hw hChain he hg ha.1 hEntry hRep
      (ForcingCodeLinks.links_mono hM env rho mul hm hp he hde hLinks)
    obtain ⟨r',index',U',Ar,Hr,Xr,Qr,pr,Or,V,x,p,_,hc',hDr,hr,hV,hx,htx,_,_⟩ := hAt
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
    have hxO := ((hV x).mp hx).1
    have hActual := ((hV x).mp hx).2
    have hel := (ForcingEligibility.eligible_ofName hM env rho G F mul hm hp hgf hVertex.1 hDr.2.2.2.2.2.1 htx).mp
      ((hDr.2.2.2.2.2.2 x).mp hxO).2.2
    obtain ⟨f,zf,hfg,hzf,hforce⟩ := hel
    have hfg' := (hg f).mp hfg
    have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
    have hzfW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 f).mp hfg'.1) hVertex.1 hzf
    have hzeW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 e).mp he) hVertex.1 hze
    have hle := (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul ze zf).mpr
      ((ForcingSupportingRoot.code_le hze hzf).mpr ⟨hfg'.2,ForcingDiagramPoset.le_refl hm hVertex.1⟩)
    refine ⟨ForcingFormula.mono hM hpre (ForcingEligibility.isClass 0 1 2)
      (Source.SetLanguage.args3 tau (env labels) (env E)) hzfW hzeW hle hforce,?_⟩
    intro n
    rw [hActual n]
    apply and_congr_right
    intro hn
    apply and_congr_right
    intro hni
    exact ForcingForcedAvailability.actual_available_iff hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hp hG hF
      hLabelMap hTop hLabels hq hAq hHq hE he hg hObjMap hObj hS hMap hMaps hSys hr hDr hVertex.2.1 htx hxO hn hni
  refine ⟨(hall d hd (fun _ h => h) z hz).1,?_⟩
  intro e he hde
  obtain ⟨ze,hze⟩ := ForcingSupportingRoot.exists_code hM e (env r)
  exact (hall e he hde ze hze).2

theorem links_stable_over (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
      zero root vertices chain names vertex r index U d tau z : Fin k) (a : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
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
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hc : Code (env vertex) (env r) (env index) (env U))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env r))
    (ha : ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) a)
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hWorks : ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env d) a)
    (hLinks : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env vertex) (env tau) a) :
    ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) (env z) (ForcingEligibility.isClass 0 1 2) ∧
    ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset (env d) e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env index) (env tau) (env U) :=
  links_stable_at hM hChoice env rho
    w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
    zero root vertices chain names vertex r index U (env d) (env tau) (env z) a
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE
    hChain hc hd hz ha hEntry hWorks hLinks

/-- Retained indexed entry point; accepts the same original parameters. -/
theorem links_stable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
      zero root vertices chain names vertex r index U d tau z a : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
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
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hc : Code (env vertex) (env r) (env index) (env U))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env r))
    (ha : ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env a))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hWorks : ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env d) (env a))
    (hLinks : ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env vertex) (env tau) (env a)) :
    ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) (env z) (ForcingEligibility.isClass 0 1 2) ∧
    ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset (env d) e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env index) (env tau) (env U) :=
  links_stable_over hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z (env a)
    hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hChain hc hd hz ha hEntry hWorks hLinks

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
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
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code vertex r index U)
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d r))
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho I G F mul q bound labels E root w chain d a)
    (.imp (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau a)
    (.conj (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (Source.SetLanguage.args3 tau labels E) (rho 6) z (ForcingEligibility.isClass 0 1 2))) (.forallE (.imp (.mem (.bound 0) (.bound (rho 3).succ)) (.imp (Project.Formula.subset (.bound d.succ) (.bound 0)) (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ index.succ tau.succ U.succ))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingTailCodes.entry_freeClosed,ForcingPersistentWorks.works_freeClosed,
      ForcingCodeLinks.links_freeClosed,ForcingForcedAvailability.carrier_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOmega_iff,
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
    ForcingSupportedNames.supported_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCarrier.code_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingTailCodes.chainCode_semantics hM,ForcingTailCodes.entry_semantics hM,ForcingPersistentWorks.works_semantics hM,
    ForcingCodeLinks.links_semantics hM,ForcingFormula.formula_semantics (M := M),ForcingForcedAvailability.carrier_semantics hM]
  exact links_stable hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a)).mp
      (construction_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z a hL hChoice)

end PPAC.Migration.ForcingLinkedStability
