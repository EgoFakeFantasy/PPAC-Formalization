/- Pinned PersistentCodes.works_covariance:238-264. Construct both actual
principal presentations, Systems, app family and glued bijection at each condition.
The System proof uses the existing internal-L Choice route, never new ZF Choice. -/
import PPAC.Migration.ForcingPersistentCovariance

namespace PPAC.Migration.ForcingWorksCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingSupportSize (MapsTo)
open ForcingPersistentWorks (Bundle Represented Works)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem represented_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names : Fin k) (code : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hpiHq : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hFix : ForcingConditionGraphs.CompositionGraph (env (rho 0)) (env pi) (env q) (env q))
    (hRoot : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) (env root) (env rootT))
    (hStab : ConstructionComponentCofinal.EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env rootT))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCode : ForcingTailCodes.ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code)
    (hTail : ForcingTailCovariance.TailFixes (env w) (env (rho 0)) (env pi) (env chain))
    {ac d dT : M.Carrier .set}
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) ac)
    (hdd : PureKuratowski.PairMember M d dT ac) :
    Represented (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) dT code ↔
      Represented (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) d code := by
  have hDataCopy := hData
  obtain ⟨hp,hG,hpi,_,_,_,_,_,_,hFilter⟩ := hDataCopy
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hPowerBound := (ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound
  have hac := ForcingLocalTransport.part_permutation hc
  have hd := ForcingConditionGraphs.function_input hac.1.1 hdd
  have hdT := hac.1.2 d dT hdd
  have ho : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨f,t,_,_,ht,_,_,hGraph⟩ := hc
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  obtain ⟨g,oi,objects,S,mi,maps,P,Q,pr,hg,hB⟩ := ForcingPersistentWorks.assemble_principal hM env rho
    I K B w one G F mul q bound labels E root hm hp hd
  obtain ⟨gT,oiT,targets,ST,miT,targetMaps,PT,Z,prT,hgT,hBT⟩ := ForcingPersistentWorks.assemble_principal hM env rho
    I K B w one G F mul q bound labels E root hm hp hdT
  have hST : ST = S := (ModelTransfer.extensionality hM).eq_of_same_members ST S
    (fun z => (hBT.2.2.1 z).trans (hB.2.2.1 z).symm)
  subst ST
  have hgf := ForcingPrincipalFilter.principal_filter hd hg
  have hgTf := ForcingPrincipalFilter.principal_filter hdT hgT
  have hImage := ForcingPrincipalFilter.principal_move hac ho hdd hg hgT
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
    hw hMu hI hSmallD hMergers hRow hm hp hG hFilter hLabelMap hTop hLabels hLabelBound
    hgf hq hA hHq hE hB.2.1 hB.2.2.1 hB.2.2.2.2.1
  have hTSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
    hw hMu hI hSmallD hMergers hRow hm hp hG hFilter hLabelMap hTop hLabels hLabelBound
    hgTf hq hA hHq hE hBT.2.1 hBT.2.2.1 hBT.2.2.2.2.1
  have hAppExists : ∃ image apps, MapsTo (env (rho 4)) image apps ∧
      ForcingEligibleReindex.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
        env (fun j => env (rho j)) (env G) (env F) (env mul) g gT (env q) (env bound)
        (env labels) (env E) (env pi) (env act) apps := by
    have ht := fun r hr => ForcingEligibleReindex.exists_row hM env rho G F mul act hm hData hw hSmall hNormal
      hLabelMap hTop hLabels hPowerBound hc hgf hImage hq hA hHq hpiHq hE (r := r) hr
    simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using
      (ForcingEligibleReindex.exists_family_over (M := M) hM (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
        (Fin.lastCases gT (Fin.lastCases g env)) (fun j => j.castSucc.castSucc) (fun j => (rho j).castSucc.castSucc)
        G.castSucc.castSucc F.castSucc.castSucc mul.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))
        q.castSucc.castSucc bound.castSucc.castSucc labels.castSucc.castSucc E.castSucc.castSucc pi.castSucc.castSucc act.castSucc.castSucc
        (by simpa only [Fin.lastCases_castSucc] using hp.2.2.2.1)
        (by
          intro r hr
          have hr' : (Project.FirstOrderSemantics.reduct M).mem r (env (rho 4)) := by
            simpa only [Fin.lastCases_castSucc] using hr
          simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using ht r hr'))
  obtain ⟨appImage,apps,hAppMap,hFamily⟩ := hAppExists
  have hApps := ForcingEligibleReindex.apps_of_family hM hp.2.2.2.1 hB.2.1 hBT.2.1 hAppMap hFamily
  have hNatural := ForcingEligibleReindex.natural_of_family hM hp.2.2.2.1 hB.1 hBT.1 hB.2.1 hBT.2.1
    hB.2.2.1 hB.2.2.2.2.1 hBT.2.2.2.2.1 hFamily
  have hv : ConstructionComponentCarrier.EncodedVertex (env (rho 0)) (env I) (env mul) (env q) (env root) := by
    obtain ⟨r,a,U,s,b,V,hc,_,hv,_,_⟩ := hStab
    exact ⟨r,a,U,hc,hv⟩
  obtain ⟨rootT',X,XT,P',Q',pr',PT',Z',prT',f,b,c',phi,hMove',hX,hXT,hGl,hGlT,hFM,hb,hc',hRootMap,hPhi,hOnto,hNat⟩ :=
    ForcingComponentRebase.exists_transport hM hm hJ hpi hFix hp.2.2.2.1 hB.1 hBT.1 hB.2.2.1
      hB.2.2.2.1 hBT.2.2.2.1 hSys hTSys hAppMap hApps hNatural hv hRoot hStab
  have hPres : ForcingReindexSystem.PreservesAvailability (env (rho 0)) (env mul) (env pi) objects maps targets targetMaps apps :=
    fun _ _ _ _ _ _ _ _ hR hr hT ha hxy hn =>
      ForcingReindexSystem.available_iff hM hm hpi hp.2.2.2.1 hB.1 hBT.1 hB.2.2.1
        hB.2.2.2.1 hBT.2.2.2.1 hSys hTSys hAppMap hApps hNatural hR hr hT ha hxy hn
  exact ForcingPersistentCovariance.represented_transport_iff hM hm hJ hData hBound hq hFix hg hgT
    ⟨hB.1,hB.2.1,hB.2.2.1,hB.2.2.2.1,hB.2.2.2.2.1,hGl.1,hGl.2.1,hGl.2.2.1,hGl.2.2.2.1⟩
    ⟨hBT.1,hBT.2.1,hBT.2.2.1,hBT.2.2.2.1,hBT.2.2.2.2.1,hGlT.1,hGlT.2.1,hGlT.2.2.1,hGlT.2.2.2.1⟩
    hAppMap hFamily hPres hGl.2.2.2.2.1 hGlT.2.2.2.2.1 hNat hPhi hOnto hRoot hStab hw hChain hCode hTail

theorem works_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names : Fin k) (code : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hpiHq : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hFix : ForcingConditionGraphs.CompositionGraph (env (rho 0)) (env pi) (env q) (env q))
    (hRoot : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) (env root) (env rootT))
    (hStab : ConstructionComponentCofinal.EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env rootT))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCode : ForcingTailCodes.ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code)
    (hTail : ForcingTailCovariance.TailFixes (env w) (env (rho 0)) (env pi) (env chain))
    {ac d dT : M.Carrier .set}
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) ac)
    (hdd : PureKuratowski.PairMember M d dT ac) :
    Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) dT code ↔
      Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) d code := by
  have hac := ForcingLocalTransport.part_permutation hc
  have ho : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨f,t,_,_,ht,_,_,hGraph⟩ := hc
    exact ForcingCohenOrderAction.graph_order hData.1.2.2.1 ht hGraph
  have transfer := fun (e eT : M.Carrier .set) (heeT : PureKuratowski.PairMember M e eT ac) =>
    represented_covariance hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hpiHq hE hFix hRoot hStab hChain hCode hTail hc heeT
  constructor
  · intro h e he hde
    obtain ⟨eT,heeT,_⟩ := hac.1.1.2 e he
    exact (transfer e eT heeT).mp (h eT (hac.1.2 e eT heeT) ((ho e d eT dT heeT hdd).mpr hde))
  · intro h eT heT hdTeT
    obtain ⟨e,he,heeT⟩ := hac.2.2 eT heT
    exact (transfer e eT heeT).mpr (h e he ((ho e d eT dT heeT hdd).mp hdTeT))

/-- Source ConditionCodeSelection.selected_covariance:64-80, with the same
code order on both sides. Only conditions are transported. -/
theorem selected_of_covariance
    {L W : M.Carrier .set → M.Carrier .set → Prop}
    {EqAt : M.Carrier .set → M.Carrier .set → M.Carrier .set → Prop}
    {P A order code ac d dT : M.Carrier .set}
    (hp : ForcingConditionGraphs.Permutation P ac)
    (ho : ∀ p q pT qT, PureKuratowski.PairMember M p pT ac →
      PureKuratowski.PairMember M q qT ac → (L pT qT ↔ L p q))
    (hw : ∀ p pT a, PureKuratowski.PairMember M p pT ac →
      (Project.FirstOrderSemantics.reduct M).mem a A → (W pT a ↔ W p a))
    (he : ∀ p pT a b, PureKuratowski.PairMember M p pT ac →
      (Project.FirstOrderSemantics.reduct M).mem a A →
      (Project.FirstOrderSemantics.reduct M).mem b A → (EqAt pT a b ↔ EqAt p a b))
    (ha : (Project.FirstOrderSemantics.reduct M).mem code A)
    (hdd : PureKuratowski.PairMember M d dT ac) :
    ForcingPersistentSelection.Selected L W EqAt P A order code dT ↔
      ForcingPersistentSelection.Selected L W EqAt P A order code d := by
  constructor
  · intro h
    refine ⟨(hw d dT code hdd ha).mp h.1,?_⟩
    intro e heP hed b hb hba hbad
    obtain ⟨eT,heeT,_⟩ := hp.1.1.2 e heP
    exact h.2 eT (hp.1.2 e eT heeT) ((ho e d eT dT heeT hdd).mpr hed) b hb hba
      ⟨(hw e eT b heeT hb).mpr hbad.1,(he e eT code b heeT ha hb).mpr hbad.2⟩
  · intro h
    refine ⟨(hw d dT code hdd ha).mpr h.1,?_⟩
    intro eT heTP heTdT b hb hba hbad
    obtain ⟨e,heP,heeT⟩ := hp.2.2 eT heTP
    exact h.2 e heP ((ho e d eT dT heeT hdd).mp heTdT) b hb hba
      ⟨(hw e eT b heeT hb).mp hbad.1,(he e eT code b heeT ha hb).mp hbad.2⟩

theorem selected_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names codes order : Fin k) (code : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hpiHq : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hFix : ForcingConditionGraphs.CompositionGraph (env (rho 0)) (env pi) (env q) (env q))
    (hRoot : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) (env root) (env rootT))
    (hStab : ConstructionComponentCofinal.EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env rootT))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hCodeMem : (Project.FirstOrderSemantics.reduct M).mem code (env codes))
    (hTail : ForcingTailCovariance.TailFixes (env w) (env (rho 0)) (env pi) (env chain))
    {ac d dT : M.Carrier .set}
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env pi) ac)
    (hdd : PureKuratowski.PairMember M d dT ac) :
    ForcingPersistentSelection.Selected (fun p q => ForcingPowerName.Subset q p)
      (Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain)) (ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env chain)) (env (rho 3)) (env codes) (env order) code dT ↔
    ForcingPersistentSelection.Selected (fun p q => ForcingPowerName.Subset q p)
      (Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain)) (ForcingPersistentCodes.Same (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env chain)) (env (rho 3)) (env codes) (env order) code d := by
  have hac := ForcingLocalTransport.part_permutation hc
  have ho : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨f,t,_,_,ht,_,_,hGraph⟩ := hc
    exact ForcingCohenOrderAction.graph_order hData.1.2.2.1 ht hGraph
  apply selected_of_covariance hac ho
  · intro p pT a hpp ha
    exact works_covariance hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names a hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hpiHq hE hFix hRoot hStab hChain ((hCarrier a).mp ha) hTail hc hpp
  · intro p pT a b hpp ha hb
    exact ForcingPersistentCovariance.same_covariance hM env rho mul act hm hData hw hChain
      ((hCarrier a).mp ha) ((hCarrier b).mp hb) hTail hc hpp
  · exact hCodeMem
  · exact hdd

def worksSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
    Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (.mem (.bound pi) (.bound Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi q q))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi root rootT)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root rootT)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain code)
    (.imp (ForcingTailCovariance.tailFixes w (rho 0) pi chain)
    (.existsE (.conj
      (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1).succ (rho 2).succ (rho 3).succ pi.succ 0))
      (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))
        (.iff (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) 0 (up code)) (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) 1 (up code))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingComponentMove.move_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingTailCovariance.tailFixes_freeClosed,
      ForcingPersistentWorks.works_freeClosed]

theorem works_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (worksSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.chainCode_semantics hM,
    ForcingTailCovariance.tailFixes_semantics hM,ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingPersistentWorks.works_semantics hM]
  intro hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hpiHq hE hFix hRoot hStab hChain hCode hTail
  have hDataCopy := hData
  obtain ⟨_,_,_,_,_,_,_,hAct,_,_⟩ := hDataCopy
  obtain ⟨ac,hc⟩ := ForcingLocalTransport.part_of_action hAct
  exact ⟨ac,hc,fun d dT hdd => works_covariance hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names (env code) hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hpiHq hE hFix hRoot hStab hChain hCode hTail hc hdd⟩

theorem works_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (worksSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code))) := by
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
  apply ConstructibleGround.relative_models hM (worksSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (worksSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code)).mp
      (works_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code hL hChoice)

def selectedSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
    Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (.mem (.bound pi) (.bound Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi q q))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi root rootT)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root rootT)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (.mem (.bound code) (.bound codes))
    (.imp (ForcingTailCovariance.tailFixes w (rho 0) pi chain)
    (.existsE (.conj
      (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1).succ (rho 2).succ (rho 3).succ pi.succ 0))
      (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))
        (.iff (ForcingPersistentSelection.selected ForcingPersistentWorks.lower (ForcingPersistentWorks.working rho I G F mul q bound labels E root w chain) (ForcingPersistentWorks.equalAt rho mul w chain) up (up (rho 3)) (up codes) (up order) (up code) 0) (ForcingPersistentSelection.selected ForcingPersistentWorks.lower (ForcingPersistentWorks.working rho I G F mul q bound labels E root w chain) (ForcingPersistentWorks.equalAt rho mul w chain) up (up (rho 3)) (up codes) (up order) (up code) 1))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingComponentMove.move_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailCovariance.tailFixes_freeClosed,
      ForcingPersistentSelection.selected,ForcingPersistentSelection.rel2,ForcingPersistentSelection.rel3,
      ForcingPersistentWorks.lower,ForcingPersistentWorks.working_freeClosed,ForcingPersistentWorks.equalAt_freeClosed]

theorem selected_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ForcingTailCodes.carrier_semantics hM,
    ForcingTailCovariance.tailFixes_semantics hM,ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingPersistentSelection.selected_semantics hM,ForcingPersistentSelection.Selected,
    ForcingPersistentWorks.lower_semantics,ForcingPersistentWorks.working_semantics hM,
    ForcingPersistentWorks.equalAt_semantics hM]
  intro hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hpiHq hE hFix hRoot hStab hChain hCarrier hCodeMem hTail
  have hDataCopy := hData
  obtain ⟨_,_,_,_,_,_,_,hAct,_,_⟩ := hDataCopy
  obtain ⟨ac,hc⟩ := ForcingLocalTransport.part_of_action hAct
  exact ⟨ac,hc,fun d dT hdd => selected_covariance hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names codes order (env code) hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound hq hA hHq hpiHq hE hFix hRoot hStab hChain hCarrier hCodeMem hTail hc hdd⟩

theorem selected_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order))) := by
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
  apply ConstructibleGround.relative_models hM (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order)).mp
      (selected_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root rootT vertices chain names code codes order hL hChoice)

end PPAC.Migration.ForcingWorksCovariance
