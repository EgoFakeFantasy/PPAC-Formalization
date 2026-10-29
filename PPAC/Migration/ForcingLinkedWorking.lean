/- Pinned CodeLinks.exists_linked_working_of_stable:349-385.
One literal code works above the initial condition at any Common vertex. -/
import PPAC.Migration.ForcingStableCodes
import PPAC.Migration.ForcingCodeLinkRepresentation

namespace PPAC.Migration.ForcingLinkedWorking
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

private theorem at_of_arrow_eq (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B g q bound labels E
      oi objects S mi maps root source Q gluePr r a U vertex n sigma tau b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hSmall : ForcingSupportSize.Small (env (rho 0)) mu)
    (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) one mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hObjMap : MapsTo (env (rho 4)) oi objects)
    (hObj : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E (env (rho 4)) objects)
    (hS : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env (rho 4)) S)
    (hMap : MapsTo S mi maps)
    (hMaps : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (fun j => env (rho j)) (env G) (env F) (env mul) g q bound labels E S maps)
    (hSys : ForcingEligibleSystem.System (env (rho 0)) objects maps)
    (hAll : ForcingComponentGluing.AllFiberMaps (env (rho 0)) I (env mul) q objects maps root Q gluePr)
    (hComm : ForcingComponentGluing.Commuting (env (rho 0)) I (env mul) q objects maps Q gluePr)
    (hRoot : Code source r a U)
    (hArrow : EncodedArrow (env (rho 0)) I (env mul) q source vertex n)
    (hCommon : EncodedCommon (env (rho 0)) I (env mul) q root vertex)
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) bound vertex sigma)
    (hAt : At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      I (env G) (env F) (env mul) g q bound labels E objects maps root gluePr source tau b)
    (hEq : ForcingLocalAtomic.EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau) :
    At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      I (env G) (env F) (env mul) g q bound labels E objects maps root gluePr vertex sigma b := by
  have hAtCopy := hAt
  obtain ⟨r',a',U',Ar,Hr,Xr,Qr,pr,Or,Vr,x,p,hBase,hCode,hDr,hr,hVr,hx,htx,hpx,hpb⟩ := hAtCopy
  have hAllBase : ForcingComponentGluing.AllFiberMaps (env (rho 0)) I (env mul) q objects maps source Q gluePr :=
    fun v X hv hX => hAll v X ((ForcingComponentRebase.common_iff hM hm hJ hBase).mpr hv) hX
  have hAtBase : At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      I (env G) (env F) (env mul) g q bound labels E objects maps source gluePr source tau b :=
    ⟨r',a',U',Ar,Hr,Xr,Qr,pr,Or,Vr,x,p,(ForcingComponentRebase.common_iff hM hm hJ hBase).mp hBase,hCode,hDr,hr,hVr,hx,htx,hpx,hpb⟩
  have hTarget := ForcingStableCodes.at_of_root_eq hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hJ hp hG hF
    hg hObjMap hObj hS hMap hMaps hSys hAllBase hComm hRoot hArrow
    ((ForcingComponentRebase.common_iff hM hm hJ hBase).mp hCommon) hEntry hAtBase hEq
  obtain ⟨s,c,V,A,Hs,Xs,Qs,ps,Os,Vs,y,pv,_,hc,hDs,hs,hVs,hy,hsy,hpv,hpvb⟩ := hTarget
  exact ⟨s,c,V,A,Hs,Xs,Qs,ps,Os,Vs,y,pv,hCommon,hc,hDs,hs,hVs,hy,hsy,hpv,hpvb⟩

theorem exists_linked_working_of_stable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
      zero root vertices chain names vertex r index U d tau z : Fin k)
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
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hc : Code (env vertex) (env r) (env index) (env U))
    (hCommon : EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env vertex))
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) (env bound) (env vertex) (env tau))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env r))
    (hForce : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) (env z) (ForcingEligibility.isClass 0 1 2))
    (hStable : ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset (env d) e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env index) (env tau) (env U)) :
    ∃ code, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code ∧
      ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env d) code ∧
      ForcingCodeLinks.Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) (env d) (env vertex) (env tau) code := by
  have hCommonCopy := hCommon
  obtain ⟨_,_,_,r',index',U',_,hc',_,hVertex,_⟩ := hCommonCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  have hEntryCopy := hEntry
  obtain ⟨r',index',U',Ar,Hr,hc',hAr,hHr,hTau⟩ := hEntryCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  have hex e (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3))) (hde : ForcingPowerName.Subset (env d) e) :
      ∃ g oi objects S mi maps P Q gluePr b,
        ForcingPrincipalFilter.Principal (env (rho 3)) e g ∧
        ForcingPersistentWorks.Bundle (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
          (env I) (env G) (env F) (env mul) g (env q) (env bound) (env labels) (env E) (env root) oi objects S mi maps P Q gluePr ∧
        ForcingEligibleSystem.System (env (rho 0)) objects maps ∧
        ForcingComponentGluing.AllFiberMaps (env (rho 0)) (env I) (env mul) (env q) objects maps (env root) Q gluePr ∧
        ForcingComponentGluing.Commuting (env (rho 0)) (env I) (env mul) (env q) objects maps Q gluePr ∧
        (Project.FirstOrderSemantics.reduct M).mem b Q ∧
        At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
          (env I) (env G) (env F) (env mul) g (env q) (env bound) (env labels) (env E) objects maps (env root) gluePr (env vertex) (env tau) b := by
    obtain ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,hg,hBundle⟩ := ForcingPersistentWorks.assemble_principal hM env rho
      I K B w one G F mul q bound labels E root hm hp he
    have hBundleCopy := hBundle
    obtain ⟨hObjMap,hObj,hS,hMap,hMaps,hP,hGlue,hQ,hProjection⟩ := hBundleCopy
    have hgf := ForcingPrincipalFilter.principal_filter he hg
    have hSys := ForcingEligibleSystem.system_of_families hM hChoice env rho G F mul
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hLabelBound hgf hq hAq hHq hE hObj hS hMaps
    obtain ⟨hAll,hComm⟩ := ForcingComponentGluing.gluing_laws hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys hP hGlue hQ hProjection
    obtain ⟨Or,hr,_⟩ := hObjMap.1.2 (env r) ((hp.2.2.2.1 (env r)).mpr hVertex.1)
    obtain ⟨Ar',Hr',Xr,Qr,pr,hDr⟩ := ((hObj (env r) Or).mp hr).2
    have eA := (ModelTransfer.extensionality hM).eq_of_same_members Ar Ar' (fun t => (hAr t).trans (hDr.1 t).symm)
    subst Ar'
    have eH := ForcingLabelPermutations.fixing_unique hM hHr hDr.2.1
    subst Hr'
    obtain ⟨ze,hze⟩ := ForcingSupportingRoot.exists_code hM e (env r)
    have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
    have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 (env d)).mp hd) hVertex.1 hz
    have hzeW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 e).mp he) hVertex.1 hze
    have hlez := (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul ze (env z)).mpr
      ((ForcingSupportingRoot.code_le hze hz).mpr ⟨hde,ForcingDiagramPoset.le_refl hm hVertex.1⟩)
    have hForceE := ForcingFormula.mono hM hpre (ForcingEligibility.isClass 0 1 2)
      (Source.SetLanguage.args3 (env tau) (env labels) (env E)) hzW hzeW hlez hForce
    obtain ⟨x,Vr,htx,hVr,hx⟩ := ForcingForcedAvailability.exists_fiber_principal hM hChoice env rho G F mul
      hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE
      he hg hObjMap hObj hS hMap hMaps hr hDr hVertex.2.1 hLabelBound hVertex.2.2.2.1
      ((hDr.2.2.1 (env tau)).mpr hTau) hze hForceE (hStable e he hde)
    obtain ⟨f,hf,_,_⟩ := hAll (env vertex) Vr hCommon ⟨env r,env index,env U,Or,hc,hr,hVr⟩
    obtain ⟨b,hxb,_⟩ := hf.1.1.2 x hx
    obtain ⟨_,p,hpx,hpb⟩ := (hf.2 x b).mp hxb
    exact ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hSys,hAll,hComm,hf.1.2 x b hxb,
      env r,env index,env U,Ar,Hr,Xr,Qr,pr,Or,Vr,x,p,hCommon,hc,hDr,hr,hVr,hx,htx,hpx,hpb⟩
  obtain ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hSys,hAll,hComm,hb,hAt⟩ := hex (env d) hd (fun _ h => h)
  obtain ⟨hObjMap,hObj,hS,hMap,hMaps,_,_,_,_⟩ := hBundle
  let ext : Fin (k+5) → M.Carrier .set := Fin.cases g (Fin.cases objects (Fin.cases maps (Fin.cases gluePr (Fin.cases b env))))
  let up : Fin k → Fin (k+5) := fun j => j.succ.succ.succ.succ.succ
  obtain ⟨code,hCode,hRep⟩ := ForcingTailCodes.exists_representing_code_over hM hChoice
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) ext up (fun j => up (rho j))
    (up I) (up G) (up F) (up mul) 0 (up q) (up bound) (up labels) (up E) 1 2 (up root) 3 (up w) (up names) (up chain) 4
    hw hNames hChain.1 hChain.2.2.2.1 hp.2.2.2.1 hObjMap hObj hAll hb
  have hCoh := ForcingComponentFibers.coherent_of_system hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys (q := env q)
  have hl := ForcingCodeLinkRepresentation.links_of_represents_at hM (ForcingPairUnion.domain rho G F) env rho mul
    hm hp hp.2.2.2.1 hObjMap hObj hMaps hCoh hAll hComm hw hChain hd hg hVertices hRep hAt
  refine ⟨code,hCode,?_,hl⟩
  intro e he hde
  obtain ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hSys,hAll,hComm,hb,hAt⟩ := hex e he hde
  have hBundleCopy := hBundle
  obtain ⟨hObjMap,hObj,hS,hMap,hMaps,_,_,_,_⟩ := hBundleCopy
  have hgf := ForcingPrincipalFilter.principal_filter he hg
  obtain ⟨r',index',U',hc',N,hN,htail⟩ := ForcingCodeLinks.links_mono hM env rho mul hm hp he hde hl
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  refine ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hb,N,hN,?_⟩
  intro i hi hNi
  obtain ⟨vi,sigma,n,hvi,hsi,hArrow,heq⟩ := htail i hi hNi
  obtain ⟨vi',hvi',hEntryi⟩ := hCode.2 i sigma hsi
  have hEqVertex := ForcingConditionGraphs.function_unique hChain.1.1 hvi hvi'
  subst vi'
  exact ⟨vi,sigma,hvi,hsi,at_of_arrow_eq hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hJ hp hG hF
    hgf hObjMap hObj hS hMap hMaps hSys hAll hComm hc hArrow (hChain.2.2.2.1 i vi hvi) hEntryi hAt
    ((ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp he hVertex.1 hg).mpr heq)⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z : Fin k) : Project.Sentence where
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
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code vertex r index U)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d r))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (Source.SetLanguage.args3 tau labels E) (rho 6) z (ForcingEligibility.isClass 0 1 2)))
    (.imp (.forallE (.imp (.mem (.bound 0) (.bound (rho 3).succ)) (.imp (Project.Formula.subset (.bound d.succ) (.bound 0)) (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ index.succ tau.succ U.succ))))
    (.existsE (.conj (ForcingTailCodes.chainCode (fun j => (rho j).succ) G.succ F.succ bound.succ w.succ names.succ chain.succ 0)
      (.conj (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.succ (fun j => (rho j).succ) I.succ G.succ F.succ mul.succ q.succ bound.succ labels.succ E.succ root.succ w.succ chain.succ d.succ 0)
        (ForcingCodeLinks.links (orderFormula (rho 0) mul) Fin.succ (rho 6).succ w.succ (rho 0).succ I.succ mul.succ q.succ chain.succ d.succ vertex.succ tau.succ 0)))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ForcingTailCodes.chainCode_freeClosed,ForcingTailCodes.entry_freeClosed,
      ForcingPersistentWorks.works_freeClosed,ForcingCodeLinks.links_freeClosed,ForcingForcedAvailability.carrier_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
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
    ConstructionComponentCarrier.code_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingTailCodes.candidates_semantics hM,ForcingTailCodes.chainCode_semantics hM,ForcingTailCodes.entry_semantics hM,
    ForcingPersistentWorks.works_semantics hM,ForcingCodeLinks.links_semantics hM,
    ForcingFormula.formula_semantics (M := M),ForcingForcedAvailability.carrier_semantics hM]
  exact exists_linked_working_of_stable hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z)).mp
      (construction_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names vertex r index U d tau z hL hChoice)

end PPAC.Migration.ForcingLinkedWorking
