/- Pinned PersistentCodes.ChainCode.exists_working_code_of_stable:371-425.
One internal omega-code is chosen once; its literal names persist at every
stronger condition. Reuse native uniformization, actual principal fibers,
local restriction injectivity and the existing toGlued_arrow law. -/
import PPAC.Migration.ForcingForcedAvailability

namespace PPAC.Migration.ForcingStableCodes
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

/-- The source hcodes/choose step, performed on the full internal omega.
Forced availability supplies the same restricted local names as the already
proved principal-fiber bijection; no new choice backend is introduced. -/
theorem root_equal_code_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul bound w names chain zero root r a U q : Fin k)
    (d tau : M.Carrier .set) {vertices : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hz : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) vertices (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env (rho 4)))
    (hAvail : ForcingForcedAvailability.Carrier R env (fun j => env (rho j)) (env G) (env F)
      (env mul) (env bound) d (env r) (env a) tau (env U)) :
    ∃ code, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code ∧
      ∀ i sigma, PureKuratowski.PairMember M i sigma code → EqF R env (env (rho 6)) d (env r) sigma tau := by
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  let schema : Project.BinarySchema (k+2) := {
    body := .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up chain).succ.succ.succ 2 0))
      (.conj (ForcingTailCodes.entry (fun j => (up (rho j)).succ.succ.succ) (up G).succ.succ.succ (up F).succ.succ.succ (up bound).succ.succ.succ 0 1)
        (ForcingPrincipalFilter.eqF R (fun j => (up j).succ.succ.succ) (up (rho 6)).succ.succ.succ 3 (up r).succ.succ.succ 1 4)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingTailCodes.entry_freeClosed,ForcingPrincipalFilter.eqF_freeClosed] }
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) (k+2) :=
    {bound := Fin.cases d (Fin.cases tau env),free := fun _ => env w}
  have he i sigma : schema.denote penv i sigma ↔ ∃ vertex,
      PureKuratowski.PairMember M i vertex (env chain) ∧
      Entry (fun j => env (rho j)) (env G) (env F) (env bound) vertex sigma ∧
      EqF R env (env (rho 6)) d (env r) sigma tau := by
    simp only [schema,Project.BinarySchema.denote,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
      ForcingTailCodes.entry_semantics hM,ForcingPrincipalFilter.eqF_semantics hM]
    rfl
  obtain ⟨code,hCode,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := env w) (Y := env names) (by
      intro i hi
      obtain ⟨vertex,hv,_⟩ := hChain.1.1.2 i hi
      have hzW := ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1
      have hzi : ConstructionFractionOrder.NatLe (env zero) i := by
        rcases ConstructionFractionOrder.nat_compare hM hw hzW hi with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hz i h).elim
      obtain ⟨n,hn⟩ := hChain.2.2.1 (env zero) i (env root) vertex hzi hChain.2.1 hv
      obtain ⟨r',a',U',s,b,V,hRoot',hvCode,_,hVertex,hArrow⟩ := hn
      obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
      obtain ⟨_,_,t,A,H,sigma,ht,hSub,hA,hH,hLocal,hEq⟩ := (hAvail n).mp hArrow.1
      have et := ConstructionComponentVertices.sub_eq hM ((hDiagrams t).mp ht) hVertex.1 hSub hArrow.2.1
      subst t
      exact ⟨sigma,(hNames sigma).mpr hLocal.1,(he i sigma).mpr ⟨vertex,hv,⟨s,b,V,A,H,hvCode,hA,hH,hLocal⟩,hEq⟩⟩)
  have hMap := (ForcingSupportSize.native_mapsTo hM _ _ _).mpr hCode
  refine ⟨code,⟨hMap,?_⟩,?_⟩
  · intro i sigma his
    obtain ⟨vertex,hv,hEntry,_⟩ := (he i sigma).mp (hSelect i sigma his)
    exact ⟨vertex,hv,hEntry⟩
  · intro i sigma his
    obtain ⟨_,_,_,hEq⟩ := (he i sigma).mp (hSelect i sigma his)
    exact hEq

theorem exists_root_equal_code (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul bound w names chain zero root r a U d tau q : Fin k) {vertices : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hz : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) vertices (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env (rho 4)))
    (hAvail : ForcingForcedAvailability.Carrier R env (fun j => env (rho j)) (env G) (env F)
      (env mul) (env bound) (env d) (env r) (env a) (env tau) (env U)) :
    ∃ code, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code ∧
      ∀ i sigma, PureKuratowski.PairMember M i sigma code → EqF R env (env (rho 6)) (env d) (env r) sigma (env tau) := by
  exact root_equal_code_at hM hChoice R env rho I G F mul bound w names chain zero root r a U q (env d) (env tau) hw hz hNames hChain hRoot hDiagrams hAvail

/-- The source restriction-injectivity and toGlued_arrow step. A literal
local name equal at the root represents the same glued element. -/
theorem at_of_root_eq (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa one mark H C incoming base I K B g q bound labels E
      oi objects S mi maps root Q gluePr r a U vertex n sigma tau b : M.Carrier .set}
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
    (hRoot : Code root r a U)
    (hArrow : EncodedArrow (env (rho 0)) I (env mul) q root vertex n)
    (hCommon : EncodedCommon (env (rho 0)) I (env mul) q root vertex)
    (hEntry : Entry (fun j => env (rho j)) (env G) (env F) bound vertex sigma)
    (hAt : At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      I (env G) (env F) (env mul) g q bound labels E objects maps root gluePr root tau b)
    (hEq : ForcingLocalAtomic.EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau) :
    At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      I (env G) (env F) (env mul) g q bound labels E objects maps root gluePr vertex sigma b := by
  obtain ⟨r',a',U',Ar,Hr,Xr,Qr,pr,Or,Vr,x,p,hCommonRoot,hRoot',hDr,hr,hVr,hx,htx,hpx,hpb⟩ := hAt
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
  obtain ⟨s,c,V,A,Hs,hCode,hA,hHs,hLocal⟩ := hEntry
  have hArrowCopy := hArrow
  obtain ⟨r',a',U',s',c',V',hRoot',hCode',hVertexRoot,hVertex,hArow⟩ := hArrowCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
  obtain ⟨Os,hs,_⟩ := hObjMap.1.2 s ((hp.2.2.2.1 s).mpr hVertex.1)
  obtain ⟨As,Hs',Xs,Qs,ps,hDs⟩ := ((hObj s Os).mp hs).2
  have eA := (ModelTransfer.extensionality hM).eq_of_same_members A As (fun z => (hA z).trans (hDs.1 z).symm)
  subst As
  have eH := ForcingLabelPermutations.fixing_unique hM hHs hDs.2.1
  subst Hs'
  obtain ⟨Vs,hVs⟩ := ForcingSystemFibers.exists_fiber hM (env (rho 0)) (env mul) objects maps s Os c V
  have hRootFiber : ForcingComponentFibers.VertexFiber (env (rho 0)) (env mul) objects maps root Vr := ⟨r,a,U,Or,hRoot,hr,hVr⟩
  have hVertexFiber : ForcingComponentFibers.VertexFiber (env (rho 0)) (env mul) objects maps vertex Vs := ⟨s,c,V,Os,hCode,hs,hVs⟩
  obtain ⟨arrow,harrow⟩ := ForcingComponentFibers.exists_arrowMap hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys hArrow hRootFiber hVertexFiber
  have harrowCopy := harrow
  obtain ⟨r',a',U',s',c',V',z,f,hRoot',hCode',hz,hf,hRestr,_,hOnto⟩ := harrowCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
  obtain ⟨y,hy,hyx⟩ := hOnto x hx
  obtain ⟨As',Hs',Xs',Qs',ps',Ar',Hr',Xr',Qr',pr',fQ,hDs',hDr',hfQ,hQRestr,_,hfRestr⟩ :=
    ForcingEligibleSystem.map_data hM hObj hMaps hs hr hz hf
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDs hDs'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,_⟩ := ForcingEligibleFamily.data_unique hM hDr hDr'
  have hLe : ForcingDiagramOrder.Le (env (rho 0)) (env mul) r s := ⟨n,hVertexRoot.2.2.1 n hArow.1,hArow.2.1⟩
  have hsigmaXs := (hDs.2.2.1 sigma).mpr hLocal
  have hRange : ForcingPowerName.Subset A Ar := fun t ht => (hDr.1 t).mpr
    (ConstructionDescentPlacement.range_antitone hLe ((hA t).mp ht))
  have hsigmaXr := ForcingLocalNames.restrict_name hHs hDr.2.1 hRange hDs.2.2.1 hDr.2.2.1 sigma hsigmaXs
  obtain ⟨y',hsy,_⟩ := hDs.2.2.2.1.1.2 sigma hsigmaXs
  obtain ⟨x',hsx,_⟩ := hDr.2.2.2.1.1.2 sigma hsigmaXr
  have ex : x' = x := (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hVertexRoot.1 hDr.2.2.2.2.2.1 sigma tau x' x hsx htx).mpr hEq
  subst x'
  have hy'x := ForcingLocalRestriction.restrict_ofName hQRestr hsy hsx
  have hyxQ := ((hfRestr y x).mp ((hRestr y x).mp hyx).1).1
  have hInj := ForcingLocalInjectivity.restrict_injective hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hVertex.1 hVertexRoot.1 hLe hA hHs hg
    hDs.2.2.1 hDs.2.2.2.2.2.1 hDr.2.2.2.2.2.1 hfQ hQRestr
  have ey := hInj.2 y' y x hy'x hyxQ
  subst y'
  obtain ⟨fRoot,hfRoot,_,_⟩ := hAll root Vr hCommonRoot hRootFiber
  obtain ⟨fVertex,hfVertex,_,_⟩ := hAll vertex Vs hCommon hVertexFiber
  have hxb := (hfRoot.2 x b).mpr ⟨hx,p,hpx,hpb⟩
  obtain ⟨c',hyc,_⟩ := hfVertex.1.1.2 y hy
  have ebc := hComm root vertex Vr Vs n arrow fRoot fVertex x y b c' hRootFiber hVertexFiber hArrow harrow hfRoot hfVertex hyx hxb hyc
  subst c'
  obtain ⟨_,pv,hpv,hpvb⟩ := (hfVertex.2 y b).mp hyc
  exact ⟨s,c,V,A,Hs,Xs,Qs,ps,Os,Vs,y,pv,hCommon,hCode,hDs,hs,hVs,hy,hsy,hpv,hpvb⟩

/-- Pinned exists_working_code_of_stable, with one code for every stronger
internal condition and equality of every literal entry at the original root. -/
theorem working_code_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr : Fin k)
    (d tau z : M.Carrier .set)
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
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hTau : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env Hr) tau)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hz : ForcingSupportingRoot.Code z d (env r))
    (hForce : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 tau (env labels) (env E)) (env (rho 6)) z (ForcingEligibility.isClass 0 1 2))
    (hStable : ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset d e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env a) tau (env U)) :
    ∃ code, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code ∧
      ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) d code ∧
      ∀ i sigma, PureKuratowski.PairMember M i sigma code →
        EqF (orderFormula (rho 0) mul) env (env (rho 6)) d (env r) sigma tau := by
  have hCommonRoot := hChain.2.2.2.1 (env zero) (env root) hChain.2.1
  have hVertex : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) (env r) (env a) (env U) := by
    obtain ⟨r',a',U',_,_,_,hRoot',_,hv,_,_⟩ := hCommonRoot
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
    exact hv
  obtain ⟨code,hCode,hEqual⟩ := root_equal_code_at hM hChoice (orderFormula (rho 0) mul) env rho
    I G F mul bound w names chain zero root r a U q d tau hw hzero hNames hChain hRoot hp.2.2.2.1
    (hStable d hd (fun _ h => h))
  refine ⟨code,hCode,?_,hEqual⟩
  intro e he hde
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
  have eA := (ModelTransfer.extensionality hM).eq_of_same_members (env Ar) Ar' (fun t => (hAr t).trans (hDr.1 t).symm)
  subst Ar'
  have eH := ForcingLabelPermutations.fixing_unique hM hHr hDr.2.1
  subst Hr'
  obtain ⟨ze,hze⟩ := ForcingSupportingRoot.exists_code hM e (env r)
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp hd) hVertex.1 hz
  have hzeW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 e).mp he) hVertex.1 hze
  have hlez := (ForcingProductSymmetry.orderFormula_semantics env (rho 0) mul ze z).mpr
    ((ForcingSupportingRoot.code_le hze hz).mpr ⟨hde,ForcingDiagramPoset.le_refl hm hVertex.1⟩)
  have hForceE := ForcingFormula.mono hM hpre (ForcingEligibility.isClass 0 1 2)
    (Source.SetLanguage.args3 tau (env labels) (env E)) hzW hzeW hlez hForce
  obtain ⟨x,Vr,htx,hVr,hx⟩ := ForcingForcedAvailability.exists_fiber_principal hM hChoice env rho G F mul
    hw hMu hI hSmall hMergers hRow hm hp hG hF hLabelMap hTop hLabels hq hAq hHq hE
    he hg hObjMap hObj hS hMap hMaps hr hDr hVertex.2.1 hLabelBound hVertex.2.2.2.1
    ((hDr.2.2.1 tau).mpr hTau) hze hForceE (hStable e he hde)
  have hVF : ForcingComponentFibers.VertexFiber (env (rho 0)) (env mul) objects maps (env root) Vr :=
    ⟨env r,env a,env U,Or,hRoot,hr,hVr⟩
  obtain ⟨f,hf,_,_⟩ := hAll (env root) Vr hCommonRoot hVF
  obtain ⟨b,hxb,_⟩ := hf.1.1.2 x hx
  have hb := hf.1.2 x b hxb
  obtain ⟨_,p,hpx,hpb⟩ := (hf.2 x b).mp hxb
  have hAt : At (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
      (env I) (env G) (env F) (env mul) g (env q) (env bound) (env labels) (env E) objects maps (env root) gluePr (env root) tau b :=
    ⟨env r,env a,env U,env Ar,env Hr,Xr,Qr,pr,Or,Vr,x,p,hCommonRoot,hRoot,hDr,hr,hVr,hx,htx,hpx,hpb⟩
  have hzWnat := ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1
  refine ⟨g,oi,objects,S,mi,maps,P,Q,gluePr,b,hg,hBundle,hb,env zero,hzWnat,?_⟩
  intro i hi hzi
  obtain ⟨sigma,his,_⟩ := hCode.1.1.2 i hi
  obtain ⟨vertex,hv,hEntry⟩ := hCode.2 i sigma his
  obtain ⟨n,hArrow⟩ := hChain.2.2.1 (env zero) i (env root) vertex hzi hChain.2.1 hv
  have hEqE := ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he hVertex.1 hde (hEqual i sigma his)
  have hEqG := (ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp he hVertex.1 hg).mpr hEqE
  exact ⟨vertex,sigma,hv,his,at_of_root_eq hM hChoice env rho G F mul hw hMu hI hSmall hMergers hRow hm hJ hp hG hF
    hgf hObjMap hObj hS hMap hMaps hSys hAll hComm hRoot hArrow (hChain.2.2.2.1 i vertex hv) hEntry hAt hEqG⟩

theorem exists_working_code_of_stable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq
      zero root vertices chain names r a U Ar Hr d tau z : Fin k)
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
    (hzero : ForcingWithTopCarrier.Empty (env zero))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : Code (env root) (env r) (env a) (env U))
    (hAr : ForcingSupportedNames.Range (env (rho 0)) (env r) (env Ar))
    (hHr : ForcingLabelPermutations.Fixing (env G) (env Ar) (env Hr))
    (hTau : ForcingLocalNames.LocalName (fun j => env (rho j)) (env G) (env F) (env bound) (env Hr) (env tau))
    (hd : (Project.FirstOrderSemantics.reduct M).mem (env d) (env (rho 3)))
    (hz : ForcingSupportingRoot.Code (env z) (env d) (env r))
    (hForce : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 (env tau) (env labels) (env E)) (env (rho 6)) (env z) (ForcingEligibility.isClass 0 1 2))
    (hStable : ∀ e, (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)) → ForcingPowerName.Subset (env d) e →
      ForcingForcedAvailability.Carrier (orderFormula (rho 0) mul) env (fun j => env (rho j)) (env G) (env F)
        (env mul) (env bound) e (env r) (env a) (env tau) (env U)) :
    ∃ code, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) code ∧
      ForcingPersistentWorks.Works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun j => env (rho j))
        (env I) (env G) (env F) (env mul) (env q) (env bound) (env labels) (env E) (env root) (env w) (env chain) (env d) code ∧
      ∀ i sigma, PureKuratowski.PairMember M i sigma code →
        EqF (orderFormula (rho 0) mul) env (env (rho 6)) (env d) (env r) sigma (env tau) := by
  exact working_code_at hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr (env d) (env tau) (env z) hw hMu hI hSmall hMergers hRow hm hJ hp hG hF hLabelMap hTop hLabels hLabelBound hq hAq hHq hE hzero hNames hChain hRoot hAr hHr hTau hd hz hForce hStable

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z : Fin k) : Project.Sentence where
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
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero))
    (.imp (ForcingTailCodes.candidates rho G F bound names)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r a U)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) r Ar))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Ar Hr))
    (.imp (ProjectSyntax.encode id (ForcingLocalNames.localName rho G F bound Hr tau))
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d r))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id (Source.SetLanguage.args3 tau labels E) (rho 6) z (ForcingEligibility.isClass 0 1 2)))
    (.imp (.forallE (.imp (.mem (.bound 0) (.bound (rho 3).succ))
      (.imp (Project.Formula.subset (.bound d.succ) (.bound 0))
        (ForcingForcedAvailability.carrier (orderFormula (rho 0) mul) Fin.succ (fun j => (rho j).succ) G.succ F.succ mul.succ bound.succ 0 r.succ a.succ tau.succ U.succ))))
    (.existsE (.conj
      (ForcingTailCodes.chainCode (fun j => (rho j).succ) G.succ F.succ bound.succ w.succ names.succ chain.succ 0)
      (.conj (ForcingPersistentWorks.works (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.succ (fun j => (rho j).succ)
        I.succ G.succ F.succ mul.succ q.succ bound.succ labels.succ E.succ root.succ w.succ chain.succ d.succ 0)
        (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))
          (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) up (up (rho 6)) (up d) (up r) 0 (up tau))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingTailCodes.candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingForcedAvailability.carrier_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingPersistentWorks.works_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z)).TrueIn M := by
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
    ForcingLocalNames.localName_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),ForcingForcedAvailability.carrier_semantics hM,
    ForcingTailCodes.chainCode_semantics hM,ForcingPersistentWorks.works_semantics hM,
    KuratowskiZF.source_edge,ForcingPrincipalFilter.eqF_semantics hM]
  exact exists_working_code_of_stable hM hChoice env rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z)).mp
      (construction_models rho w mu history kappa one mark H C incoming base I K B G F mul labelMap top bit labels bound E q Aq Hq zero root vertices chain names r a U Ar Hr d tau z hL hChoice)

end PPAC.Migration.ForcingStableCodes
