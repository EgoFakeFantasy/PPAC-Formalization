/- Pinned TailGraphs.at_transport_iff:103-146. Literal names, actual local
quotient maps and whole-component gluing. Both directions retain arbitrary
names; locality is recovered from the actual name bijection, not assumed. -/
import PPAC.Migration.ForcingTailCodes
import PPAC.Migration.ForcingComponentRebase

namespace PPAC.Migration.ForcingTailTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (EncodedCommon)
open ForcingComponentMove (Move)
open ForcingEligibleFamily (Data)
open ForcingTailCodes (At)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem common_transport_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q pi inv root rootT vertex vertexT : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hp : Permutation I pi) (hi : Permutation I inv)
    (hInv : ForcingConditionGraphs.InverseGraph pi inv)
    (hq : Injection D I q) (hFix : CompositionGraph D pi q q)
    (hRoot : Move D I mul q pi root rootT) (hStab : EncodedCommon D I mul q root rootT)
    (hMove : Move D I mul q pi vertex vertexT) :
    EncodedCommon D I mul q root vertexT ↔ EncodedCommon D I mul q root vertex := by
  constructor
  · intro h
    exact ForcingComponentMove.move_common hM hi (ForcingDiagramCarrier.reverse hp hq hInv hFix)
      (ForcingComponentMove.move_inverse hp hInv hRoot) (ForcingComponentMove.move_inverse hp hInv hMove)
      ((ForcingComponentRebase.common_iff hM hm hJ hStab).mp h)
  · intro h
    exact (ForcingComponentRebase.common_iff hM hm hJ hStab).mpr
      (ForcingComponentMove.move_common hM hp hFix hRoot hMove h)

theorem at_iff_row (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E objects maps root gluePr vertex sigma b r index U A H X Q pr O V : M.Carrier .set}
    (hCode : Code vertex r index U) (hD : Data R Hdom env v G F mul g q bound labels E r A H X Q pr O)
    (hr : PureKuratowski.PairMember M r O objects)
    (hV : ForcingSystemFibers.Fiber (v 0) mul objects maps r O index U V) :
    At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b ↔
      EncodedCommon (v 0) I mul q root vertex ∧ ∃ x,
        (Project.FirstOrderSemantics.reduct M).mem x V ∧ PureKuratowski.PairMember M sigma x pr ∧
        ∃ p, PureKuratowski.Code M p vertex x ∧ PureKuratowski.PairMember M p b gluePr := by
  constructor
  · rintro ⟨r',index',U',A',H',X',Q',pr',O',V',x,p,hCommon,hCode',hD',_,hV',hx,hs,hp,hb⟩
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode hCode'
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hD hD'
    exact ⟨hCommon,x,(hV x).mpr ((hV' x).mp hx),hs,p,hp,hb⟩
  · rintro ⟨hCommon,x,hx,hs,p,hp,hb⟩
    exact ⟨r,index,U,A,H,X,Q,pr,O,V,x,p,hCommon,hCode,hD,hr,hV,hx,hs,hp,hb⟩

theorem at_transport_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps
      objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (v 0) mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (v 0) mul)
    (hData : ForcingProductCovariance.SystemData v I K B w G F mu pi inv c act ai)
    (hBound : ForcingSupportedNames.Supported v G bound)
    (hq : Injection (v 0) I q) (hFix : CompositionGraph (v 0) pi q q)
    (hObjMap : MapsTo (v 4) objImage objects) (hTargetMap : MapsTo (v 4) targetImage targets)
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hTarget : ForcingEligibleFamily.Family R Hdom env v G F mul gT q bound labels E (v 4) targets)
    (hAppMap : MapsTo (v 4) appImage apps)
    (hFamily : ForcingEligibleReindex.Family R Hdom env v G F mul g gT q bound labels E pi act apps)
    (hPres : ForcingReindexSystem.PreservesAvailability (v 0) mul pi objects maps targets targetMaps apps)
    (hAll : ForcingComponentGluing.AllFiberMaps (v 0) I mul q objects maps root Q gluePr)
    (hAllT : ForcingComponentGluing.AllFiberMaps (v 0) I mul q targets targetMaps root Z gluePrT)
    (hNat : ForcingGluedTransport.Naturality (v 0) I mul q pi objects maps targets targetMaps apps root Q Z gluePr gluePrT phi)
    (hPhi : Injection Q Z phi) (hRoot : Move (v 0) I mul q pi root rootT)
    (hStab : EncodedCommon (v 0) I mul q root rootT) (hMove : Move (v 0) I mul q pi vertex vertexT)
    (hName : ForcingNames.IsName (v 6) sigma) (hAct : ForcingStabilizer.Action (v 6) act sigma sigmaT)
    (hbbT : PureKuratowski.PairMember M b bT phi) :
    At R Hdom env v I G F mul gT q bound labels E targets targetMaps root gluePrT vertexT sigmaT bT ↔
      At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b := by
  have hDiagrams := hData.1.2.2.2.1
  have hc := ForcingProductCovariance.context_of_data hM hData
  have hApps := ForcingEligibleReindex.apps_of_family hM hDiagrams hObj hTarget hAppMap hFamily
  have hCommon := common_transport_iff hM hm hJ hData.2.2.1 hData.2.2.2.1 hData.2.2.2.2.1 hq hFix hRoot hStab hMove
  obtain ⟨r,index,U,rT,hCode,hCodeT,hrI,hrTI,hComp⟩ := hMove
  obtain ⟨O,hr,_⟩ := hObjMap.1.2 r ((hDiagrams r).mpr hrI.1)
  obtain ⟨OT,hrT,_⟩ := hTargetMap.1.2 rT ((hDiagrams rT).mpr hrTI.1)
  obtain ⟨app,hApp,_⟩ := hAppMap.1.2 r ((hDiagrams r).mpr hrI.1)
  obtain ⟨A,H,X,T,pr,AT,HT,Y,TT,ps,fq,hD,hDT,hFq,hGraph,hAppInj,hRes,_⟩ :=
    ForcingEligibleReindex.app_data hM hDiagrams hObj hTarget hFamily hComp hr hrT hApp
  have hASub : ForcingPowerName.Subset A I := by
    intro x hx
    obtain ⟨d,_,hdx⟩ := (hD.1 x).mp hx
    exact hrI.1.1.2 d x hdx
  have hImage : ForcingStabilizerTransport.Image pi A AT := by
    intro y
    constructor
    · intro hy
      obtain ⟨d,hd,hdy⟩ := (hDT.1 y).mp hy
      obtain ⟨_,x,hdx,hxy⟩ := (hComp d y).mp hdy
      exact ⟨x,(hD.1 x).mpr ⟨d,hd,hdx⟩,hxy⟩
    · rintro ⟨x,hx,hxy⟩
      obtain ⟨d,hd,hdx⟩ := (hD.1 x).mp hx
      exact (hDT.1 y).mpr ⟨d,hd,(hComp d y).mpr ⟨hd,x,hdx,hxy⟩⟩
  obtain ⟨nf,hnf,hnGraph,hnOnto⟩ := ForcingLocalNameTransport.exists_graph hM hData hBound hASub hImage
    hD.2.1 hDT.2.1 hD.2.2.1 hDT.2.2.1
  obtain ⟨V,hV⟩ := ForcingSystemFibers.exists_fiber hM (v 0) mul objects maps r O index U
  obtain ⟨VT,hVT⟩ := ForcingSystemFibers.exists_fiber hM (v 0) mul targets targetMaps rT OT index U
  obtain ⟨f,hf,hFRes,hfOnto⟩ := ForcingReindexSystem.fiber_bijection hM hAppMap hApps hPres hComp hr hrT hApp hV hVT
  have hVF : ForcingComponentFibers.VertexFiber (v 0) mul objects maps vertex V := ⟨r,index,U,O,hCode,hr,hV⟩
  have hVFT : ForcingComponentFibers.VertexFiber (v 0) mul targets targetMaps vertexT VT := ⟨rT,index,U,OT,hCodeT,hrT,hVT⟩
  have hFM : ForcingGluedTransport.FiberMove (v 0) mul pi objects maps targets targetMaps apps vertex vertexT V VT f :=
    ⟨r,index,U,rT,O,OT,app,hCode,hCodeT,hComp,hr,hrT,hApp,hV,hVT,hFRes,hf,hfOnto⟩
  have hFqEdge : ∀ x y, PureKuratowski.PairMember M x y f → PureKuratowski.PairMember M x y fq :=
    fun x y hxy => ((hRes x y).mp ((hFRes x y).mp hxy).1).1
  rw [at_iff_row hM hCodeT hDT hrT hVT,at_iff_row hM hCode hD hr hV]
  constructor
  · rintro ⟨hCT,y,hy,hsy,p,hp,hpb⟩
    have hC := hCommon.mp hCT
    obtain ⟨x,hx,hxy⟩ := hfOnto y hy
    obtain ⟨sigma',hsigma',hst⟩ := hnOnto sigmaT (ForcingConditionGraphs.function_input hDT.2.2.2.1.1 hsy)
    have hn' := ForcingHS.isName ((hD.2.2.1 sigma').mp hsigma').1.1
    have he := ForcingNameConjugacy.injective hM hc.2.2.1 hn' hName ((hnGraph sigma' sigmaT).mp hst).2 hAct
    subst sigma'
    obtain ⟨x',hsx',_⟩ := hD.2.2.2.1.1.2 sigma hsigma'
    have he := hFq.2 x' x y ((hGraph x' y).mpr ⟨sigma,sigmaT,hsx',hAct,hsy⟩) (hFqEdge x y hxy)
    subst x'
    obtain ⟨bt,hbt,_,_⟩ := hAll vertex V hC hVF
    obtain ⟨ct,hct,_,_⟩ := hAllT vertexT VT hCT hVFT
    obtain ⟨b',hxb',_⟩ := hbt.1.1.2 x hx
    have hybT := (hct.2 y bT).mpr ⟨hy,p,hp,hpb⟩
    have hb'bT := hNat vertex vertexT V VT f bt ct x y b' bT hC
      ⟨r,index,U,rT,hCode,hCodeT,hrI,hrTI,hComp⟩ hVF hVFT hFM hbt hct hxb' hxy hybT
    have he := hPhi.2 b' b bT hb'bT hbbT
    subst b'
    exact ⟨hC,x,hx,hsx',((hbt.2 x b).mp hxb').2⟩
  · rintro ⟨hC,x,hx,hsx,p,hp,hpb⟩
    have hCT := hCommon.mpr hC
    have hsigma := ForcingConditionGraphs.function_input hD.2.2.2.1.1 hsx
    have hst := (hnGraph sigma sigmaT).mpr ⟨hsigma,hAct⟩
    obtain ⟨y,hsy,_⟩ := hDT.2.2.2.1.1.2 sigmaT (hnf.1.2 sigma sigmaT hst)
    obtain ⟨y',hxy',_⟩ := hf.1.1.2 x hx
    have he := ForcingConditionGraphs.function_unique hFq.1.1
      ((hGraph x y).mpr ⟨sigma,sigmaT,hsx,hAct,hsy⟩) (hFqEdge x y' hxy')
    subst y'
    have hy := hf.1.2 x y hxy'
    obtain ⟨bt,hbt,_,_⟩ := hAll vertex V hC hVF
    obtain ⟨ct,hct,_,_⟩ := hAllT vertexT VT hCT hVFT
    obtain ⟨bT',hybT',_⟩ := hct.1.1.2 y hy
    have hxb := (hbt.2 x b).mpr ⟨hx,p,hp,hpb⟩
    have hbbT' := hNat vertex vertexT V VT f bt ct x y b bT' hC
      ⟨r,index,U,rT,hCode,hCodeT,hrI,hrTI,hComp⟩ hVF hVFT hFM hbt hct hxb hxy' hybT'
    have he := ForcingConditionGraphs.function_unique hPhi.1.1 hbbT' hbbT
    subst bT'
    exact ⟨hCT,y,hy,hsy,((hct.2 y bT).mp hybT').2⟩

def transportSentence {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi q q))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) objImage))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targets (rho 4) targetImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family R Hdom base rho G F mul g q bound labels E (rho 4) objects))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family R Hdom base rho G F mul gT q bound labels E (rho 4) targets))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo apps (rho 4) appImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleReindex.family R Hdom base rho G F mul g gT q bound labels E pi act apps))
    (.imp (ForcingReindexSystem.preservesAvailability (rho 0) mul pi objects maps targets targetMaps apps)
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q objects maps root Q gluePr)
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q targets targetMaps root Z gluePrT)
    (.imp (ForcingGluedTransport.naturality (rho 0) I mul q pi objects maps targets targetMaps apps root Q Z gluePr gluePrT phi)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection phi Q Z))
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi root rootT)
    (.imp (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root rootT)
    (.imp (ForcingComponentMove.move (rho 0) I mul q pi vertex vertexT)
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) sigma))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) act sigma sigmaT))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge phi b bT))
    (.iff (ForcingTailCodes.atName R Hdom base rho I G F mul gT q bound labels E targets targetMaps root gluePrT vertexT sigmaT bT)
      (ForcingTailCodes.atName R Hdom base rho I G F mul g q bound labels E objects maps root gluePr vertex sigma b)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingReindexSystem.preservesAvailability_freeClosed,
      ForcingComponentGluing.allFiberMaps_freeClosed,ForcingGluedTransport.naturality_freeClosed,
      ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,ForcingTailCodes.atName_freeClosed]

theorem transport_models {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (transportSentence R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (transportSentence R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro boundEnv
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleFamily.family_semantics (M := M),
    ForcingEligibleReindex.family_semantics (M := M),ForcingReindexSystem.preservesAvailability_semantics hM,
    ForcingComponentGluing.allFiberMaps_semantics hM,ForcingGluedTransport.naturality_semantics hM,
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    ForcingNames.isName_semantics (M := M),ForcingStabilizer.action_semantics (M := M),KuratowskiZF.source_edge,
    ForcingTailCodes.atName_semantics hM]
  exact at_transport_iff hM (R := R) (Hdom := Hdom)
    (env := fun j => boundEnv (base j)) (v := fun j => boundEnv (rho j))

theorem transport_kernel_certificate {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (transportSentence R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT)) :=
  ModelTransfer.derives (fun _ hM => transport_models R Hdom base rho I K B w G F mu pi inv c act ai mul e g gT q bound labels E objects maps targets targetMaps objImage targetImage appImage apps root rootT vertex vertexT gluePr gluePrT Q Z phi sigma sigmaT b bT hM)

end PPAC.Migration.ForcingTailTransport
