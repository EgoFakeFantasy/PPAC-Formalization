/- Pinned CodeLinks.links_of_represents_at:257 and at_of_represents_links:289.
Use the SAME actual local/glued projections and restriction maps at the supplied
principal filter. Literal names descend by existing local-name inclusion. -/
import PPAC.Migration.ForcingCodeLinks

namespace PPAC.Migration.ForcingCodeLinkRepresentation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedArrow EncodedCommon)
open ConstructionFractionOrder (NatLe)
open ForcingPrincipalFilter (EqF)
open ForcingTailCodes (At Represents Entry)
open ForcingCodeLinks (Links)
open ForcingEligibleFamily (Data)
open ForcingComponentFibers (VertexFiber ArrowMap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem join (hM : FirstOrder.Theory.Models M nativeZF) {w n l : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hl : (Project.FirstOrderSemantics.reduct M).mem l w) :
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j w ∧ NatLe n j ∧ NatLe l j := by
  rcases ConstructionFractionOrder.nat_compare hM hw hn hl with he | hnl | hln
  · exact ⟨l,hl,Or.inl he,Or.inl rfl⟩
  · exact ⟨l,hl,Or.inr hnl,Or.inl rfl⟩
  · exact ⟨n,hn,Or.inl rfl,Or.inr hln⟩

section Bridge
variable (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat} (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one G F g q bound labels E objects maps root gluePr Q diagrams objImage S mapImage : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hObjFamily : ForcingEligibleFamily.Family (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) G F (env mul) g q bound labels E diagrams objects)
    (hMapFamily : ForcingEligibleMapFamily.Family (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) G F (env mul) g q bound labels E S maps)
    (hCoh : ForcingComponentFibers.Coherent (env (rho 0)) I (env mul) q objects maps)
    (hAll : ForcingComponentGluing.AllFiberMaps (env (rho 0)) I (env mul) q objects maps root Q gluePr)
    (hComm : ForcingComponentGluing.Commuting (env (rho 0)) I (env mul) q objects maps Q gluePr)

include hM hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm in
private theorem at_restrict {v target n name cls : M.Carrier .set}
    (hCommon : EncodedCommon (env (rho 0)) I (env mul) q root v)
    (hArrow : EncodedArrow (env (rho 0)) I (env mul) q v target n)
    (hAt : At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr target name cls) :
    At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr v name cls := by
  obtain ⟨r,index,U,s,idx,V,hcv,hct,hv,ht,harr⟩ := hArrow
  obtain ⟨s',idx',V',At,Ht,Xt,Qt,pt,Ot,Y,y,p,hCt,hct',hDt,hst,hY,hy,hny,hpcode,hpcls⟩ := hAt
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hct hct'
  obtain ⟨Os,hrs,_⟩ := hObj.1.2 r ((hDiagrams r).mpr hv.1)
  obtain ⟨As,Hs,Xs,Qs,ps,hDs⟩ := ((hObjFamily r Os).mp hrs).2
  obtain ⟨X,hX⟩ := ForcingSystemFibers.exists_fiber hM (env (rho 0)) (env mul) objects maps r Os index U
  have hvX : VertexFiber (env (rho 0)) (env mul) objects maps v X := ⟨r,index,U,Os,hcv,hrs,hX⟩
  have htY : VertexFiber (env (rho 0)) (env mul) objects maps target Y := ⟨s,idx,V,Ot,hct,hst,hY⟩
  obtain ⟨ar,har⟩ := hCoh.1 v target n X Y ⟨r,index,U,s,idx,V,hcv,hct,hv,ht,harr⟩ hvX htY
  have harCopy := har
  obtain ⟨r',index',U',s',idx',V',z,f,hcv',hct',hz,hf,hRestr,hInj,_⟩ := harCopy
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hcv hcv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hct hct'
  obtain ⟨x,hyx,_⟩ := hInj.1.1.2 y hy
  have hx := hInj.1.2 y x hyx
  obtain ⟨s',r',At',Ht',Xt',Qt',pt',Ot',As',Hs',Xs',Qs',ps',Os',fq,hz',hDt',hDs',hfq,hQuot,hfObj,hObjRestr⟩ := ((hMapFamily z f).mp hf).2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hDt hDt'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hDs hDs'
  have hRange : ForcingPowerName.Subset At As := fun z hz => (hDs.1 z).mpr
    (ConstructionDescentPlacement.range_antitone ⟨n,hv.2.2.1 n harr.1,harr.2.1⟩ ((hDt.1 z).mp hz))
  have hNames := ForcingLocalNames.restrict_name hDt.2.1 hDs.2.1 hRange hDt.2.2.1 hDs.2.2.1
  obtain ⟨x',hnx',_⟩ := hDs.2.2.2.1.1.2 name (hNames name (ForcingConditionGraphs.function_input hDt.2.2.2.1.1 hny))
  have hyx' := ForcingLocalRestriction.restrict_ofName hQuot hny hnx'
  have hyxq := ((hObjRestr y x).mp ((hRestr y x).mp hyx).1).1
  have hxx := ForcingConditionGraphs.function_unique hfq.1 hyx' hyxq
  subst x'
  obtain ⟨fg,hfg,_,_⟩ := hAll v X hCommon hvX
  obtain ⟨tg,htg,_,_⟩ := hAll target Y hCt htY
  obtain ⟨cls',hxcls',_⟩ := hfg.1.1.2 x hx
  have hycls := (htg.2 y cls).mpr ⟨hy,p,hpcode,hpcls⟩
  have hcc := hComm v target X Y n ar fg tg x y cls' cls hvX htY
    ⟨r,index,U,s,idx,V,hcv,hct,hv,ht,harr⟩ har hfg htg hyx hxcls' hycls
  subst cls'
  obtain ⟨_,p',hp',hpcls'⟩ := (hfg.2 x cls).mp hxcls'
  exact ⟨r,index,U,As,Hs,Xs,Qs,ps,Os,X,x,p',hCommon,hcv,hDs,hrs,hX,hx,hnx',hp',hpcls'⟩

include hM hm hp in
private theorem at_congr {d v r index U sigma tau cls : M.Carrier .set}
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hg : ForcingPrincipalFilter.Principal (env (rho 3)) d g) (hc : Code v r index U)
    (hEntry : Entry (fun j => env (rho j)) G F bound v tau)
    (hAt : At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr v sigma cls)
    (he : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau) :
    At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr v tau cls := by
  obtain ⟨r',index',U',A,H,X,T,pr,O,V,x,p,hCommon,hc',hD,hr,hV,hx,hs,hpx,hpc⟩ := hAt
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  obtain ⟨r',index',U',A',H',hc',hA',hH',hn⟩ := hEntry
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  have hAA := (ModelTransfer.extensionality hM).eq_of_same_members A A' (fun z => (hD.1 z).trans (hA' z).symm)
  subst A'
  have hHH := ForcingLabelPermutations.fixing_unique hM hD.2.1 hH'
  subst H'
  obtain ⟨x',ht,_⟩ := hD.2.2.2.1.1.2 tau ((hD.2.2.1 tau).mpr hn)
  have hri : Injection (env (rho 0)) I r := by
    obtain ⟨_,_,_,r',index',U',_,hc',_,hv,_⟩ := hCommon
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
    exact hv.1
  have hxx := (ForcingLocalQuotient.equality_law hM env rho mul hm hp (ForcingPrincipalFilter.principal_filter hd hg)
    hri hD.2.2.2.2.2.1 sigma tau x x' hs ht).mpr ((ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd hri hg).mpr he)
  subst x'
  exact ⟨r,index,U,A,H,X,T,pr,O,V,x,p,hCommon,hc,hD,hr,hV,hx,ht,hpx,hpc⟩

variable {zero vertices chain names d vertex tau a cls : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hg : ForcingPrincipalFilter.Principal (env (rho 3)) d g)

include hM hm hp hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm hw hChain hd hg in
theorem links_of_represents_at
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) I (env mul) q vertices)
    (hRep : Represents (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr w chain a cls)
    (hAt : At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr vertex tau cls) :
    Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a := by
  have hAtCopy := hAt
  obtain ⟨r,index,U,_,_,_,_,_,_,_,_,_,hCommon,hc,_⟩ := hAtCopy
  have hv : ConstructionComponentVertices.Vertex (env (rho 0)) I (env mul) q r index U := by
    obtain ⟨_,_,_,r',index',U',_,hc',_,hv,_⟩ := hCommon
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
    exact hv
  obtain ⟨L,target,n,hL,hTarget,hArrow⟩ := hChain.2.2.2.2 vertex ((hVertices vertex).mpr ⟨r,index,U,hc,hv⟩) hCommon
  obtain ⟨N,hN,hRep⟩ := hRep
  obtain ⟨J,hJ,hNJ,hLJ⟩ := join hM hw hN hL
  refine ⟨r,index,U,hc,J,hJ,?_⟩
  intro i hi hJi
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) i hi
  obtain ⟨vi,sigma,hvi,hsi,hAti⟩ := hRep i hi (ZF.eqOrMem_trans ord hNJ hJi)
  obtain ⟨m,hIncreasing⟩ := hChain.2.2.1 L i target vi (ZF.eqOrMem_trans ord hLJ hJi) hTarget hvi
  obtain ⟨nm,hComposite⟩ := ForcingComponentMatches.arrow_comp hm hArrow hIncreasing
  have hRestricted := at_restrict hM Hdom env rho mul hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm hCommon hComposite hAti
  have he := (ForcingPersistentCodes.at_eq_iff hM Hdom env rho mul hm hp (ForcingPrincipalFilter.principal_filter hd hg) hAll hc hRestricted hAt).mp rfl
  exact ⟨vi,sigma,nm,hvi,hsi,hComposite,(ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd hv.1 hg).mp he⟩

include hM hm hp hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm hw hChain hd hg in
theorem at_of_represents_links
    (ha : MapsTo w names a)
    (hEntry : Entry (fun j => env (rho j)) G F bound vertex tau)
    (hRep : Represents (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr w chain a cls)
    (hLinks : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a) :
    At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr vertex tau cls := by
  have hCommon := ForcingCodeLinks.links_common hM env rho mul hw hChain hLinks
  obtain ⟨r,index,U,hc,L,hL,hLinks⟩ := hLinks
  obtain ⟨N,hN,hRep⟩ := hRep
  obtain ⟨J,hJ,hNJ,hLJ⟩ := join hM hw hN hL
  obtain ⟨vi,sigma,hvi,hsi,hAti⟩ := hRep J hJ hNJ
  obtain ⟨vi',sigma',n,hvi',hsi',hArrow,he⟩ := hLinks J hJ hLJ
  have hvv := ForcingConditionGraphs.function_unique hChain.1.1 hvi hvi'
  have hss := ForcingConditionGraphs.function_unique ha.1 hsi hsi'
  subst vi'; subst sigma'
  have hRestricted := at_restrict hM Hdom env rho mul hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm hCommon hArrow hAti
  exact at_congr hM Hdom env rho mul hm hp hd hg hc hEntry hRestricted he

end Bridge


/- The auxiliary coherence and gluing laws are obtained from the existing
actual System and its literal quotient here, not added as endpoint premises. -/
def constructionSentence {k : Nat} (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I K B w mul one G F g q bound labels E diagrams objImage objects S mapImage maps root P Q gluePr zero vertices chain names d vertex tau a cls : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) Hdom id rho G F mul g q bound labels E diagrams objects))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) Hdom id rho G F mul g q bound labels E S maps))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage))
    (.imp (ForcingEligibleSystem.system (rho 0) objects maps)
    (.imp (ForcingComponentGluing.component (rho 0) I mul q objects maps root P)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo gluePr P Q))
    (.imp (ForcingComponentGluing.classes (rho 0) I mul q objects maps P Q)
    (.imp (ForcingComponentGluing.projection (rho 0) I mul q objects maps P gluePr)
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ForcingPrincipalFilter.principal (rho 3) d g)
    (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a)
    (.imp (ForcingTailCodes.entry rho G F bound vertex tau)
    (.imp (ForcingTailCodes.represents (orderFormula (rho 0) mul) Hdom id rho I G F mul g q bound labels E objects maps root gluePr w chain a cls)
    (.iff (ForcingTailCodes.atName (orderFormula (rho 0) mul) Hdom id rho I G F mul g q bound labels E objects maps root gluePr vertex tau cls) (ForcingCodeLinks.links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau a))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingComponentGluing.component_freeClosed,
      ForcingComponentGluing.classes_freeClosed,ForcingComponentGluing.projection_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingPrincipalFilter.principal_freeClosed,ForcingTailCodes.chainCode_freeClosed,
      ForcingTailCodes.entry_freeClosed,ForcingTailCodes.represents_freeClosed,
      ForcingTailCodes.atName_freeClosed,ForcingCodeLinks.links_freeClosed]

theorem construction_models {k : Nat} (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I K B w mul one G F g q bound labels E diagrams objImage objects S mapImage maps root P Q gluePr zero vertices chain names d vertex tau a cls : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence Hdom rho I K B w mul one G F g q bound labels E diagrams objImage objects S mapImage maps root P Q gluePr zero vertices chain names d vertex tau a cls)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),ForcingEligibleMapFamily.family_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    ForcingComponentGluing.component_semantics hM,ForcingComponentGluing.classes_semantics hM,
    ForcingComponentGluing.projection_semantics hM,ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ForcingPrincipalFilter.principal_semantics,
    ForcingTailCodes.chainCode_semantics hM,ForcingTailCodes.entry_semantics hM,
    ForcingTailCodes.represents_semantics hM,ForcingTailCodes.atName_semantics hM,ForcingCodeLinks.links_semantics hM]
  intro hm hp hw hJ hDiagrams hObj hObjFamily hMapFamily hS hMaps hSys hP hpr hQ hProjection hVertices hChain hd hg ha hEntry hRep
  have hCoh := ForcingComponentFibers.coherent_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := env q)
  obtain ⟨hAll,hComm⟩ := ForcingComponentGluing.gluing_laws hM hm hJ hDiagrams hObj hS hMaps hSys hP hpr hQ hProjection
  exact ⟨links_of_represents_at hM Hdom env rho mul hm hp hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm hw hChain hd hg hVertices hRep,
    at_of_represents_links hM Hdom env rho mul hm hp hDiagrams hObj hObjFamily hMapFamily hCoh hAll hComm hw hChain hd hg ha.1 hEntry hRep⟩

theorem construction_kernel_certificate {k : Nat} (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I K B w mul one G F g q bound labels E diagrams objImage objects S mapImage maps root P Q gluePr zero vertices chain names d vertex tau a cls : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence Hdom rho I K B w mul one G F g q bound labels E diagrams objImage objects S mapImage maps root P Q gluePr zero vertices chain names d vertex tau a cls)) :=
  ModelTransfer.derives (fun _ hM => construction_models Hdom rho I K B w mul one G F g q bound labels E diagrams objImage objects S mapImage maps root P Q gluePr zero vertices chain names d vertex tau a cls hM)

end PPAC.Migration.ForcingCodeLinkRepresentation
