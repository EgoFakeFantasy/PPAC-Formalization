/- Pinned CodeLinks.Links and its local laws:171-245,391-400.
All thresholds belong to the model's internal omega. Actual arrows and the
same literal names/conditions are retained; existing forcing/root proofs supply the laws. -/
import PPAC.Migration.ForcingPersistentCodes
import PPAC.Migration.ForcingOrdinalRoot

namespace PPAC.Migration.ForcingCodeLinks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection Small)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain EncodedArrow EncodedCommon)
open ConstructionComponentVertices (Vertex Arrow)
open ConstructionFractionOrder (NatLe)
open ForcingPrincipalFilter (EqF)
open ForcingPersistentCodes (Same)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Links {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W w D I mul q chain d vertex tau a : M.Carrier .set) : Prop :=
  ∃ r index U, Code vertex r index U ∧ ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧
    ∀ i, (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
      ∃ target sigma n, PureKuratowski.PairMember M i target chain ∧ PureKuratowski.PairMember M i sigma a ∧
        EncodedArrow D I mul q vertex target n ∧ EqF R env W d r sigma tau

private theorem at_code {k : Nat} {R : Formula (k+2)} {env : Fin k → M.Carrier .set}
    {W w D I mul q chain d vertex tau a r index U : M.Carrier .set}
    (hc : Code vertex r index U) (h : Links R env W w D I mul q chain d vertex tau a) :
    ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
        ∃ target sigma n, PureKuratowski.PairMember M i target chain ∧ PureKuratowski.PairMember M i sigma a ∧
          EncodedArrow D I mul q vertex target n ∧ EqF R env W d r sigma tau := by
  obtain ⟨r',index',U',hc',h⟩ := h
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  exact h

private theorem arrow_data {D I mul q vertex target n r index U : M.Carrier .set}
    (hc : Code vertex r index U) (h : EncodedArrow D I mul q vertex target n) :
    ∃ s b V, Code target s b V ∧ Vertex D I mul q r index U ∧
      Vertex D I mul q s b V ∧ Arrow D mul r U s V n := by
  obtain ⟨r',index',U',s,b,V,hc',hs,hr,hv,ha⟩ := h
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  exact ⟨s,b,V,hs,hr,hv,ha⟩

private theorem join (hM : FirstOrder.Theory.Models M nativeZF) {w n l : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hl : (Project.FirstOrderSemantics.reduct M).mem l w) :
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j w ∧ NatLe n j ∧ NatLe l j := by
  rcases ConstructionFractionOrder.nat_compare hM hw hn hl with he | hnl | hln
  · exact ⟨l,hl,Or.inl he,Or.inl rfl⟩
  · exact ⟨l,hl,Or.inr hnl,Or.inl rfl⟩
  · exact ⟨n,hn,Or.inl rfl,Or.inr hln⟩

private theorem eq_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one d r s sigma tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) (hr : Injection (env (rho 0)) I r)
    (hle : ForcingDiagramOrder.Le (env (rho 0)) (env mul) r s)
    (h : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d s sigma tau) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau := by
  obtain ⟨z,hz,he⟩ := h
  obtain ⟨t,ht⟩ := ForcingSupportingRoot.exists_code hM d r
  exact ⟨t,ht,ForcingAtomicBasic.eq_mono hM
    (ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2)
    (ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp hd) hr ht)
    ((orderFormula_semantics env (rho 0) mul t z).mpr ((ForcingSupportingRoot.code_le ht hz).mpr
      ⟨fun _ h => h,hle⟩)) he⟩

section Laws
variable (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one q zero root vertices chain names d e vertex tau sigma a b : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)

include hM hm hp in
theorem links_mono
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3))) (hde : ForcingPowerName.Subset d e)
    (h : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a) :
    Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain e vertex tau a := by
  obtain ⟨r,index,U,hc,N,hN,h⟩ := h
  refine ⟨r,index,U,hc,N,hN,?_⟩
  intro i hi hNi
  obtain ⟨target,name,n,hv,hn,ha,hf⟩ := h i hi hNi
  obtain ⟨s,b,V,_,hr,_,_⟩ := arrow_data hc ha
  exact ⟨target,name,n,hv,hn,ha,ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he hr.1 hde hf⟩

include hM hw hChain in
theorem links_common
    (h : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a) :
    EncodedCommon (env (rho 0)) I (env mul) q root vertex := by
  obtain ⟨r,index,U,hc,N,hN,h⟩ := h
  obtain ⟨j,hj,hNj,hzj⟩ := join hM hw hN (ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1)
  obtain ⟨target,name,n,hv,_,ha,_⟩ := h j hj hNj
  obtain ⟨m,hb⟩ := hChain.2.2.1 zero j root target hzj hChain.2.1 hv
  obtain ⟨s,b,V,hs,hr,hv',han⟩ := arrow_data hc ha
  obtain ⟨rr,idx,UR,s',b',V',hcr,hcs,hroot,_,ham⟩ := hb
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hs hcs
  exact ⟨rr,idx,UR,r,index,U,hcr,hc,hroot,hr,s,b,V,m,n,hv',ham,han⟩

include hM hm hp in
theorem links_congr {r index U : M.Carrier .set}
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) (hc : Code vertex r index U)
    (h : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a)
    (he : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r tau sigma) :
    Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex sigma a := by
  obtain ⟨N,hN,h⟩ := at_code hc h
  refine ⟨r,index,U,hc,N,hN,?_⟩
  intro i hi hNi
  obtain ⟨target,name,n,hv,hn,ha,hf⟩ := h i hi hNi
  obtain ⟨s,b,V,_,hr,_,_⟩ := arrow_data hc ha
  exact ⟨target,name,n,hv,hn,ha,ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd hr.1 hf he⟩

include hM hm hp hw hChain in
theorem links_same
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) (ha : MapsTo w names a)
    (h : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a)
    (hsame : Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a b) :
    Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau b := by
  obtain ⟨r,index,U,hc,N,hN,h⟩ := h
  obtain ⟨L,hL,hsame⟩ := hsame
  obtain ⟨J,hJ,hNJ,hLJ⟩ := join hM hw hN hL
  refine ⟨r,index,U,hc,J,hJ,?_⟩
  intro i hi hJi
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) i hi
  obtain ⟨target,name,n,hv,hn,harr,hf⟩ := h i hi (ZF.eqOrMem_trans ord hNJ hJi)
  obtain ⟨target',name',nameB,s,idx,V,hv',hn',hb,hcs,he⟩ := hsame i hi (ZF.eqOrMem_trans ord hLJ hJi)
  have hvv := ForcingConditionGraphs.function_unique hChain.1.1 hv hv'
  have hnn := ForcingConditionGraphs.function_unique ha.1 hn hn'
  subst target'; subst name'
  obtain ⟨s',idx',V',hcs',hr,ht,harr'⟩ := arrow_data hc harr
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hcs hcs'
  have he' := eq_restrict hM env rho mul hm hp hd hr.1 ⟨n,hr.2.2.1 n harr'.1,harr'.2.1⟩
    (ForcingPrincipalFilter.eqF_symm hM he)
  exact ⟨target,nameB,n,hv,hb,harr,ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd hr.1 he' hf⟩

include hM hm hp in
theorem links_restrict {vertex' n : M.Carrier .set}
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hf : EncodedArrow (env (rho 0)) I (env mul) q vertex' vertex n)
    (h : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a) :
    Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex' tau a := by
  obtain ⟨r,index,U,hc,N,hN,h⟩ := h
  obtain ⟨s,b,V,r',index',U',hcs,hc',hs,hr,harr⟩ := hf
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  refine ⟨s,b,V,hcs,N,hN,?_⟩
  intro i hi hNi
  obtain ⟨target,name,m,hv,hn,hg,he⟩ := h i hi hNi
  obtain ⟨t,c,W,hct,_,ht,har⟩ := arrow_data hc hg
  obtain ⟨nm,_,hnm⟩ := (hm.2.1 n (hs.2.2.1 n harr.1)).1 m (hr.2.2.1 m har.1)
  exact ⟨target,name,nm,hv,hn,⟨s,b,V,t,c,W,hcs,hct,hs,ht,ConstructionComponentVertices.compose hm hs hr harr har hnm⟩,
    eq_restrict hM env rho mul hm hp hd hs.1 ⟨n,hs.2.2.1 n harr.1,harr.2.1⟩ he⟩
end Laws

def links {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (W w D I mul q chain d vertex tau a : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE ((.conj (ConstructionComponentCarrier.code vertex.succ.succ.succ 2 1 0) (.existsE ((.conj (.mem (.bound 0) (.bound w.succ.succ.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound w.succ.succ.succ.succ.succ)) (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))) (.existsE (.existsE (.existsE ((.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ.succ.succ.succ.succ.succ.succ 3 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge a.succ.succ.succ.succ.succ.succ.succ.succ 3 1)) (.conj (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ vertex.succ.succ.succ.succ.succ.succ.succ.succ 2 0) (ForcingPrincipalFilter.eqF R (fun j => (base j).succ.succ.succ.succ.succ.succ.succ.succ) W.succ.succ.succ.succ.succ.succ.succ.succ d.succ.succ.succ.succ.succ.succ.succ.succ 7 1 tau.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))

theorem links_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (W w D I mul q chain d vertex tau a : Fin m) : (links R base W w D I mul q chain d vertex tau a).FreeClosed := by
  simp -implicitDefEqProofs [links,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCarrier.code_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed,
    ForcingPrincipalFilter.eqF_freeClosed]

theorem links_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (base : Fin k → Fin m)
    (W w D I mul q chain d vertex tau a : Fin m) :
    Project.Formula.satisfies env (links R base W w D I mul q chain d vertex tau a) ↔
      Links R (fun j => env.bound (base j)) (env.bound W) (env.bound w) (env.bound D) (env.bound I)
        (env.bound mul) (env.bound q) (env.bound chain) (env.bound d) (env.bound vertex) (env.bound tau) (env.bound a) := by
  simp only [links,Links,NatLe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM]
  rfl

section Reflection
variable (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {w mu history kappa e mark H C incoming base I K B : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small (env (rho 0)) mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa (env (rho 0)) (env mul) e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
include hM hChoice hw hMu hI hD hMergers hRow hm hpres hG hF

private theorem reflect_entry {s r index U vertex bound d sigma tau : M.Carrier .set}
    (hr : Injection (env (rho 0)) I r) (hs : Injection (env (rho 0)) I s)
    (hle : ForcingDiagramOrder.Le (env (rho 0)) (env mul) s r)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) (hc : Code vertex r index U)
    (ha : ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) bound vertex sigma)
    (hb : ForcingTailCodes.Entry (fun j => env (rho j)) (env G) (env F) bound vertex tau)
    (he : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d s sigma tau) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau := by
  obtain ⟨r',idx',U',A,fixing,hc',hRange,hFix,ha⟩ := ha
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  obtain ⟨r',idx',U',A',fixing',hc',hRange',hFix',hb⟩ := hb
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  have hAA := (ModelTransfer.extensionality hM).eq_of_same_members A A' (fun z => (hRange z).trans (hRange' z).symm)
  subst A'
  have hHH := ForcingLabelPermutations.fixing_unique hM hFix hFix'
  subst fixing'
  obtain ⟨z,hz,he⟩ := he
  obtain ⟨zr,hzr⟩ := ForcingSupportingRoot.exists_code hM d r
  exact ⟨zr,hzr,ForcingOrdinalRoot.eq_at_root hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF
    hr hRange hFix hs hle ((hpres.2.2.1 d).mp hd) hz hzr ha.2 hb.2 he⟩

theorem links_eq_iff_same {q zero root vertices chain names d vertex r index U bound a b tau sigma : M.Carrier .set}
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) (hc : Code vertex r index U)
    (ha : ForcingTailCodes.ChainCode (fun j => env (rho j)) (env G) (env F) bound w names chain a)
    (hb : ForcingTailCodes.ChainCode (fun j => env (rho j)) (env G) (env F) bound w names chain b)
    (hA : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex tau a)
    (hB : Links (orderFormula (rho 0) mul) env (env (rho 6)) w (env (rho 0)) I (env mul) q chain d vertex sigma b) :
    EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r tau sigma ↔
      Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a b := by
  constructor
  · intro he
    obtain ⟨N,hN,hAt⟩ := at_code hc hA
    obtain ⟨L,hL,hBt⟩ := at_code hc hB
    obtain ⟨J,hJ,hNJ,hLJ⟩ := join hM hw hN hL
    refine ⟨J,hJ,?_⟩
    intro i hi hJi
    have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) i hi
    obtain ⟨target,sa,n,hv,hsa,hArrow,hfa⟩ := hAt i hi (ZF.eqOrMem_trans ord hNJ hJi)
    obtain ⟨target',sb,m,hv',hsb,_,hfb⟩ := hBt i hi (ZF.eqOrMem_trans ord hLJ hJi)
    have hvv := ForcingConditionGraphs.function_unique hChain.1.1 hv hv'
    subst target'
    obtain ⟨t,idx,V,hct,hr,ht,harr⟩ := arrow_data hc hArrow
    obtain ⟨va,hva,hEntryA⟩ := ha.2 i sa hsa
    obtain ⟨vb,hvb,hEntryB⟩ := hb.2 i sb hsb
    have hvA := ForcingConditionGraphs.function_unique hChain.1.1 hv hva
    have hvB := ForcingConditionGraphs.function_unique hChain.1.1 hv hvb
    subst va; subst vb
    have hf := ForcingPrincipalFilter.eqF_trans hM env rho mul hm hpres hd hr.1 hfa
      (ForcingPrincipalFilter.eqF_trans hM env rho mul hm hpres hd hr.1 he (ForcingPrincipalFilter.eqF_symm hM hfb))
    exact ⟨target,sa,sb,t,idx,V,hv,hsa,hsb,hct,
      reflect_entry hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hF ht.1 hr.1
        ⟨n,hr.2.2.1 n harr.1,harr.2.1⟩ hd hct hEntryA hEntryB hf⟩
  · intro hsame
    have hA' := links_same hM env rho mul hm hpres hw hChain hd ha.1 hA hsame
    obtain ⟨N,hN,hAt⟩ := at_code hc hA'
    obtain ⟨L,hL,hBt⟩ := at_code hc hB
    obtain ⟨J,hJ,hNJ,hLJ⟩ := join hM hw hN hL
    obtain ⟨target,sa,n,_,hsa,hArrow,hfa⟩ := hAt J hJ hNJ
    obtain ⟨target',sb,m,_,hsb,_,hfb⟩ := hBt J hJ hLJ
    have hNames := ForcingConditionGraphs.function_unique hb.1.1 hsa hsb
    subst sb
    obtain ⟨_,_,_,_,hr,_,_⟩ := arrow_data hc hArrow
    exact ForcingPrincipalFilter.eqF_trans hM env rho mul hm hpres hd hr.1
      (ForcingPrincipalFilter.eqF_symm hM hfa) hfb
end Reflection

def lawsSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul one q zero root vertices chain names d e vertex vertexT n r index U tau sigma a b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one)) (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6))) (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo a w names)) (.imp (.mem (.bound d) (.bound (rho 3))) (.imp (.mem (.bound e) (.bound (rho 3))) (.imp (Project.Formula.subset (.bound d) (.bound e)) (.imp (ConstructionComponentCarrier.code vertex r index U) (.imp (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau a) (.conj (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex) (.conj (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain e vertex tau a) (.conj (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) d r tau sigma) (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex sigma a)) (.conj (.imp (ForcingPersistentCodes.same (orderFormula (rho 0) mul) id (rho 6) w chain d a b) (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau b)) (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q vertexT vertex n) (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertexT tau a))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,links_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed,
      ForcingPrincipalFilter.eqF_freeClosed,ForcingPersistentCodes.same_freeClosed]

theorem laws_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul one q zero root vertices chain names d e vertex vertexT n r index U tau sigma a b : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (lawsSentence rho I K B w mul one q zero root vertices chain names d e vertex vertexT n r index U tau sigma a b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionComponentCarrier.code_semantics hM,links_semantics hM,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM,ForcingPersistentCodes.same_semantics hM]
  intro hm hp hw hChain ha hd he hde hc hl
  exact ⟨links_common hM env rho mul hw hChain hl,links_mono hM env rho mul hm hp he hde hl,
    fun hf => links_congr hM env rho mul hm hp hd hc hl hf,
    fun hs => links_same hM env rho mul hm hp hw hChain hd ha hl hs,
    fun hf => links_restrict hM env rho mul hm hp hd hf hl⟩

theorem laws_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w mul one q zero root vertices chain names d e vertex vertexT n r index U tau sigma a b : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (lawsSentence rho I K B w mul one q zero root vertices chain names d e vertex vertexT n r index U tau sigma a b)) :=
  ModelTransfer.derives (fun _ hM => laws_models rho I K B w mul one q zero root vertices chain names d e vertex vertexT n r index U tau sigma a b hM)

def equalitySentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu)) (.imp (ConstructionSaturationIndex.hartogs mu I) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu)) (.imp (ConstructionSaturationMergers.allMergers w history kappa) (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one)) (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6))) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G)) (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F)) (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain) (.imp (.mem (.bound d) (.bound (rho 3))) (.imp (ConstructionComponentCarrier.code vertex r index U) (.imp (ForcingTailCodes.chainCode rho G F bound w names chain a) (.imp (ForcingTailCodes.chainCode rho G F bound w names chain b) (.imp (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex tau a) (.imp (links (orderFormula (rho 0) mul) id (rho 6) w (rho 0) I mul q chain d vertex sigma b) (.iff (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) d r tau sigma) (ForcingPersistentCodes.same (orderFormula (rho 0) mul) id (rho 6) w chain d a b)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega_freeClosed,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,links_freeClosed,
      ForcingTailCodes.chainCode_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,ForcingPersistentCodes.same_freeClosed]

theorem equality_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    ForcingTailCodes.chainCode_semantics hM,links_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM,ForcingPersistentCodes.same_semantics hM]
  intro hw hMu hI hD hMergers hRow hm hp hG hF hChain hd hc ha hb hA hB
  exact links_eq_iff_same hM hChoice env rho G F mul hw hMu hI hD hMergers hRow hm hp hG hF
    hChain hd hc ha hb hA hB

theorem equality_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b))) := by
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
  apply ConstructibleGround.relative_models hM (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (equalitySentence rho I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b)).mp
      (equality_models rho I K B w G F mul one mu history kappa mark H C incoming base q zero root vertices chain names bound d vertex r index U tau sigma a b hL hChoice)


end PPAC.Migration.ForcingCodeLinks
