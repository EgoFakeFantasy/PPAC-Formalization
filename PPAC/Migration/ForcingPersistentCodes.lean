/- Pinned PersistentCodes.Same and same_refl/symm/trans/mono:129-167.
Actual internal chain, code-function values and Product/WithTop EqF are retained.
The only thresholds are members of the model's own omega. -/
import PPAC.Migration.ForcingPrincipalFilter
import PPAC.Migration.ForcingTailCovariance
import PPAC.Migration.ForcingPersistentSelection

namespace PPAC.Migration.ForcingPersistentCodes
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingProductFamily (Presentation)
open ForcingProductSymmetry (orderFormula)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain)
open ConstructionFractionOrder (NatLe)
open ForcingPrincipalFilter (EqF)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Same {k : Nat} (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (W w chain d a b : M.Carrier .set) : Prop :=
  ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ i,
    (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
    ∃ vertex sigma tau r index U,
      PureKuratowski.PairMember M i vertex chain ∧ PureKuratowski.PairMember M i sigma a ∧
      PureKuratowski.PairMember M i tau b ∧ Code vertex r index U ∧ EqF R env W d r sigma tau

theorem chain_diagram {w D I mul q zero root vertices chain i vertex r index U : M.Carrier .set}
    (hChain : Chain w D I mul q zero root vertices chain)
    (hv : PureKuratowski.PairMember M i vertex chain) (hc : Code vertex r index U) : Injection D I r := by
  obtain ⟨_,_,_,r',index',U',_,hc',_,hr',_⟩ := hChain.2.2.2.1 i vertex hv
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  exact hr'.1

theorem same_refl (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e d q zero root vertices chain names a : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (ha : MapsTo w names a) (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3))) :
    Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a a := by
  obtain ⟨z,_,hz⟩ := hw.1.1
  refine ⟨z,hz,?_⟩
  intro i hi _
  obtain ⟨vertex,hv,_⟩ := hChain.1.1.2 i hi
  obtain ⟨sigma,hs,_⟩ := ha.1.2 i hi
  obtain ⟨_,_,_,r,index,U,_,hc,_,hr,_⟩ := hChain.2.2.2.1 i vertex hv
  exact ⟨vertex,sigma,sigma,r,index,U,hv,hs,hs,hc,
    ForcingPrincipalFilter.eqF_refl hM env rho mul hm hp hd hr.1 sigma⟩

theorem same_symm (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {env : Fin k → M.Carrier .set} {W w chain d a b : M.Carrier .set}
    (h : Same R env W w chain d a b) : Same R env W w chain d b a := by
  obtain ⟨N,hN,h⟩ := h
  refine ⟨N,hN,?_⟩
  intro i hi hNi
  obtain ⟨vertex,sigma,tau,r,index,U,hv,hs,ht,hc,he⟩ := h i hi hNi
  exact ⟨vertex,tau,sigma,r,index,U,hv,ht,hs,hc,ForcingPrincipalFilter.eqF_symm hM he⟩

theorem same_trans (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w e d q zero root vertices chain names a b c : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (hb : MapsTo w names b) (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hab : Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a b)
    (hbc : Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d b c) :
    Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a c := by
  obtain ⟨N,hN,hab⟩ := hab
  obtain ⟨L,hL,hbc⟩ := hbc
  have hmax : ∃ J, (Project.FirstOrderSemantics.reduct M).mem J w ∧ NatLe N J ∧ NatLe L J := by
    rcases ConstructionFractionOrder.nat_compare hM hw hN hL with he | hn | hl
    · exact ⟨L,hL,Or.inl he,Or.inl rfl⟩
    · exact ⟨L,hL,Or.inr hn,Or.inl rfl⟩
    · exact ⟨N,hN,Or.inl rfl,Or.inr hl⟩
  obtain ⟨J,hJ,hNJ,hLJ⟩ := hmax
  refine ⟨J,hJ,?_⟩
  intro i hi hJi
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM) i hi
  obtain ⟨vertex,sigma,tau,r,index,U,hv,hs,ht,hcode,he⟩ := hab i hi (ZF.eqOrMem_trans ord hNJ hJi)
  obtain ⟨vertex',tau',upsilon,r',index',U',hv',ht',hu,hcode',he'⟩ := hbc i hi (ZF.eqOrMem_trans ord hLJ hJi)
  have hvertex := ForcingConditionGraphs.function_unique hChain.1.1 hv hv'
  have htau := ForcingConditionGraphs.function_unique hb.1 ht ht'
  subst vertex'; subst tau'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hcode hcode'
  exact ⟨vertex,sigma,upsilon,r,index,U,hv,hs,hu,hcode,
    ForcingPrincipalFilter.eqF_trans hM env rho mul hm hp hd (chain_diagram hChain hv hcode) he he'⟩

theorem same_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one d e q zero root vertices chain a b : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3))) (hde : ForcingPowerName.Subset d e)
    (hab : Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a b) :
    Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain e a b := by
  obtain ⟨N,hN,hab⟩ := hab
  refine ⟨N,hN,?_⟩
  intro i hi hNi
  obtain ⟨vertex,sigma,tau,r,index,U,hv,hs,ht,hc,hf⟩ := hab i hi hNi
  exact ⟨vertex,sigma,tau,r,index,U,hv,hs,ht,hc,
    ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he (chain_diagram hChain hv hc) hde hf⟩


def same {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (W w chain d a b : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound w.succ))
    (.forallE (.imp (.mem (.bound 0) (.bound w.succ.succ))
      (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0)))
        (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
          (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ.succ.succ.succ.succ.succ.succ 6 5))
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge a.succ.succ.succ.succ.succ.succ.succ.succ 6 4))
              (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge b.succ.succ.succ.succ.succ.succ.succ.succ 6 3))
                (.conj (ConstructionComponentCarrier.code 5 2 1 0)
                  (ForcingPrincipalFilter.eqF R (fun j => (base j).succ.succ.succ.succ.succ.succ.succ.succ)
                    W.succ.succ.succ.succ.succ.succ.succ.succ d.succ.succ.succ.succ.succ.succ.succ.succ 2 4 3)))))))))))))))

theorem same_freeClosed {k m : Nat} (R : Formula (k+2)) (base : Fin k → Fin m)
    (W w chain d a b : Fin m) : (same R base W w chain d a b).FreeClosed := by
  simp [same,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCarrier.code_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem same_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (base : Fin k → Fin m)
    (W w chain d a b : Fin m) : Project.Formula.satisfies env (same R base W w chain d a b) ↔
      Same R (fun j => env.bound (base j)) (env.bound W) (env.bound w) (env.bound chain) (env.bound d) (env.bound a) (env.bound b) := by
  simp only [same,Same,NatLe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,ForcingPrincipalFilter.eqF_semantics hM]
  rfl

def lawsSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mul one q zero root vertices chain names a b c d e : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
        (.imp (Project.Formula.isOmega (.bound w))
          (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
            (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo a w names))
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo b w names))
                (.imp (.mem (.bound d) (.bound (rho 3)))
                  (.imp (.mem (.bound e) (.bound (rho 3)))
                    (.imp (Project.Formula.subset (.bound d) (.bound e))
                      (.conj (same (orderFormula (rho 0) mul) id (rho 6) w chain d a a)
                        (.conj (.imp (same (orderFormula (rho 0) mul) id (rho 6) w chain d a b)
                          (same (orderFormula (rho 0) mul) id (rho 6) w chain d b a))
                          (.conj (.imp (same (orderFormula (rho 0) mul) id (rho 6) w chain d a b)
                            (.imp (same (orderFormula (rho 0) mul) id (rho 6) w chain d b c)
                              (same (orderFormula (rho 0) mul) id (rho 6) w chain d a c)))
                            (.imp (same (orderFormula (rho 0) mul) id (rho 6) w chain d a b)
                              (same (orderFormula (rho 0) mul) id (rho 6) w chain e a b))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCofinal.chain_freeClosed,same_freeClosed]
    exact Project.Formula.isOmega_freeClosed _ rfl

theorem laws_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mul one q zero root vertices chain names a b c d e : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (lawsSentence rho I K B w mul one q zero root vertices chain names a b c d e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),same_semantics hM]
  intro hm hp hw hChain ha hb hd he hde
  exact ⟨same_refl hM env rho mul hm hp hw hChain ha hd,
    same_symm hM,fun hab hbc => same_trans hM env rho mul hm hp hw hChain hb hd hab hbc,
    fun hab => same_mono hM env rho mul hm hp hChain he hde hab⟩

theorem laws_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mul one q zero root vertices chain names a b c d e : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (lawsSentence rho I K B w mul one q zero root vertices chain names a b c d e)) :=
  ModelTransfer.derives (fun _ hM => laws_models rho I K B w mul one q zero root vertices chain names a b c d e hM)


theorem at_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one G F g q bound labels E objects maps root gluePr Q vertex sigma tau x y r index U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hg : ForcingLocalAtomic.CohenFilter (env (rho 3)) g)
    (hAll : ForcingComponentGluing.AllFiberMaps (env (rho 0)) I (env mul) q objects maps root Q gluePr)
    (hc : Code vertex r index U)
    (hx : ForcingTailCodes.At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr vertex sigma x)
    (hy : ForcingTailCodes.At (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr vertex tau y) :
    x = y ↔ ForcingLocalAtomic.EqG (orderFormula (rho 0) mul) env (env (rho 6)) g r sigma tau := by
  obtain ⟨r',index',U',A,H,X,T,pr,O,V,u,p,hCommon,hc',hD,hr,hV,hu,hs,hpu,hpx⟩ := hx
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
  obtain ⟨_,v,hv,ht,p',hpv,hpy⟩ := (ForcingTailTransport.at_iff_row hM hc hD hr hV).mp hy
  obtain ⟨f,hf,hinj,_⟩ := hAll vertex V hCommon ⟨r,index,U,O,hc,hr,hV⟩
  have hux := (hf.2 u x).mpr ⟨hu,p,hpu,hpx⟩
  have hvy := (hf.2 v y).mpr ⟨hv,p',hpv,hpy⟩
  have hxy : x = y ↔ u = v := by
    constructor
    · intro he
      subst y
      exact hinj.2 u v x hux hvy
    · intro he
      subst v
      exact ForcingConditionGraphs.function_unique hf.1.1 hux hvy
  have hri : Injection (env (rho 0)) I r := by
    obtain ⟨_,_,_,r'',index'',U'',_,hc'',_,hv',_⟩ := hCommon
    obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc''
    exact hv'.1
  exact hxy.trans (ForcingLocalQuotient.equality_law hM env rho mul hm hp hg hri hD.2.2.2.2.2.1 sigma tau u v hs ht)

theorem same_iff_represents_eq (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (mul : Fin k)
    {I K B w one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hg : ForcingPrincipalFilter.Principal (env (rho 3)) d g)
    (hChain : Chain w (env (rho 0)) I (env mul) q zero root vertices chain)
    (ha : MapsTo w names a) (hb : MapsTo w names b)
    (hAll : ForcingComponentGluing.AllFiberMaps (env (rho 0)) I (env mul) q objects maps root Q gluePr)
    (hx : ForcingTailCodes.Represents (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr w chain a x)
    (hy : ForcingTailCodes.Represents (orderFormula (rho 0) mul) Hdom env (fun j => env (rho j)) I G F (env mul) g q bound labels E objects maps root gluePr w chain b y) :
    Same (orderFormula (rho 0) mul) env (env (rho 6)) w chain d a b ↔ x = y := by
  obtain ⟨N,hN,hx⟩ := hx
  obtain ⟨L,hL,hy⟩ := hy
  have hiff : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i → NatLe L i →
      (x = y ↔ ∃ vertex sigma tau r index U,
        PureKuratowski.PairMember M i vertex chain ∧ PureKuratowski.PairMember M i sigma a ∧
        PureKuratowski.PairMember M i tau b ∧ Code vertex r index U ∧
        EqF (orderFormula (rho 0) mul) env (env (rho 6)) d r sigma tau) := by
    intro i hi hNi hLi
    obtain ⟨vertex,sigma,hv,hs,hAt⟩ := hx i hi hNi
    obtain ⟨vertex',tau,hv',ht,hAt'⟩ := hy i hi hLi
    have he := ForcingConditionGraphs.function_unique hChain.1.1 hv hv'
    subst vertex'
    have hAtCopy := hAt
    obtain ⟨r,index,U,_,_,_,_,_,_,_,_,_,_,hc,_⟩ := hAtCopy
    have hEq := (at_eq_iff hM Hdom env rho mul hm hp (ForcingPrincipalFilter.principal_filter hd hg) hAll hc hAt hAt').trans
      (ForcingPrincipalFilter.eqG_principal hM env rho mul hm hp hd (chain_diagram hChain hv hc) hg)
    constructor
    · intro heq
      exact ⟨vertex,sigma,tau,r,index,U,hv,hs,ht,hc,hEq.mp heq⟩
    · rintro ⟨vertex',sigma',tau',r',index',U',hv',hs',ht',hc',heq⟩
      have hvv := ForcingConditionGraphs.function_unique hChain.1.1 hv hv'
      have hss := ForcingConditionGraphs.function_unique ha.1 hs hs'
      have htt := ForcingConditionGraphs.function_unique hb.1 ht ht'
      subst vertex'; subst sigma'; subst tau'
      obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hc hc'
      exact hEq.mpr heq
  have join : ∀ n l, (Project.FirstOrderSemantics.reduct M).mem n w → (Project.FirstOrderSemantics.reduct M).mem l w →
      ∃ j, (Project.FirstOrderSemantics.reduct M).mem j w ∧ NatLe n j ∧ NatLe l j := by
    intro n l hn hl
    rcases ConstructionFractionOrder.nat_compare hM hw hn hl with he | hnl | hln
    · exact ⟨l,hl,Or.inl he,Or.inl rfl⟩
    · exact ⟨l,hl,Or.inr hnl,Or.inl rfl⟩
    · exact ⟨n,hn,Or.inl rfl,Or.inr hln⟩
  obtain ⟨J,hJ,hNJ,hLJ⟩ := join N L hN hL
  have ord := hw.members_areOrdinals (ModelTransfer.project_models_iff.mp hM)
  constructor
  · rintro ⟨T,hT,hSame⟩
    obtain ⟨i,hi,hJi,hTi⟩ := join J T hJ hT
    exact (hiff i hi (ZF.eqOrMem_trans (ord i hi) hNJ hJi) (ZF.eqOrMem_trans (ord i hi) hLJ hJi)).mpr (hSame i hi hTi)
  · intro heq
    refine ⟨J,hJ,?_⟩
    intro i hi hJi
    exact (hiff i hi (ZF.eqOrMem_trans (ord i hi) hNJ hJi) (ZF.eqOrMem_trans (ord i hi) hLJ hJi)).mp heq


-- Pinned same_iff_represents_eq: equality in the actual principal-filter gluing.
def equalitySentence {k : Nat} (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I K B w mul one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (ForcingPrincipalFilter.principal (rho 3) d g)
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo a w names))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo b w names))
    (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q objects maps root Q gluePr)
    (.imp (ForcingTailCodes.represents (orderFormula (rho 0) mul) Hdom id rho I G F mul g q bound labels E objects maps root gluePr w chain a x)
    (.imp (ForcingTailCodes.represents (orderFormula (rho 0) mul) Hdom id rho I G F mul g q bound labels E objects maps root gluePr w chain b y)
    (.iff (same (orderFormula (rho 0) mul) id (rho 6) w chain d a b)
      (Project.Formula.extensionalEq (.bound x) (.bound y))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingPrincipalFilter.principal_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingComponentGluing.allFiberMaps_freeClosed,ForcingTailCodes.represents_freeClosed,same_freeClosed]
    exact Project.Formula.isOmega_freeClosed _ rfl

theorem equality_models {k : Nat} (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I K B w mul one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (equalitySentence Hdom rho I K B w mul one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingPrincipalFilter.principal_semantics,ConstructionComponentCofinal.chain_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingComponentGluing.allFiberMaps_semantics hM,
    ForcingTailCodes.represents_semantics hM,same_semantics hM]
  exact same_iff_represents_eq hM Hdom env rho mul

theorem equality_kernel_certificate {k : Nat} (Hdom : Formula (k+1)) (rho : Fin 7 → Fin k)
    (I K B w mul one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (equalitySentence Hdom rho I K B w mul one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y)) :=
  ModelTransfer.derives (fun _ hM => equality_models Hdom rho I K B w mul one d G F g q bound labels E objects maps root gluePr Q zero vertices chain names a b x y hM)

end PPAC.Migration.ForcingPersistentCodes
