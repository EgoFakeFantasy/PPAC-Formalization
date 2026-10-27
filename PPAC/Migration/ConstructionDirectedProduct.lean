/- Pinned DirectLimit.mul_def / ConservativeLimit.of.map_mul and actual
multiplication used by DirectLimits:32-60. SAME common-future carrier and
projection. Well-definedness follows from original stage map_mul plus
common-future equality; NO transition injectivity or chosen representatives. -/
import PPAC.Migration.ConstructionDirectedMonoidData

namespace PPAC.Migration.ConstructionDirectedProduct
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family ProductAt HomLaws)
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (J Domains Muls projection a b c : M.Carrier .set) : Prop :=
  ∃ i x y z, ProductAt J Domains Muls i x y z ∧ Product projection i x a ∧
    Product projection i y b ∧ Product projection i z c

def Graph (J Domains Muls projection G : M.Carrier .set) : Prop :=
  ∀ a b c, Product G a b c ↔ Value J Domains Muls projection a b c

/-- Unchanged source common-future test, at a specified later stage. -/
theorem equal_after {J E Domains F i j k t x y z xx yy : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t J)
    (hik : PureKuratowski.PairMember M i k E) (hjk : PureKuratowski.PairMember M j k E)
    (hkt : PureKuratowski.PairMember M k t E)
    (hxz : Transition J Domains F i k x z) (hyz : Transition J Domains F j k y z)
    (hxx : Transition J Domains F i t x xx) (hyy : Transition J Domains F j t y yy) : xx = yy := by
  obtain ⟨zz,hzz⟩ := hT.1 k t z hxz.2.1 ht hkt
  have hit := hE.2.1 i k t hxz.1.1 hxz.2.1.1 ht hik hkt
  have hjt := hE.2.1 j k t hyz.1.1 hyz.2.1.1 ht hjk hkt
  have he1 := hT.2.1 i t x xx zz hit hxx (hT.2.2.2 i k t x z zz hik hkt hxz hzz)
  have he2 := hT.2.1 j t y yy zz hjt hyy (hT.2.2.2 j k t y z zz hjk hkt hyz hzz)
  exact he1.trans he2.symm

theorem value_members {J Domains Muls C L projection a b c : M.Carrier .set}
    (hp : MapsTo C L projection) (hv : Value J Domains Muls projection a b c) :
    (Project.FirstOrderSemantics.reduct M).mem a L ∧ (Project.FirstOrderSemantics.reduct M).mem b L ∧
      (Project.FirstOrderSemantics.reduct M).mem c L := by
  obtain ⟨_,_,_,_,_,⟨p,_,hpa⟩,⟨q,_,hqb⟩,⟨r,_,hrc⟩⟩ := hv
  exact ⟨hp.2 p a hpa,hp.2 q b hqb,hp.2 r c hrc⟩

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units C L projection a b : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a L) (hb : (Project.FirstOrderSemantics.reduct M).mem b L) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c L ∧ Value J Domains Muls projection a b c := by
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := ConstructionDirectedLimitCarrier.common_stage_pair hM hC hp hE hT hL hP hEq ha hb
  obtain ⟨z,hxyz⟩ := ConstructionDirectedMonoidData.product_total hFam hx hy
  obtain ⟨c,hc,hzc⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hxyz.2.2.1
  exact ⟨c,hc,i,x,y,z,hxyz,hxa,hyb,hzc⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units C L projection a b c d : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hHom : HomLaws J E Domains F Muls Units)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw J E Domains F projection)
    (hc : Value J Domains Muls projection a b c) (hd : Value J Domains Muls projection a b d) : c = d := by
  obtain ⟨i,x,y,z,hxyz,hxa,hyb,hzc⟩ := hc
  obtain ⟨j,u,v,w,huvw,hua,hvb,hwd⟩ := hd
  obtain ⟨_,_,k,s,hk,hik,hjk,hxs,hus⟩ := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hxa hua).mp rfl
  obtain ⟨_,_,l,t,hl,hil,hjl,hyt,hvt⟩ := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hyb hvb).mp rfl
  obtain ⟨r,hr,hkr,hlr⟩ := hE.2.2 k l hk hl
  have hir := hE.2.1 i k r hxyz.1.1 hk hr hik hkr
  have hjr := hE.2.1 j k r huvw.1.1 hk hr hjk hkr
  obtain ⟨xx,hxx⟩ := hT.1 i r x hxyz.1 hr hir
  obtain ⟨yy,hyy⟩ := hT.1 i r y hxyz.2.1 hr hir
  obtain ⟨zz,hzz⟩ := hT.1 i r z hxyz.2.2.1 hr hir
  obtain ⟨uu,huu⟩ := hT.1 j r u huvw.1 hr hjr
  obtain ⟨vv,hvv⟩ := hT.1 j r v huvw.2.1 hr hjr
  obtain ⟨ww,hww⟩ := hT.1 j r w huvw.2.2.1 hr hjr
  have heX := equal_after hE hT hr hik hjk hkr hxs hus hxx huu
  have heY := equal_after hE hT hr hil hjl hlr hyt hvt hyy hvv
  subst uu
  subst vv
  have hp1 := hHom.1 i r x y z xx yy zz hir hxyz hxx hyy hzz
  have hp2 := hHom.1 j r u v w xx yy ww hjr huvw huu hvv hww
  have heZ := ConstructionDirectedMonoidData.product_unique hFam hp1 hp2
  subst ww
  obtain ⟨out,_,hout⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hp1.2.2.1
  have heC := ConstructionDirectedLimitCarrier.of_map hE hT hEq hir hzz hzc hout
  have heD := ConstructionDirectedLimitCarrier.of_map hE hT hEq hjr hww hwd hout
  exact heC.trans heD.symm

def value {m : Nat} (J Domains Muls projection a b c : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionDirectedMonoidData.productAt
  ((((J).succ).succ).succ).succ ((((Domains).succ).succ).succ).succ ((((Muls).succ).succ).succ).succ
  ((((0 : Fin (m+1))).succ).succ).succ (((0 : Fin (m+2))).succ).succ ((0 : Fin (m+3))).succ (0 : Fin
  (m+4))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  ((((projection).succ).succ).succ).succ ((((0 : Fin (m+1))).succ).succ).succ (((0 : Fin
  (m+2))).succ).succ ((((a).succ).succ).succ).succ)) (.conj (ProjectSyntax.encode id
  (ForcingDiagramOrder.product ((((projection).succ).succ).succ).succ ((((0 : Fin
  (m+1))).succ).succ).succ ((0 : Fin (m+3))).succ ((((b).succ).succ).succ).succ)) (ProjectSyntax.encode
  id (ForcingDiagramOrder.product ((((projection).succ).succ).succ).succ ((((0 : Fin
  (m+1))).succ).succ).succ (0 : Fin (m+4)) ((((c).succ).succ).succ).succ)))))))))
theorem value_freeClosed {m : Nat} (J Domains Muls projection a b c : Fin m) :
    (value J Domains Muls projection a b c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionDirectedMonoidData.productAt_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls projection a b c : Fin m) :
    Project.Formula.satisfies env (value J Domains Muls projection a b c) ↔
      Value (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound projection) (env.bound a) (env.bound b) (env.bound c) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),
    ConstructionDirectedMonoidData.productAt_semantics hM]
  rfl

def pairValue {m : Nat} (J Domains Muls projection p c : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0))
    (value J.succ.succ Domains.succ.succ Muls.succ.succ projection.succ.succ 1 0 c.succ.succ)))

theorem pairValue_freeClosed {m : Nat} (J Domains Muls projection p c : Fin m) :
    (pairValue J Domains Muls projection p c).FreeClosed := by
  simp -implicitDefEqProofs [pairValue,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,value_freeClosed]

theorem pairValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls projection p c : Fin m) :
    Project.Formula.satisfies env (pairValue J Domains Muls projection p c) ↔
      ∃ a b, PureKuratowski.Code M (env.bound p) a b ∧
        Value (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound projection) a b (env.bound c) := by
  simp only [pairValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,value_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units C L projection : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hHom : HomLaws J E Domains F Muls Units)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) :
    ∃ B G, ConstructionProbeLetters.Representatives L L B ∧ MapsTo B L G ∧ Graph J Domains Muls projection G := by
  obtain ⟨B,hB⟩ := ConstructionProbeLetters.exists_representatives hM L L
  let schema : Project.BinarySchema 4 := {
    body := pairValue 2 3 4 5 1 0
    freeClosed := pairValue_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases J (Fin.cases Domains (Fin.cases Muls (fun _ => projection))), free := fun _ => J }
  have he (p c) : schema.denote env p c ↔ ∃ a b, PureKuratowski.Code M p a b ∧ Value J Domains Muls projection a b c :=
    pairValue_semantics hM ((env.push p).push c) 2 3 4 5 1 0
  obtain ⟨G,hG,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := B) (target := L) (by
      intro p hpB
      obtain ⟨a,b,ha,hb,hcode⟩ := (hB p).mp hpB
      obtain ⟨c,_,hc⟩ := value_total hM hFam hE hT hC hp hL hP hEq ha hb
      exact ⟨c,(he p c).mpr ⟨a,b,hcode,hc⟩⟩) (by
      intro p _ c d hc hd
      obtain ⟨a,b,hcode,hc⟩ := (he p c).mp hc
      obtain ⟨a',b',hcode',hd⟩ := (he p d).mp hd
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact value_unique hM hFam hE hT hHom hC hp hEq hc hd) (by
      intro p c _ hc
      obtain ⟨_,_,_,hc⟩ := (he p c).mp hc
      exact (value_members hp hc).2.2)
  refine ⟨B,G,hB,(ForcingSupportSize.native_mapsTo hM B L G).mpr hG,?_⟩
  intro a b c
  constructor
  · rintro ⟨p,hcode,hpc⟩
    obtain ⟨a',b',hcode',hv⟩ := (he p c).mp ((hGraph p c).mp hpc).2
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact hv
  · intro hv
    obtain ⟨ha,hb,_⟩ := value_members hp hv
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM a b
    exact ⟨p,hcode,(hGraph p c).mpr ⟨(hB p).mpr ⟨a,b,ha,hb,hcode⟩,(he p c).mpr ⟨a,b,hcode,hv⟩⟩⟩

def graph {m : Nat} (J Domains Muls projection G : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.iff
    (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ 2 1 0))
    (value J.succ.succ.succ Domains.succ.succ.succ Muls.succ.succ.succ projection.succ.succ.succ 2 1 0))))

theorem graph_freeClosed {m : Nat} (J Domains Muls projection G : Fin m) :
    (graph J Domains Muls projection G).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls projection G : Fin m) :
    Project.Formula.satisfies env (graph J Domains Muls projection G) ↔
      Graph (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound projection) (env.bound G) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),value_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedProduct
