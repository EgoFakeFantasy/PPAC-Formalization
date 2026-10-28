
/- Pinned Models/ComponentGluing.Vertex/Arrow/contractAt/successors_directed/Common.
The root equation and actual bounded ideal are retained. All diagrams, indices
and ideals are internal sets. Reuse old Sub/index_unique and actual ideal
contraction; no host category, quotient, or finite-path induction is substituted. -/
import PPAC.Migration.ConstructionIdealContraction
import PPAC.Migration.ForcingDiagramPoset

namespace PPAC.Migration.ConstructionComponentVertices
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionIdealProbes (ConeIdeal)
open ConstructionIdealContraction (Contract)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ForcingSupportSize (Injection)
open ForcingDiagramOrder (Sub Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Vertex (D I mul q r a U : M.Carrier .set) : Prop :=
  Injection D I r ∧ Sub D mul r a q ∧ ConeIdeal D mul a U

def Arrow (D mul r U s V n : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem n U ∧ Sub D mul r n s ∧ Contract D mul n U V

theorem sub_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul r n s t : M.Carrier .set} (hs : Injection D I s) (ht : Injection D I t)
    (hS : Sub D mul r n s) (hT : Sub D mul r n t) : s = t :=
  ForcingDiagramPoset.injection_ext hM hs ht (fun x z => (hS x z).trans (hT x z).symm)

theorem arrow_index_unique {D I mul e q r a U s V n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hf : Arrow D mul r U s V n) (hg : Arrow D mul r U s V m) : n = m :=
  ForcingDiagramPoset.index_unique hm hv.1 (hv.2.2.1 n hf.1) (hv.2.2.1 m hg.1) hf.2.1 hg.2.1

theorem index_mul {D I mul e q r a U s b V n : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hw : Vertex D I mul q s b V) (hf : Arrow D mul r U s V n) : Product mul n b a := by
  have hn := hv.2.2.1 n hf.1
  obtain ⟨c,hc,hp⟩ := (hm.2.1 n hn).1 b hw.2.2.2.1
  have hs := ForcingDiagramPoset.sub_sub hm hn hw.2.2.2.1 hp hf.2.1 hw.2.1
  have he := ForcingDiagramPoset.index_unique hm hv.1 hc hv.2.2.2.1 hs hv.2.1
  exact he ▸ hp

theorem identity {D I mul e q r a U : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U) :
    Arrow D mul r U r U e := by
  obtain ⟨x,hx⟩ := hv.2.2.2.2.1
  have heU := hv.2.2.2.2.2.2.1 e x hm.1.1 hx
    ⟨x,hv.2.2.1 x hx,(hm.1.2 x (hv.2.2.1 x hx) x).1.mpr rfl⟩
  refine ⟨heU,ForcingDiagramPoset.sub_one hm hv.1,?_⟩
  intro y
  constructor
  · intro hy
    exact ⟨hv.2.2.1 y hy,y,(hm.1.2 y (hv.2.2.1 y hy) y).1.mpr rfl,hy⟩
  · rintro ⟨hy,z,hp,hz⟩
    exact (hm.1.2 y hy z).1.mp hp ▸ hz

theorem compose {D I mul e q r a U s b V t W n m nm : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hw : Vertex D I mul q s b V)
    (hf : Arrow D mul r U s V n) (hg : Arrow D mul s V t W m)
    (hp : Product mul n m nm) : Arrow D mul r U t W nm := by
  have hn := hv.2.2.1 n hf.1
  have hmD := hw.2.2.1 m hg.1
  obtain ⟨_,nm',hp',hnm'⟩ := (hf.2.2 m).mp hg.1
  have he := (hm.2.1 n hn).2.1 m nm' nm hmD hp' hp
  exact ⟨he ▸ hnm',ForcingDiagramPoset.sub_sub hm hn hmD hp hf.2.1 hg.2.1,
    ConstructionIdealContraction.contract_comp hm hn hmD hp hf.2.2 hg.2.2⟩

theorem between (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U s b V t c W n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hw : Vertex D I mul q s b V) (hz : Vertex D I mul q t c W)
    (hf : Arrow D mul r U s V n) (hg : Arrow D mul r U t W m)
    (hle : Divides D mul n m) : ∃ d, Product mul n d m ∧ Arrow D mul s V t W d := by
  obtain ⟨d,hd,hp⟩ := hle
  have hn := hv.2.2.1 n hf.1
  have hdV := (hf.2.2 d).mpr ⟨hd,m,hp,hg.1⟩
  obtain ⟨t',ht',hsub⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 d hd) hw.1
  have ht := sub_eq hM ht' hz.1 (ForcingDiagramPoset.sub_sub hm hn hd hp hf.2.1 hsub) hg.2.1
  obtain ⟨W',hW'⟩ := ConstructionIdealContraction.exists_contract hM D mul d V
  have he := ConstructionIdealContraction.contract_unique hM
    (ConstructionIdealContraction.contract_comp hm hn hd hp hf.2.2 hW') hg.2.2
  exact ⟨d,hp,hdV,ht ▸ hsub,he ▸ hW'⟩

theorem eq_of_index_one (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U s b V : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hw : Vertex D I mul q s b V) (hf : Arrow D mul r U s V e) :
    r = s ∧ a = b ∧ U = V := by
  have hrs := sub_eq hM hv.1 hw.1 (ForcingDiagramPoset.sub_one hm hv.1) hf.2.1
  subst s
  have hab := ForcingDiagramPoset.index_unique hm hv.1 hv.2.2.2.1 hw.2.2.2.1 hv.2.1 hw.2.1
  exact ⟨rfl,hab,(ConstructionIdealContraction.contract_one hM hm hv.2.2 hf.2.2).symm⟩

/-- Source contractAt, constructing both the entire subdiagram and its exact right-quotient ideal. -/
theorem contract_at (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U n c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n U)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c D) (hnc : Product mul n c a) :
    ∃ s V, Vertex D I mul q s c V ∧ Arrow D mul r U s V n := by
  have hnD := hv.2.2.1 n hn
  obtain ⟨s,hs,hsub⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 n hnD) hv.1
  obtain ⟨V,hV⟩ := ConstructionIdealContraction.exists_contract hM D mul n U
  have hIdeal := ConstructionIdealContraction.contract_ideal hm hv.2.2 hn hc hnc hV
  have hroot : Sub D mul s c q := by
    intro x z
    constructor
    · intro hxz
      obtain ⟨hx,y,hy,hax,hyz⟩ := (hv.2.1 x z).mp hxz
      obtain ⟨cx,hcx,hcxp⟩ := (hm.2.1 c hc).1 x hx
      exact ⟨hx,cx,hcx,hcxp,(hsub cx z).mpr ⟨hcx,y,hy,
        (hm.2.2 n c x a cx y hnD hc hx hnc hcxp).mp hax,hyz⟩⟩
    · rintro ⟨hx,cx,hcx,hcxp,hcxz⟩
      obtain ⟨_,y,hy,hncx,hyz⟩ := (hsub cx z).mp hcxz
      exact (hv.2.1 x z).mpr ⟨hx,y,hy,
        (hm.2.2 n c x a cx y hnD hc hx hnc hcxp).mpr hncx,hyz⟩
  exact ⟨s,V,⟨hs,hroot,hIdeal⟩,hn,hsub,hV⟩

theorem exists_contraction (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U n : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n U) :
    ∃ s c V, Vertex D I mul q s c V ∧ Arrow D mul r U s V n := by
  obtain ⟨c,hc,hp⟩ := hv.2.2.2.2.2.1 n hn
  obtain ⟨s,V,hv',hf⟩ := contract_at hM hm hv hn hc hp
  exact ⟨s,c,V,hv',hf⟩

theorem successors_directed (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U s b V t c W n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hv : Vertex D I mul q r a U) (hw : Vertex D I mul q s b V)
    (hz : Vertex D I mul q t c W)
    (hf : Arrow D mul r U s V n) (hg : Arrow D mul r U t W m) :
    ∃ z d Z i j, Vertex D I mul q z d Z ∧ Arrow D mul s V z Z i ∧ Arrow D mul t W z Z j := by
  obtain ⟨k,hk,hJoin⟩ := hJ n m a (hv.2.2.1 n hf.1) (hv.2.2.1 m hg.1) hv.2.2.2.1
    (hv.2.2.2.2.2.1 n hf.1) (hv.2.2.2.2.2.1 m hg.1)
  have hkU := hv.2.2.2.2.2.2.2 n m k hf.1 hg.1 hk hJoin
  obtain ⟨z,d,Z,hz',hh⟩ := exists_contraction hM hm hv hkU
  have hkk : Divides D mul k k := ⟨e,hm.1.1,(hm.1.2 k hk k).2.mpr rfl⟩
  obtain ⟨i,_,hi⟩ := between hM hm hv hw hz' hf hh ((hJoin k hk).mpr hkk).1
  obtain ⟨j,_,hj⟩ := between hM hm hv hz hz' hg hh ((hJoin k hk).mpr hkk).2
  exact ⟨z,d,Z,i,j,hz',hi,hj⟩

def Common (D I mul q r U s V : M.Carrier .set) : Prop :=
  ∃ t c W n m, Vertex D I mul q t c W ∧ Arrow D mul r U t W n ∧ Arrow D mul s V t W m

theorem common_refl {D I mul e q r a U : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U) :
    Common D I mul q r U r U :=
  ⟨r,a,U,e,e,hv,identity hm hv,identity hm hv⟩

theorem common_symm {D I mul q r U s V : M.Carrier .set}
    (h : Common D I mul q r U s V) : Common D I mul q s V r U := by
  obtain ⟨t,c,W,n,m,ht,hn,hm⟩ := h
  exact ⟨t,c,W,m,n,ht,hm,hn⟩

theorem common_of_arrow {D I mul e q r U s b V n : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hw : Vertex D I mul q s b V)
    (h : Arrow D mul r U s V n) : Common D I mul q r U s V :=
  ⟨s,b,V,n,e,hw,h,identity hm hw⟩

theorem common_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U s b V t c W : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hr : Vertex D I mul q r a U) (hs : Vertex D I mul q s b V)
    (ht : Vertex D I mul q t c W)
    (hab : Common D I mul q r U s V) (hbc : Common D I mul q s V t W) :
    Common D I mul q r U t W := by
  obtain ⟨p,d,P,n,m,hp,hn,hm'⟩ := hab
  obtain ⟨k,f,K,i,j,hk,hi,hj⟩ := hbc
  obtain ⟨z,g,Z,l,o,hz,hl,ho⟩ := successors_directed hM hm hJ hs hp hk hm' hi
  obtain ⟨nl,_,hnl⟩ := (hm.2.1 n (hr.2.2.1 n hn.1)).1 l (hp.2.2.1 l hl.1)
  obtain ⟨jo,_,hjo⟩ := (hm.2.1 j (ht.2.2.1 j hj.1)).1 o (hk.2.2.1 o ho.1)
  exact ⟨z,g,Z,nl,jo,hz,compose hm hr hp hn hl hnl,compose hm ht hk hj ho hjo⟩

/-- Uniqueness of the actual contraction vertex at a specified index. -/
theorem contraction_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U s b V t c W n : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hv : Vertex D I mul q r a U)
    (hw : Vertex D I mul q s b V) (hz : Vertex D I mul q t c W)
    (hf : Arrow D mul r U s V n) (hg : Arrow D mul r U t W n) :
    s = t ∧ b = c ∧ V = W := by
  exact ⟨sub_eq hM hw.1 hz.1 hf.2.1 hg.2.1,
    (hm.2.1 n (hv.2.2.1 n hf.1)).2.2 b c a hw.2.2.2.1 hz.2.2.2.1
      (index_mul hm hv hw hf) (index_mul hm hv hz hg),
    ConstructionIdealContraction.contract_unique hM hf.2.2 hg.2.2⟩

def vertex {m : Nat} (D I mul q r a U : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.injection r D I))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub D mul r a q))
      (ConstructionIdealProbes.coneIdeal D mul a U))

theorem vertex_freeClosed {m : Nat} (D I mul q r a U : Fin m) :
    (vertex D I mul q r a U).FreeClosed := by
  simp -implicitDefEqProofs [vertex,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionIdealProbes.coneIdeal_freeClosed]

theorem vertex_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q r a U : Fin m) :
    Project.Formula.satisfies env (vertex D I mul q r a U) ↔
      Vertex (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound r) (env.bound a) (env.bound U) := by
  simp only [vertex,Vertex,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ConstructionIdealProbes.coneIdeal_semantics hM]
  rfl

def arrow {m : Nat} (D mul r U s V n : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound n) (.bound U))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub D mul r n s))
      (ConstructionIdealContraction.contract D mul n U V))

theorem arrow_freeClosed {m : Nat} (D mul r U s V n : Fin m) :
    (arrow D mul r U s V n).FreeClosed := by
  simp -implicitDefEqProofs [arrow,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionIdealContraction.contract_freeClosed]

theorem arrow_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul r U s V n : Fin m) :
    Project.Formula.satisfies env (arrow D mul r U s V n) ↔
      Arrow (env.bound D) (env.bound mul) (env.bound r) (env.bound U) (env.bound s) (env.bound V) (env.bound n) := by
  simp only [arrow,Arrow,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.sub_semantics (M := M),ConstructionIdealContraction.contract_semantics hM,
    Project.Term.eval_bound]
  rfl

def common {m : Nat} (D I mul q r U s V : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (vertex D.succ.succ.succ.succ.succ
  I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ (4 : Fin (m+5))
  (3 : Fin (m+5)) (2 : Fin (m+5))) (.conj (arrow D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ U.succ.succ.succ.succ.succ (4 : Fin (m+5))
  (2 : Fin (m+5)) (1 : Fin (m+5))) (arrow D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ
  s.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ (4 : Fin (m+5)) (2 : Fin (m+5)) (0 : Fin
  (m+5))))))))))

theorem common_freeClosed {m : Nat} (D I mul q r U s V : Fin m) :
    (common D I mul q r U s V).FreeClosed := by
  simp -implicitDefEqProofs [common,Definitional.Formula.FreeClosed,vertex_freeClosed,arrow_freeClosed]

theorem common_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q r U s V : Fin m) :
    Project.Formula.satisfies env (common D I mul q r U s V) ↔
      Common (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound r) (env.bound U) (env.bound s) (env.bound V) := by
  simp only [common,Common,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,vertex_semantics hM,arrow_semantics hM]
  rfl

def geometrySentence : Project.Sentence where
  formula :=
    (Project.Formula.forallClosure 16 (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (0 : Fin 16) (2 : Fin 16) (3 : Fin 16))) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (0 : Fin 16) (2 : Fin 16)) (.imp (vertex (0
    : Fin 16) (1 : Fin 16) (2 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6 : Fin 16) (7 : Fin 16)) (.imp
    (vertex (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (4 : Fin 16) (8 : Fin 16) (9 : Fin 16) (10 : Fin
    16)) (.imp (vertex (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (4 : Fin 16) (11 : Fin 16) (12 : Fin 16)
    (13 : Fin 16)) (.conj (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin 16) (5 : Fin 16) (7 :
    Fin 16) (3 : Fin 16)) (.conj (.imp (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin 16) (8 :
    Fin 16) (10 : Fin 16) (14 : Fin 16)) (.imp (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin
    16) (8 : Fin 16) (10 : Fin 16) (15 : Fin 16)) (Project.Formula.extensionalEq (.bound (14 : Fin
    16)) (.bound (15 : Fin 16))))) (.conj (.imp (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin
    16) (8 : Fin 16) (10 : Fin 16) (14 : Fin 16)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product (2 : Fin 16) (14 : Fin 16) (9 : Fin 16) (6 : Fin 16)))) (.conj (.imp
    (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin 16) (8 : Fin 16) (10 : Fin 16) (14 : Fin
    16)) (.imp (arrow (0 : Fin 16) (2 : Fin 16) (8 : Fin 16) (10 : Fin 16) (11 : Fin 16) (13 : Fin 16)
    (15 : Fin 16)) (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product (2 : Fin
    16).succ (14 : Fin 16).succ (15 : Fin 16).succ (0 : Fin 17))) (arrow (0 : Fin 16).succ (2 : Fin
    16).succ (5 : Fin 16).succ (7 : Fin 16).succ (11 : Fin 16).succ (13 : Fin 16).succ (0 : Fin
    17)))))) (.conj (.imp (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin 16) (8 : Fin 16) (10
    : Fin 16) (14 : Fin 16)) (.imp (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin 16) (11 :
    Fin 16) (13 : Fin 16) (15 : Fin 16)) (.imp (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides (0 : Fin 16) (2 : Fin 16) (14 : Fin 16) (15 : Fin 16))) (.existsE
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product (2 : Fin 16).succ (14 : Fin 16).succ
    (0 : Fin 17) (15 : Fin 16).succ)) (arrow (0 : Fin 16).succ (2 : Fin 16).succ (8 : Fin 16).succ (10
    : Fin 16).succ (11 : Fin 16).succ (13 : Fin 16).succ (0 : Fin 17))))))) (.conj (.imp (arrow (0 :
    Fin 16) (2 : Fin 16) (5 : Fin 16) (7 : Fin 16) (8 : Fin 16) (10 : Fin 16) (3 : Fin 16)) (.conj
    (Project.Formula.extensionalEq (.bound (5 : Fin 16)) (.bound (8 : Fin 16))) (.conj
    (Project.Formula.extensionalEq (.bound (6 : Fin 16)) (.bound (9 : Fin 16)))
    (Project.Formula.extensionalEq (.bound (7 : Fin 16)) (.bound (10 : Fin 16)))))) (.conj (.imp (.mem
    (.bound (14 : Fin 16)) (.bound (7 : Fin 16))) (.existsE (.existsE (.existsE (.conj (vertex (0 :
    Fin 16).succ.succ.succ (1 : Fin 16).succ.succ.succ (2 : Fin 16).succ.succ.succ (4 : Fin
    16).succ.succ.succ (2 : Fin 19) (1 : Fin 19) (0 : Fin 19)) (arrow (0 : Fin 16).succ.succ.succ (2 :
    Fin 16).succ.succ.succ (5 : Fin 16).succ.succ.succ (7 : Fin 16).succ.succ.succ (2 : Fin 19) (0 :
    Fin 19) (14 : Fin 16).succ.succ.succ)))))) (.conj (.imp (arrow (0 : Fin 16) (2 : Fin 16) (5 : Fin
    16) (7 : Fin 16) (8 : Fin 16) (10 : Fin 16) (14 : Fin 16)) (.imp (arrow (0 : Fin 16) (2 : Fin 16)
    (5 : Fin 16) (7 : Fin 16) (11 : Fin 16) (13 : Fin 16) (15 : Fin 16)) (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (vertex (0 : Fin 16).succ.succ.succ.succ.succ (1 : Fin
    16).succ.succ.succ.succ.succ (2 : Fin 16).succ.succ.succ.succ.succ (4 : Fin
    16).succ.succ.succ.succ.succ (4 : Fin 21) (3 : Fin 21) (2 : Fin 21)) (.conj (arrow (0 : Fin
    16).succ.succ.succ.succ.succ (2 : Fin 16).succ.succ.succ.succ.succ (8 : Fin
    16).succ.succ.succ.succ.succ (10 : Fin 16).succ.succ.succ.succ.succ (4 : Fin 21) (2 : Fin 21) (1 :
    Fin 21)) (arrow (0 : Fin 16).succ.succ.succ.succ.succ (2 : Fin 16).succ.succ.succ.succ.succ (11 :
    Fin 16).succ.succ.succ.succ.succ (13 : Fin 16).succ.succ.succ.succ.succ (4 : Fin 21) (2 : Fin 21)
    (0 : Fin 21))))))))))) (.imp (common (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (4 : Fin 16) (5 : Fin
    16) (7 : Fin 16) (8 : Fin 16) (10 : Fin 16)) (.imp (common (0 : Fin 16) (1 : Fin 16) (2 : Fin 16)
    (4 : Fin 16) (8 : Fin 16) (10 : Fin 16) (11 : Fin 16) (13 : Fin 16)) (common (0 : Fin 16) (1 : Fin
    16) (2 : Fin 16) (4 : Fin 16) (5 : Fin 16) (7 : Fin 16) (11 : Fin 16) (13 : Fin
    16))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      vertex_freeClosed,arrow_freeClosed,common_freeClosed]

theorem geometry_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence geometrySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) geometrySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    vertex_semantics hM,arrow_semantics hM,common_semantics hM,Project.Term.eval_bound]
  intro hm hJ hv hw hz
  refine ⟨identity hm hv,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun hf hg => arrow_index_unique hm hv hf hg
  · exact fun hf => index_mul hm hv hw hf
  · intro hf hg
    obtain ⟨nm,_,hp⟩ := (hm.2.1 (bound 14) (hv.2.2.1 _ hf.1)).1 (bound 15) (hw.2.2.1 _ hg.1)
    exact ⟨nm,hp,compose hm hv hw hf hg hp⟩
  · exact fun hf hg hle => between hM hm hv hw hz hf hg hle
  · exact fun hf => eq_of_index_one hM hm hv hw hf
  · exact fun hn => exists_contraction hM hm hv hn
  · exact fun hf hg => successors_directed hM hm hJ hv hw hz hf hg
  · exact fun h1 h2 => common_trans hM hm hJ hv hw hz h1 h2

theorem geometry_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence geometrySentence) := ModelTransfer.derives (fun _ hM => geometry_models hM)

end PPAC.Migration.ConstructionComponentVertices
