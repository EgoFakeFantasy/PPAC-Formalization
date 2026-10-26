/- Source ProbeWords.Path.transition / DirectedSystem. Right multiplication
uses only the original left-cancel monoid; no injective transition premise. -/
import PPAC.Migration.ConstructionProbePath

namespace PPAC.Migration.ConstructionProbeTransitions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionFractionOrder (NatLe)
open ConstructionBaseCostBound (natLeF natLeF_freeClosed natLeF_semantics)
open ConstructionProbePath
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem product_closed {D mul e x y z : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D) (hp : Product mul x y z) :
    (Project.FirstOrderSemantics.reduct M).mem z D := by
  obtain ⟨z',hz,hp'⟩ := (hm.2.1 x hx).1 y hy
  exact ((hm.2.1 x hx).2.1 y z' z hy hp' hp) ▸ hz

def Transition (D mul F i j x y : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem x D ∧ ∃ f, Product F i j f ∧ Product mul x f y

theorem transition_total {w D mul e zero a node F i j x : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hp : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j w) (hij : NatLe i j)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y D ∧ Transition D mul F i j x y := by
  obtain ⟨f,hf⟩ := hp.2.2.2.1 i j hi hj hij
  obtain ⟨ni,nj,hni,hnj,hfD,hprod⟩ := hf
  obtain ⟨y,hy,hxy⟩ := (hm.2.1 x hx).1 f hfD
  exact ⟨y,hy,hx,f,(hF i j f).mpr ⟨hi,hj,hij,ni,nj,hni,hnj,hfD,hprod⟩,hxy⟩

theorem transition_unique {w D mul e zero a node F i j x y z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hp : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F)
    (hy : Transition D mul F i j x y) (hz : Transition D mul F i j x z) : y = z := by
  obtain ⟨hx,f,hf,hxy⟩ := hy
  obtain ⟨_,g,hg,hxz⟩ := hz
  have hf' := ((hF i j f).mp hf).2.2.2
  have hg' := ((hF i j g).mp hg).2.2.2
  have he := factor_unique hm hp.1 hf' hg'
  subst g
  obtain ⟨_,_,_,_,hfD,_⟩ := hf'
  exact (hm.2.1 x hx).2.1 f y z hfD hxy hxz

theorem transition_closed {w D mul e node F i j x y : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (h : Transition D mul F i j x y) : (Project.FirstOrderSemantics.reduct M).mem y D := by
  obtain ⟨hx,f,hf,hxy⟩ := h
  obtain ⟨_,_,_,ni,nj,_,_,hfD,_⟩ := (hF i j f).mp hf
  exact product_closed hm hx hfD hxy

theorem transition_self {w D mul e zero a node F T i x : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hL : TableLaws w mul e zero a node F T)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) : Transition D mul F i i x x :=
  ⟨hx,e,hL.1 i hi,((hm.1.2 x hx x).2).mpr rfl⟩

theorem transition_comp {w D mul e zero a node F T i j k x y z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hL : TableLaws w mul e zero a node F T)
    (hxy : Transition D mul F i j x y) (hyz : Transition D mul F j k y z) :
    Transition D mul F i k x z := by
  obtain ⟨hx,f,hf,hxf⟩ := hxy
  obtain ⟨_,g,hg,hyg⟩ := hyz
  obtain ⟨_,_,_,ni,nj,_,_,hfD,_⟩ := (hF i j f).mp hf
  obtain ⟨_,_,_,nj',nk,_,_,hgD,_⟩ := (hF j k g).mp hg
  obtain ⟨fg,_,hfg⟩ := (hm.2.1 f hfD).1 g hgD
  exact ⟨hx,fg,hL.2.2.1 i j k f g fg hf hg hfg,
    (hm.2.2 x f g y fg z hx hfD hgD hxf hfg).mp hyg⟩

theorem transition_left {w D mul e node F i j b x y bx byv : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hbx : Product mul b x bx) (hby : Product mul b y byv)
    (hxy : Transition D mul F i j x y) : Transition D mul F i j bx byv := by
  obtain ⟨hx,f,hf,hxf⟩ := hxy
  obtain ⟨_,_,_,ni,nj,_,_,hfD,_⟩ := (hF i j f).mp hf
  exact ⟨product_closed hm hb hx hbx,f,hf,(hm.2.2 b x f bx y byv hb hx hfD hbx hxf).mpr hby⟩

theorem transition_reflect_left {w D mul e node F i j b x y bx byv : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (hbx : Product mul b x bx) (hby : Product mul b y byv)
    (hxy : Transition D mul F i j bx byv) : Transition D mul F i j x y := by
  obtain ⟨_,f,hf,hbxf⟩ := hxy
  obtain ⟨_,_,_,ni,nj,_,_,hfD,_⟩ := (hF i j f).mp hf
  obtain ⟨z,hz,hxf⟩ := (hm.2.1 x hx).1 f hfD
  have hbz := (hm.2.2 b x f bx z byv hb hx hfD hbx hxf).mp hbxf
  have he := (hm.2.1 b hb).2.2 z y byv hz hy hbz hby
  exact ⟨hx,f,hf,he ▸ hxf⟩

def transition {m : Nat} (D mul F i j x y : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound x) (.bound D)) (.existsE (.conj
    (ProjectSyntax.encode id (product F.succ i.succ j.succ 0))
    (ProjectSyntax.encode id (product mul.succ x.succ 0 y.succ))))

theorem transition_freeClosed {m : Nat} (D mul F i j x y : Fin m) :
    (transition D mul F i j x y).FreeClosed := by
  simp -implicitDefEqProofs [transition,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem transition_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul F i j x y : Fin m) :
    Project.Formula.satisfies env (transition D mul F i j x y) ↔
      Transition (env.bound D) (env.bound mul) (env.bound F) (env.bound i) (env.bound j) (env.bound x) (env.bound y) := by
  simp only [transition,Transition,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def TransitionGraph (D mul F i j r : M.Carrier .set) : Prop := ∀ x y,
  PureKuratowski.PairMember M x y r ↔ Transition D mul F i j x y

theorem exists_transition_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F i j : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hp : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j w) (hij : NatLe i j) :
    ∃ r, MapsTo D D r ∧ TransitionGraph D mul F i j r := by
  let schema : Project.BinarySchema 5 := { body := transition 2 3 4 5 6 1 0, freeClosed := transition_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases D (Fin.cases mul (Fin.cases F (Fin.cases i (fun _ => j)))), free := fun _ => D }
  have he : ∀ x y, schema.denote env x y ↔ Transition D mul F i j x y :=
    fun x y => transition_semantics hM ((env.push x).push y) 2 3 4 5 6 1 0
  obtain ⟨r,hr,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := D) (target := D) (by
      intro x hx
      obtain ⟨y,_,hxy⟩ := transition_total hm hp hF hi hj hij hx
      exact ⟨y,(he x y).mpr hxy⟩) (by
      intro x _ y z hy hz
      exact transition_unique hm hp hF ((he x y).mp hy) ((he x z).mp hz)) (by
      intro x y _ hxy
      exact transition_closed hm hF ((he x y).mp hxy))
  refine ⟨r,(ForcingSupportSize.native_mapsTo hM D D r).mpr hr,fun x y => ?_⟩
  exact (hgraph x y).trans ⟨fun h => (he x y).mp h.2,fun h => ⟨h.1,(he x y).mpr h⟩⟩

/-- The relation defining equality of source direct-limit representatives. -/
def Meets (w D mul F i x j y : M.Carrier .set) : Prop :=
  ∃ k z, (Project.FirstOrderSemantics.reduct M).mem k w ∧
    Transition D mul F i k x z ∧ Transition D mul F j k y z

theorem meets_refl {w D mul e zero a node F T i x : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hL : TableLaws w mul e zero a node F T)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) : Meets w D mul F i x i x :=
  ⟨i,x,hi,transition_self hm hL hi hx,transition_self hm hL hi hx⟩

theorem meets_symm {w D mul F i x j y : M.Carrier .set}
    (h : Meets w D mul F i x j y) : Meets w D mul F j y i x := by
  obtain ⟨k,z,hk,hx,hy⟩ := h
  exact ⟨k,z,hk,hy,hx⟩

theorem meets_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F T i x j y k z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hp : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F) (hL : TableLaws w mul e zero a node F T)
    (hxy : Meets w D mul F i x j y) (hyz : Meets w D mul F j y k z) :
    Meets w D mul F i x k z := by
  obtain ⟨r,v,hr,hxv,hyv⟩ := hxy
  obtain ⟨s,t,hs,hyt,hzt⟩ := hyz
  have upper : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q w ∧ NatLe r q ∧ NatLe s q := by
    rcases ConstructionFractionOrder.nat_compare hM hw hr hs with he | hrs | hsr
    · exact ⟨s,hs,Or.inl he,Or.inl rfl⟩
    · exact ⟨s,hs,Or.inr hrs,Or.inl rfl⟩
    · exact ⟨r,hr,Or.inl rfl,Or.inr hsr⟩
  obtain ⟨q,hq,hrq,hsq⟩ := upper
  obtain ⟨v',_,hvv⟩ := transition_total hm hp hF hr hq hrq (transition_closed hm hF hxv)
  obtain ⟨t',_,htt⟩ := transition_total hm hp hF hs hq hsq (transition_closed hm hF hzt)
  have he := transition_unique hm hp hF (transition_comp hm hF hL hyv hvv) (transition_comp hm hF hL hyt htt)
  exact ⟨q,t',hq,he ▸ transition_comp hm hF hL hxv hvv,transition_comp hm hF hL hzt htt⟩

theorem meets_transition {w D mul e zero a node F T i j x y : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hL : TableLaws w mul e zero a node F T)
    (h : Transition D mul F i j x y) : Meets w D mul F i x j y := by
  have hcopy := h
  obtain ⟨_,f,hf,_⟩ := hcopy
  have hj := ((hF i j f).mp hf).2.1
  exact ⟨j,y,hj,h,transition_self hm hL hj (transition_closed hm hF h)⟩

theorem meets_left {w D mul e node F i j b x y bx byv : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hbx : Product mul b x bx) (hby : Product mul b y byv)
    (h : Meets w D mul F i x j y) : Meets w D mul F i bx j byv := by
  obtain ⟨k,z,hk,hxz,hyz⟩ := h
  obtain ⟨bz,_,hbz⟩ := (hm.2.1 b hb).1 z (transition_closed hm hF hxz)
  exact ⟨k,bz,hk,transition_left hm hF hb hbx hbz hxz,transition_left hm hF hb hby hbz hyz⟩

theorem meets_reflect_left {w D mul e node F i j b x y bx byv : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D)
    (hbx : Product mul b x bx) (hby : Product mul b y byv)
    (h : Meets w D mul F i bx j byv) : Meets w D mul F i x j y := by
  obtain ⟨k,z,hk,hbxz,hbyz⟩ := h
  obtain ⟨_,f,hf,hbxf⟩ := hbxz
  obtain ⟨_,g,hg,hbyg⟩ := hbyz
  obtain ⟨_,_,_,ni,nk,_,_,hfD,_⟩ := (hF i k f).mp hf
  obtain ⟨_,_,_,nj,nk',_,_,hgD,_⟩ := (hF j k g).mp hg
  obtain ⟨xf,hxfD,hxf⟩ := (hm.2.1 x hx).1 f hfD
  obtain ⟨yg,hygD,hyg⟩ := (hm.2.1 y hy).1 g hgD
  have hbxf' := (hm.2.2 b x f bx xf z hb hx hfD hbx hxf).mp hbxf
  have hbyg' := (hm.2.2 b y g byv yg z hb hy hgD hby hyg).mp hbyg
  have he := (hm.2.1 b hb).2.2 xf yg z hxfD hygD hbxf' hbyg'
  exact ⟨k,yg,hk,⟨hx,f,hf,he ▸ hxf⟩,hy,g,hg,hyg⟩

def TransitionGraphs (w D mul F : M.Carrier .set) : Prop :=
  ∀ i j, (Project.FirstOrderSemantics.reduct M).mem i w →
    (Project.FirstOrderSemantics.reduct M).mem j w → NatLe i j →
      ∃ r, MapsTo D D r ∧ TransitionGraph D mul F i j r

def DirectedLaws (w D mul F : M.Carrier .set) : Prop :=
  (∀ i x, (Project.FirstOrderSemantics.reduct M).mem i w →
    (Project.FirstOrderSemantics.reduct M).mem x D → Transition D mul F i i x x) ∧
  (∀ i j k x y z, Transition D mul F i j x y → Transition D mul F j k y z → Transition D mul F i k x z) ∧
  (∀ i j b x y bx byv, (Project.FirstOrderSemantics.reduct M).mem b D →
    (Project.FirstOrderSemantics.reduct M).mem x D → (Project.FirstOrderSemantics.reduct M).mem y D →
    Product mul b x bx → Product mul b y byv →
      (Transition D mul F i j bx byv ↔ Transition D mul F i j x y))

def MeetsLaws (w D mul F : M.Carrier .set) : Prop :=
  (∀ i x, (Project.FirstOrderSemantics.reduct M).mem i w →
    (Project.FirstOrderSemantics.reduct M).mem x D → Meets w D mul F i x i x) ∧
  (∀ i x j y, Meets w D mul F i x j y → Meets w D mul F j y i x) ∧
  (∀ i x j y k z, Meets w D mul F i x j y → Meets w D mul F j y k z → Meets w D mul F i x k z) ∧
  (∀ i j x y, Transition D mul F i j x y → Meets w D mul F i x j y) ∧
  (∀ i j b x y bx byv, (Project.FirstOrderSemantics.reduct M).mem b D →
    (Project.FirstOrderSemantics.reduct M).mem x D → (Project.FirstOrderSemantics.reduct M).mem y D →
    Product mul b x bx → Product mul b y byv →
      (Meets w D mul F i bx j byv ↔ Meets w D mul F i x j y))

def transitionGraph {m : Nat} (D mul F i j r : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ 1 0))
    (transition D.succ.succ mul.succ.succ F.succ.succ i.succ.succ j.succ.succ 1 0)))

theorem transitionGraph_freeClosed {m : Nat} (D mul F i j r : Fin m) :
    (transitionGraph D mul F i j r).FreeClosed := by
  simp -implicitDefEqProofs [transitionGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,transition_freeClosed]

theorem transitionGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul F i j r : Fin m) :
    Project.Formula.satisfies env (transitionGraph D mul F i j r) ↔
      TransitionGraph (env.bound D) (env.bound mul) (env.bound F) (env.bound i) (env.bound j) (env.bound r) := by
  simp only [transitionGraph,TransitionGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,transition_semantics hM]
  rfl

def meets {m : Nat} (w D mul F i x j y : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ))
    (.conj (transition D.succ.succ mul.succ.succ F.succ.succ i.succ.succ 1 x.succ.succ 0)
      (transition D.succ.succ mul.succ.succ F.succ.succ j.succ.succ 1 y.succ.succ 0))))

theorem meets_freeClosed {m : Nat} (w D mul F i x j y : Fin m) :
    (meets w D mul F i x j y).FreeClosed := by
  simp -implicitDefEqProofs [meets,Definitional.Formula.FreeClosed,transition_freeClosed]

theorem meets_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F i x j y : Fin m) :
    Project.Formula.satisfies env (meets w D mul F i x j y) ↔
      Meets (env.bound w) (env.bound D) (env.bound mul) (env.bound F) (env.bound i) (env.bound x) (env.bound j) (env.bound y) := by
  simp only [meets,Meets,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,transition_semantics hM]
  rfl

def transitionGraphs {m : Nat} (w D mul F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound w.succ.succ)) (.imp (.mem (.bound 0) (.bound w.succ.succ))
    (.imp (natLeF (1 : Fin (m+2)) 0) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0
    D.succ.succ.succ D.succ.succ.succ)) (transitionGraph D.succ.succ.succ mul.succ.succ.succ F.succ.succ.succ 2
    1 0))))))))

theorem transitionGraphs_freeClosed {m : Nat} (w D mul F : Fin m) : (transitionGraphs w D mul F).FreeClosed := by
  simp -implicitDefEqProofs [transitionGraphs,Definitional.Formula.FreeClosed,transitionGraph_freeClosed,natLeF_freeClosed,ProjectSyntax.freeClosed]

theorem transitionGraphs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F : Fin m) :
    Project.Formula.satisfies env (transitionGraphs w D mul F) ↔
      TransitionGraphs (env.bound w) (env.bound D) (env.bound mul) (env.bound F) := by
  simp only [transitionGraphs,TransitionGraphs,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),natLeF_semantics hM,transitionGraph_semantics hM]
  rfl

def directedLaws {m : Nat} (w D mul F : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound w.succ.succ)) (.imp (.mem (.bound 0) (.bound
    D.succ.succ)) (transition D.succ.succ mul.succ.succ F.succ.succ 1 1 0 0))))) (.conj (.forallE (.forallE
    (.forallE (.forallE (.forallE (.forallE (.imp (transition D.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ 5 4 2 1) (.imp (transition
    D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ 4 3 1 0)
    (transition D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ.succ 5 3 2 0))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.forallE (.imp (.mem (.bound 4) (.bound D.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 3)
    (.bound D.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 2) (.bound
    D.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (product
    mul.succ.succ.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id (product
    mul.succ.succ.succ.succ.succ.succ.succ 4 2 0)) (.iff (transition D.succ.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ 6 5 1 0) (transition
    D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ.succ.succ 6 5 3 2))))))))))))))))

theorem directedLaws_freeClosed {m : Nat} (w D mul F : Fin m) : (directedLaws w D mul F).FreeClosed := by
  simp -implicitDefEqProofs [directedLaws,Definitional.Formula.FreeClosed,transition_freeClosed,ProjectSyntax.freeClosed]

theorem directedLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F : Fin m) :
    Project.Formula.satisfies env (directedLaws w D mul F) ↔
      DirectedLaws (env.bound w) (env.bound D) (env.bound mul) (env.bound F) := by
  simp only [directedLaws,DirectedLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),
    transition_semantics hM]
  rfl

def meetsLaws {m : Nat} (w D mul F : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (.bound w.succ.succ)) (.imp (.mem (.bound 0) (.bound
    D.succ.succ)) (meets w.succ.succ D.succ.succ mul.succ.succ F.succ.succ 1 0 1 0))))) (.conj (.forallE
    (.forallE (.forallE (.forallE (.imp (meets w.succ.succ.succ.succ D.succ.succ.succ.succ
    mul.succ.succ.succ.succ F.succ.succ.succ.succ 3 2 1 0) (meets w.succ.succ.succ.succ D.succ.succ.succ.succ
    mul.succ.succ.succ.succ F.succ.succ.succ.succ 1 0 3 2)))))) (.conj (.forallE (.forallE (.forallE (.forallE
    (.forallE (.forallE (.imp (meets w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ 5 4 3 2) (.imp (meets
    w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ.succ 3 2 1 0) (meets w.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ 5 4 1
    0))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp (transition D.succ.succ.succ.succ
    mul.succ.succ.succ.succ F.succ.succ.succ.succ 3 2 1 0) (meets w.succ.succ.succ.succ D.succ.succ.succ.succ
    mul.succ.succ.succ.succ F.succ.succ.succ.succ 3 1 2 0)))))) (.forallE (.forallE (.forallE (.forallE
    (.forallE (.forallE (.forallE (.imp (.mem (.bound 4) (.bound D.succ.succ.succ.succ.succ.succ.succ)) (.imp
    (.mem (.bound 3) (.bound D.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 2) (.bound
    D.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (product
    mul.succ.succ.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id (product
    mul.succ.succ.succ.succ.succ.succ.succ 4 2 0)) (.iff (meets w.succ.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ.succ.succ 6 1 5 0) (meets w.succ.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ.succ.succ 6 3 5 2))))))))))))))))))

theorem meetsLaws_freeClosed {m : Nat} (w D mul F : Fin m) : (meetsLaws w D mul F).FreeClosed := by
  simp -implicitDefEqProofs [meetsLaws,Definitional.Formula.FreeClosed,meets_freeClosed,transition_freeClosed,ProjectSyntax.freeClosed]

theorem meetsLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul F : Fin m) :
    Project.Formula.satisfies env (meetsLaws w D mul F) ↔
      MeetsLaws (env.bound w) (env.bound D) (env.bound mul) (env.bound F) := by
  simp only [meetsLaws,MeetsLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),
    transition_semantics hM,meets_semantics hM]
  rfl

theorem directed_laws {w D mul e zero a node F T : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hF : FactorTable w D mul node F)
    (hL : TableLaws w mul e zero a node F T) : DirectedLaws w D mul F := by
  refine ⟨fun i x hi hx => transition_self hm hL hi hx,
    fun i j k x y z hxy hyz => transition_comp hm hF hL hxy hyz,?_⟩
  intro i j b x y bx byv hb hx hy hbx hby
  exact ⟨transition_reflect_left hm hF hb hx hy hbx hby,transition_left hm hF hb hbx hby⟩

theorem meets_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node F T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hp : Path w D mul e zero a node)
    (hF : FactorTable w D mul node F) (hL : TableLaws w mul e zero a node F T) : MeetsLaws w D mul F := by
  refine ⟨fun i x hi hx => meets_refl hm hL hi hx,fun i x j y h => meets_symm h,
    fun i x j y k z hxy hyz => meets_trans hM hw hm hp hF hL hxy hyz,
    fun i j x y h => meets_transition hm hF hL h,?_⟩
  intro i j b x y bx byv hb hx hy hbx hby
  exact ⟨meets_reflect_left hm hF hb hx hy hbx hby,meets_left hm hF hb hbx hby⟩

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7 (.imp (Project.Formula.isOmega (.bound 0))
    (.imp (.forallE (.neg (.mem (.bound 0) (.bound 5))))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 7) 2 3))
        (.imp (path (0 : Fin 7) 1 2 3 4 5 6)
          (.existsE (.existsE (.conj (orderedPairs (2 : Fin 9) 1)
            (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 9) 1 3))
              (.conj (factorTable (2 : Fin 9) 3 4 8 0)
                (.conj (transitionGraphs (2 : Fin 9) 3 4 0)
                  (.conj (directedLaws (2 : Fin 9) 3 4 0) (meetsLaws (2 : Fin 9) 3 4 0))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    path_freeClosed,orderedPairs_freeClosed,factorTable_freeClosed,transitionGraphs_freeClosed,
    directedLaws_freeClosed,meetsLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),path_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,orderedPairs_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),factorTable_semantics hM,transitionGraphs_semantics hM,
    directedLaws_semantics hM,meetsLaws_semantics hM]
  intro hw hz hm hp
  obtain ⟨pairs,hpairs⟩ := exists_ordered_pairs hM (bound 0)
  obtain ⟨F,hFm,hF⟩ := exists_factor_table hM hm hp hpairs
  obtain ⟨T,_,hT⟩ := exists_terminal_table hM hm hp
  have hL := table_laws hM hw hz hm hp hF hT
  exact ⟨pairs,F,hpairs,hFm,hF,fun i j hi hj hij => exists_transition_graph hM hm hp hF hi hj hij,
    directed_laws hm hF hL,meets_laws hM hw hm hp hF hL⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeTransitions
