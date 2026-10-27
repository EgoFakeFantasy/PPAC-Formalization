/- Pinned MergerWords.copiesAct/copiesAct_copy/copiesRightFreeAction.
Actual internal right action on the prescribed quotient; injectivity is in the
OLD factor, exactly as RightFreeAction requires, not cancellation of the copy.
Consumer: literal Merger Word.act/product and its left cancellation. -/
import PPAC.Migration.ConstructionMergerCopies

namespace PPAC.Migration.ConstructionMergerAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerRelations (Prescription Valid product_range rel_mul)
open ConstructionMergerCopies (Copies Projection EqualityLaw representative copy_eq_iff copy_injective)
open ConstructionProbeLetters (Representatives exists_representatives)
open ConstructionProbeAction (projected projected_indices projected_range)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Act (D mul projection c m d : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem m D ∧ ∃ i x xm,
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x c ∧
      Product mul x m xm ∧ Product projection i xm d

theorem act_total (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection c m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C)
    (hL : Copies n D mul P C L) (hp : MapsTo C L projection) (hProjection : Projection n D mul P C projection)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) (hmD : (Project.FirstOrderSemantics.reduct M).mem m D) :
    ∃ d, (Project.FirstOrderSemantics.reduct M).mem d L ∧ Act D mul projection c m d := by
  obtain ⟨i,x,hi,hx,hxc⟩ := representative hC hL hProjection hc
  obtain ⟨xm,hxmD,hxm⟩ := (hm.2.1 x hx).1 m hmD
  obtain ⟨d,hd,hxmd⟩ := projected hM hC hp hi hxmD
  exact ⟨d,hd,hmD,i,x,xm,hx,hxc,hxm,hxmd⟩

theorem act_unique {n D mul e P projection c m d f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P) (hEq : EqualityLaw n D mul P projection)
    (hd : Act D mul projection c m d) (hf : Act D mul projection c m f) : d = f := by
  obtain ⟨hmD,i,x,xm,_,hxc,hxm,hxmd⟩ := hd
  obtain ⟨_,j,y,ym,_,hyc,hym,hymf⟩ := hf
  have hrel := (copy_eq_iff hEq hxc hyc).mp rfl
  exact (copy_eq_iff hEq hxmd hymf).mpr (rel_mul hm hP hmD hrel hxm hym)

theorem act_copy_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection i x xm c m d : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hp : MapsTo C L projection) (hEq : EqualityLaw n D mul P projection)
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m D)
    (hxc : Product projection i x c) (hxm : Product mul x m xm) :
    Act D mul projection c m d ↔ Product projection i xm d := by
  obtain ⟨hi,hx⟩ := projected_indices hC hp hxc
  constructor
  · intro hd
    obtain ⟨q,_,hxmq⟩ := projected hM hC hp hi (product_range hm hx hmD hxm)
    have hq : Act D mul projection c m q := ⟨hmD,i,x,xm,hx,hxc,hxm,hxmq⟩
    exact (act_unique hm hP hEq hq hd) ▸ hxmq
  · exact fun hd => ⟨hmD,i,x,xm,hx,hxc,hxm,hd⟩

theorem act_one {n D mul e P C L projection c : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C)
    (hL : Copies n D mul P C L) (hProjection : Projection n D mul P C projection)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) : Act D mul projection c e c := by
  obtain ⟨i,x,_,hx,hxc⟩ := representative hC hL hProjection hc
  exact ⟨hm.1.1,i,x,x,hx,hxc,((hm.1.2 x hx x).2).mpr rfl,hxc⟩

theorem act_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection c x y xy d f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hp : MapsTo C L projection) (hEq : EqualityLaw n D mul P projection)
    (hxy : Product mul x y xy) (hcxd : Act D mul projection c x d) (hdyf : Act D mul projection d y f) :
    Act D mul projection c xy f := by
  obtain ⟨hx,i,a,ax,ha,hac,hax,haxd⟩ := hcxd
  have hy := hdyf.1
  have haxD := product_range hm ha hx hax
  obtain ⟨axy,haxyD,haxy⟩ := (hm.2.1 ax haxD).1 y hy
  have haxyf := (act_copy_iff hM hm hP hC hp hEq hy haxd haxy).mp hdyf
  exact ⟨product_range hm hx hy hxy,i,a,axy,ha,hac,
    (hm.2.2 a x y ax xy axy ha hx hy hax hxy).mp haxy,haxyf⟩

theorem factor_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection c x y d : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hp : MapsTo C L projection) (hEq : EqualityLaw n D mul P projection)
    (hx : Act D mul projection c x d) (hy : Act D mul projection c y d) : x = y := by
  obtain ⟨hxD,i,a,ax,ha,hac,hax,haxd⟩ := hx
  obtain ⟨ay,_,hay⟩ := (hm.2.1 a ha).1 y hy.1
  have hayd := (act_copy_iff hM hm hP hC hp hEq hy.1 hac hay).mp hy
  have hEqProd := copy_injective hC hp hEq haxd hayd
  exact (hm.2.1 a ha).2.2 x y ax hxD hy.1 hax (hEqProd.symm ▸ hay)

def act {m0 : Nat} (D mul projection c m d : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.mem (.bound m) (.bound D)) (.existsE (.existsE (.existsE (.conj (.mem (.bound 1) (.bound
  D.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ
  2 1 c.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ 1
  m.succ.succ.succ 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ 2 0
  d.succ.succ.succ)))))))))

theorem act_freeClosed {m0 : Nat} (D mul projection c m d : Fin m0) : (act D mul projection c m d).FreeClosed := by
  simp -implicitDefEqProofs [act,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem act_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D mul projection c m d : Fin m0) :
    Project.Formula.satisfies env (act D mul projection c m d) ↔ Act (env.bound D) (env.bound mul) (env.bound projection) (env.bound c) (env.bound m) (env.bound d) := by
  simp only [act,Act,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def actPair {m0 : Nat} (D mul projection p d : Fin m0) : Project.Formula 1 m0 :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0)) (act
  D.succ.succ mul.succ.succ projection.succ.succ 1 0 d.succ.succ))))

theorem actPair_freeClosed {m0 : Nat} (D mul projection p d : Fin m0) : (actPair D mul projection p d).FreeClosed := by
  simp -implicitDefEqProofs [actPair,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,act_freeClosed]

theorem actPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D mul projection p d : Fin m0) :
    Project.Formula.satisfies env (actPair D mul projection p d) ↔ (∃ c m, PureKuratowski.Code M (env.bound p) c m ∧ Act (env.bound D) (env.bound mul) (env.bound projection) c m (env.bound d)) := by
  simp only [actPair,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM,act_semantics hM]
  rfl

def ActionTable (D mul projection A : M.Carrier .set) : Prop := ∀ c m d,
  Product A c m d ↔ Act D mul projection c m d

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hL : Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProjection : Projection n D mul P C projection)
    (hEq : EqualityLaw n D mul P projection) :
    ∃ J A, Representatives L D J ∧ MapsTo J L A ∧ ActionTable D mul projection A := by
  obtain ⟨J,hJ⟩ := exists_representatives hM L D
  let schema : Project.BinarySchema 3 := { body := actPair 2 3 4 1 0, freeClosed := actPair_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases D (Fin.cases mul (fun _ => projection)), free := fun _ => D }
  have he : ∀ p d, schema.denote env p d ↔ ∃ c m, PureKuratowski.Code M p c m ∧ Act D mul projection c m d :=
    fun p d => actPair_semantics hM ((env.push p).push d) 2 3 4 1 0
  obtain ⟨A,hA,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := L) (by
      intro p hpJ
      obtain ⟨c,m,hc,hmD,hcode⟩ := (hJ p).mp hpJ
      obtain ⟨d,_,hact⟩ := act_total hM hm hC hL hp hProjection hc hmD
      exact ⟨d,(he p d).mpr ⟨c,m,hcode,hact⟩⟩) (by
      intro p _ d f hd hf
      obtain ⟨c,m,hcode,hd⟩ := (he p d).mp hd
      obtain ⟨c',m',hcode',hf⟩ := (he p f).mp hf
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact act_unique hm hP hEq hd hf) (by
      intro p d _ hd
      obtain ⟨c,m,_,hact⟩ := (he p d).mp hd
      obtain ⟨_,i,x,xm,_,_,_,hxmD⟩ := hact
      exact projected_range hp hxmD)
  refine ⟨J,A,hJ,(ForcingSupportSize.native_mapsTo hM J L A).mpr hA,fun c m d => ?_⟩
  constructor
  · rintro ⟨p,hcode,hpad⟩
    obtain ⟨_,hval⟩ := (hgraph p d).mp hpad
    obtain ⟨c',m',hcode',hact⟩ := (he p d).mp hval
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact hact
  · intro hact
    have hcopy := hact
    obtain ⟨hmD,i,x,xm,_,hxc,_,_⟩ := hcopy
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM c m
    exact ⟨p,hcode,(hgraph p d).mpr ⟨(hJ p).mpr ⟨c,m,projected_range hp hxc,hmD,hcode⟩,
      (he p d).mpr ⟨c,m,hcode,hact⟩⟩⟩

def RightFreeAction (mul e L A : M.Carrier .set) : Prop :=
  (∀ c, (Project.FirstOrderSemantics.reduct M).mem c L → Product A c e c) ∧
  (∀ c x y xy d f, Product mul x y xy → Product A c x d → Product A d y f → Product A c xy f) ∧
  (∀ c x y z, Product A c x z → Product A c y z → x = y)

def CopyLaw (D mul projection A : M.Carrier .set) : Prop :=
  ∀ i x xm c m d, (Project.FirstOrderSemantics.reduct M).mem m D → Product projection i x c →
    Product mul x m xm → (Product A c m d ↔ Product projection i xm d)

theorem right_free_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P C L projection A : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P)
    (hC : Representatives n D C) (hL : Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProjection : Projection n D mul P C projection)
    (hEq : EqualityLaw n D mul P projection) (hA : ActionTable D mul projection A) :
    RightFreeAction mul e L A ∧ CopyLaw D mul projection A := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · exact fun c hc => (hA c e c).mpr (act_one hm hC hL hProjection hc)
  · exact fun c x y xy d f hxy hcx hdy => (hA c xy f).mpr
      (act_mul hM hm hP hC hp hEq hxy ((hA c x d).mp hcx) ((hA d y f).mp hdy))
  · exact fun c x y z hx hy => factor_injective hM hm hP hC hp hEq ((hA c x z).mp hx) ((hA c y z).mp hy)
  · exact fun i x xm c m d hmD hxc hxm => (hA c m d).trans (act_copy_iff hM hm hP hC hp hEq hmD hxc hxm)

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul e P : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hP : Prescription n D P) (hValid : Valid n D mul P) :
    ∃ C L projection J A, Representatives n D C ∧ MapsTo C L projection ∧
      Copies n D mul P C L ∧ Projection n D mul P C projection ∧ EqualityLaw n D mul P projection ∧
      Representatives L D J ∧ MapsTo J L A ∧ ActionTable D mul projection A ∧
      RightFreeAction mul e L A ∧ CopyLaw D mul projection A := by
  obtain ⟨C,L,projection,hC,hp,hL,hProjection,hEq⟩ := ConstructionMergerCopies.exists_quotient hM n D mul P hValid
  obtain ⟨J,A,hJ,hA,hTable⟩ := exists_action hM hm hP hC hL hp hProjection hEq
  obtain ⟨hLaws,hCopy⟩ := right_free_laws hM hm hP hC hL hp hProjection hEq hTable
  exact ⟨C,L,projection,J,A,hC,hp,hL,hProjection,hEq,hJ,hA,hTable,hLaws,hCopy⟩

def actionTable {m0 : Nat} (D mul projection A : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product A.succ.succ.succ
  2 1 0)) (act D.succ.succ.succ mul.succ.succ.succ projection.succ.succ.succ 2 1 0)))))

theorem actionTable_freeClosed {m0 : Nat} (D mul projection A : Fin m0) : (actionTable D mul projection A).FreeClosed := by
  simp -implicitDefEqProofs [actionTable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,act_freeClosed]

theorem actionTable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D mul projection A : Fin m0) :
    Project.Formula.satisfies env (actionTable D mul projection A) ↔ ActionTable (env.bound D) (env.bound mul) (env.bound projection) (env.bound A) := by
  simp only [actionTable,ActionTable,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),act_semantics hM]
  rfl

def rightFreeAction {m0 : Nat} (mul e L A : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.forallE (.imp (.mem (.bound 0) (.bound L.succ)) (ProjectSyntax.encode id
  (ForcingDiagramOrder.product A.succ 0 e.succ 0)))) (.conj (.forallE (.forallE (.forallE (.forallE
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul.succ.succ.succ.succ.succ.succ 4 3 2)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  A.succ.succ.succ.succ.succ.succ 5 4 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  A.succ.succ.succ.succ.succ.succ 1 3 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
  A.succ.succ.succ.succ.succ.succ 5 2 0))))))))))) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product A.succ.succ.succ.succ 3 2 0)) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product A.succ.succ.succ.succ 3 1 0))
  (Project.Formula.extensionalEq (.bound 2) (.bound 1))))))))))

theorem rightFreeAction_freeClosed {m0 : Nat} (mul e L A : Fin m0) : (rightFreeAction mul e L A).FreeClosed := by
  simp -implicitDefEqProofs [rightFreeAction,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem rightFreeAction_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (mul e L A : Fin m0) :
    Project.Formula.satisfies env (rightFreeAction mul e L A) ↔ RightFreeAction (env.bound mul) (env.bound e) (env.bound L) (env.bound A) := by
  simp only [rightFreeAction,RightFreeAction,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def copyLaw {m0 : Nat} (D mul projection A : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 1) (.bound
  D.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  projection.succ.succ.succ.succ.succ.succ 5 4 2)) (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ 4 1 3)) (.iff (ProjectSyntax.encode id
  (ForcingDiagramOrder.product A.succ.succ.succ.succ.succ.succ 2 1 0)) (ProjectSyntax.encode id
  (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ.succ 5 3 0))))))))))))

theorem copyLaw_freeClosed {m0 : Nat} (D mul projection A : Fin m0) : (copyLaw D mul projection A).FreeClosed := by
  simp -implicitDefEqProofs [copyLaw,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem copyLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (D mul projection A : Fin m0) :
    Project.Formula.satisfies env (copyLaw D mul projection A) ↔ CopyLaw (env.bound D) (env.bound mul) (env.bound projection) (env.bound A) := by
  simp only [copyLaw,CopyLaw,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionMergerAction
