/- Fixed AssignedGraphs.GraphWitness/GraphHolds/graphWitness_mono/graphRelation:25-66.
The literal source assignment, actual label name and actual condition encoding
are retained. Density is over all internal conditions of the same forcing.
Consumers: graphWitness_bounds/move, graphRelation_one/inj, assignmentGraph. -/
import PPAC.Migration.ForcingAssignedCompatibility
import PPAC.Migration.ForcingLabelNames

namespace PPAC.Migration.ForcingAssignedGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingAssigned (Assigned assigned)
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Witness (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k)
    (families : Fin 16 → Fin k) (p x y : M.Carrier .set) : Prop :=
  ∃ d vertex j tau r index U z labelName,
    (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)) ∧
    ConstructionComponentCarrier.Code vertex r index U ∧
    ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) r index U ∧
    (Project.FirstOrderSemantics.reduct M).mem j (env I) ∧
    ForcingTailCodes.Entry (fun i => env (rho i)) (env G) (env F) (env bound) vertex tau ∧
    ForcingSupportingRoot.Code z d r ∧
    MapRel (orderFormula (rho 0) mul) env p z ∧
    Assigned hM env rho I G F mul q bound labels E w top K B zero Q families d vertex j tau ∧
    ForcingLabelNames.Label (env (rho 6)) (env K) (env labelMap) (env top) j (env bit) labelName ∧
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x labelName p ∧
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y tau p

def witness {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (base : Fin k → Fin m) (p x y : Fin m) : Project.Formula 1 m :=
  let up : Fin k → Fin (m+9) := fun i => (base i).succ.succ.succ.succ.succ.succ.succ.succ.succ
  let shift : Fin m → Fin (m+9) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound (8 : Fin (m+9))) (.bound (up (rho 3))))
    (.conj (ConstructionComponentCarrier.code 7 4 3 2)
    (.conj (ConstructionComponentVertices.vertex (up (rho 0)) (up I) (up mul) (up q) 4 3 2)
    (.conj (.mem (.bound (6 : Fin (m+9))) (.bound (up I)))
    (.conj (ForcingTailCodes.entry (fun j => up (rho j)) (up G) (up F) (up bound) 7 5)
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 1 8 4))
    (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) up (shift p) 1))
    (.conj (assigned (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up w) (up top) (up K) (up B) (up zero) (up Q) (fun j => up (families j)) 8 7 6 5)
    (.conj (ProjectSyntax.encode id (ForcingLabelNames.label (up (rho 6)) (up K) (up labelMap) (up top) 6 (up bit) 0))
    (.conj (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) up (up (rho 6)) (shift x) 0 (shift p)))
    (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) up (up (rho 6)) (shift y) 5 (shift p))))))))))))))))))))))

theorem witness_freeClosed {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (base : Fin k → Fin m) (p x y : Fin m) : (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families base p x y).FreeClosed := by
  simp -implicitDefEqProofs [witness,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed,ForcingTailCodes.entry_freeClosed,ForcingAssigned.assigned_freeClosed]

theorem witness_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (base : Fin k → Fin m) (p x y : Fin m) :
    Project.Formula.satisfies env (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families base p x y) ↔
      Witness hM (fun i => env.bound (base i)) rho I G F mul q bound labels E w top K B zero Q labelMap bit families (env.bound p) (env.bound x) (env.bound y) := by
  simp only [witness,Witness,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ForcingTailCodes.entry_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportingRoot.code_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),ForcingAssigned.assigned_semantics hM,ForcingLabelNames.label_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M)]
  apply exists_congr
  intro d
  apply exists_congr
  intro vertex
  apply exists_congr
  intro j
  apply exists_congr
  intro tau
  apply exists_congr
  intro r
  apply exists_congr
  intro index
  apply exists_congr
  intro U
  apply exists_congr
  intro z
  apply exists_congr
  intro labelName
  let other : Fin (m+9) → M.Carrier .set := Fin.cases labelName (Fin.cases z (Fin.cases U (Fin.cases index (Fin.cases r (Fin.cases tau (Fin.cases j (Fin.cases vertex (Fin.cases d (env.bound)))))))))
  let up : Fin k → Fin (m+9) := fun i => (base i).succ.succ.succ.succ.succ.succ.succ.succ.succ
  have he (i : Fin k) : other (up i) = env.bound (base i) := rfl
  have hAssign := ForcingAssigned.assigned_reindex hM (fun i => env.bound (base i)) other up he rho I G F mul q bound labels E w top K B zero Q families d vertex j tau
  refine and_congr Iff.rfl ?_
  refine and_congr Iff.rfl ?_
  refine and_congr Iff.rfl ?_
  refine and_congr Iff.rfl ?_
  refine and_congr Iff.rfl ?_
  refine and_congr Iff.rfl ?_
  refine and_congr Iff.rfl ?_
  exact and_congr hAssign Iff.rfl

def Holds (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k)
    (families : Fin 16 → Fin k) (p x y : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) ∧
    ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env r p →
      ∃ s, MapRel (orderFormula (rho 0) mul) env s r ∧ Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families s x y

def holds {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (base : Fin k → Fin m) (p x y : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound p) (.bound (base (rho 6))))
    (.forallE (.imp (.mem (.bound 0) (.bound ((base (rho 6)).succ)))
      (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => (base i).succ) 0 p.succ))
        (.existsE (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => (base i).succ.succ) 0 1))
          (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun i => (base i).succ.succ) 0 x.succ.succ y.succ.succ))))))

theorem holds_freeClosed {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (base : Fin k → Fin m) (p x y : Fin m) : (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families base p x y).FreeClosed := by
  simp -implicitDefEqProofs [holds,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,witness_freeClosed]

theorem holds_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k)
    (base : Fin k → Fin m) (p x y : Fin m) :
    Project.Formula.satisfies env (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families base p x y) ↔
      Holds hM (fun i => env.bound (base i)) rho I G F mul q bound labels E w top K B zero Q labelMap bit families (env.bound p) (env.bound x) (env.bound y) := by
  simp only [holds,Holds,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingMapConditions.rel_semantics (M := M),witness_semantics hM]
  rfl

theorem witness_condition (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k) {p x y : M.Carrier .set}
    (h : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) := by
  obtain ⟨d,vertex,j,tau,t,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,hpz,hAssigned,hLabel,hx,hy⟩ := h
  exact ForcingAtomicBasic.condition hM hx

theorem witness_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) {p r x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hr : (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6))) (hrp : MapRel (orderFormula (rho 0) mul) env r p)
    (h : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families r x y := by
  obtain ⟨d,vertex,j,tau,t,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,hpz,hAssigned,hLabel,hx,hy⟩ := h
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have hpW := ForcingAtomicBasic.condition hM hx
  have hzW := ForcingSupportingRoot.code_mem hp ((hp.2.2.1 d).mp hd) hVertex.1 hz
  exact ⟨d,vertex,j,tau,t,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,
    hpre.2 r p z hr hpW hzW hrp hpz,hAssigned,hLabel,
    ForcingAtomicBasic.eq_mono hM hpre hr hrp hx,ForcingAtomicBasic.eq_mono hM hpre hr hrp hy⟩

theorem witness_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) {p x y u v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hxu : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x u p) (hyv : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y v p)
    (h : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p u v := by
  obtain ⟨d,vertex,j,tau,t,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,hpz,hAssigned,hLabel,hx,hy⟩ := h
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ⟨d,vertex,j,tau,t,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,hpz,hAssigned,hLabel,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM hxu) hx,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_symm hM hyv) hy⟩

theorem holds_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) {p r x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hr : (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6))) (hrp : MapRel (orderFormula (rho 0) mul) env r p)
    (h : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families r x y := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  exact ⟨hr,fun t ht htr => h.2 t ht (hpre.2 t r p ht hr h.1 htr hrp)⟩

theorem witness_holds (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) {p x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (h : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  refine ⟨witness_condition hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families h,?_⟩
  intro r hr hrp
  exact ⟨r,hpre.1 r hr,witness_mono hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp hr hrp h⟩

theorem holds_regular (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) {p x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hpW : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (h : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) → MapRel (orderFormula (rho 0) mul) env r p →
      ∃ t, MapRel (orderFormula (rho 0) mul) env t r ∧ Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families t x y) : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  refine ⟨hpW,?_⟩
  intro r hr hrp
  obtain ⟨t,htr,ht⟩ := h r hr hrp
  obtain ⟨z,hzt,hz⟩ := ht.2 t ht.1 (hpre.1 t ht.1)
  exact ⟨z,hpre.2 z t r (witness_condition hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families hz) ht.1 hr hzt htr,hz⟩

theorem holds_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) {p x y u v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hxu : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x u p) (hyv : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y v p) :
    Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y ↔ Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p u v := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  have step {x y u v : M.Carrier .set} (hxu : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x u p) (hyv : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y v p)
      (h : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p u v := by
    refine ⟨h.1,?_⟩
    intro r hr hrp
    obtain ⟨t,htr,ht⟩ := h.2 r hr hrp
    have htW := witness_condition hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families ht
    have htp := hpre.2 t r p htW hr h.1 htr hrp
    exact ⟨t,htr,witness_congr hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
      (ForcingAtomicBasic.eq_mono hM hpre htW htp hxu) (ForcingAtomicBasic.eq_mono hM hpre htW htp hyv) ht⟩
  exact ⟨step hxu hyv,step (ForcingAtomicBasic.eq_symm hM hxu) (ForcingAtomicBasic.eq_symm hM hyv)⟩

def lawsSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one p r x y u v : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.conj (.imp (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y)
    (.mem (.bound p) (.bound (rho 6))))
    (.conj (.imp (.mem (.bound r) (.bound (rho 6)))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) id r p))
    (.imp (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y)
    (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id r x y))))
    (.conj (.imp (.mem (.bound r) (.bound (rho 6)))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) id r p))
    (.imp (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y)
    (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id r x y))))
    (.conj (.imp (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y)
    (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y))
    (.conj (.imp (.mem (.bound p) (.bound (rho 6)))
    (.imp (.forallE (.imp (.mem (.bound 0) (.bound (rho 6).succ))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) Fin.succ 0 p.succ))
    (.existsE (.conj (ProjectSyntax.encode id (ReplacementPredicates.rel (orderFormula (rho 0) mul) (fun i => i.succ.succ) 0 1))
    (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun i => i.succ.succ) 0 x.succ.succ y.succ.succ))))))
    (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y)))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) x u p))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) y v p))
    (.iff (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y) (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p u v)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,witness_freeClosed,holds_freeClosed]

theorem laws_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one p r x y u v : Fin k) (families : Fin 16 → Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (lawsSentence rho I G F mul q bound labels E w top K B zero Q labelMap bit one p r x y u v families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),witness_semantics hM,holds_semantics hM]
  intro hm hp
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact witness_condition hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families
  · exact witness_mono hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  · exact holds_mono hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  · exact witness_holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  · exact holds_regular hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp
  · exact holds_congr hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp

theorem laws_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q labelMap bit one p r x y u v : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (lawsSentence rho I G F mul q bound labels E w top K B zero Q labelMap bit one p r x y u v families)) := by
  apply ModelTransfer.derives
  intro M hM
  exact laws_models rho I G F mul q bound labels E w top K B zero Q labelMap bit one p r x y u v families hM

end PPAC.Migration.ForcingAssignedGraph
