/- Pinned ConservativeHulls.factor/join/operations/exists_countable_conservative:225-338.
Actual consumers: CellTowers.hull/factors/joins/countable/contains/dependencies_closed
at 330-348 and ConcreteQuotients.factor_eq at 118. Reuse native internal omega
closure, actual set functions and the original conservative-inclusion proof. -/
import PPAC.Migration.ConstructionCountableHull
import PPAC.Migration.ConstructionConservativeHull
import PPAC.Migration.ConstructionProbeGateCap
import PPAC.Migration.ConstructibleSource
import PPAC.Migration.ConstructionDirectedCardinality

namespace PPAC.Migration.ConstructionCountableConservativeHull
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The unique right factor, or the original unit when no factor exists. -/
def Factor (D mul e x y z : M.Carrier .set) : Prop :=
  ((Project.FirstOrderSemantics.reduct M).mem z D ∧ Product mul x z y) ∨
    (¬ Divides D mul x y) ∧ z = e

/-- The actual ambient cone join, or the original unit when none exists. -/
def Join (D mul e x y j : M.Carrier .set) : Prop :=
  ((Project.FirstOrderSemantics.reduct M).mem j D ∧ JoinProperty D mul x y j) ∨
    (¬ ∃ k, (Project.FirstOrderSemantics.reduct M).mem k D ∧ JoinProperty D mul x y k) ∧ j = e

def Operation (D mul e deps x y z : M.Carrier .set) : Prop :=
  Product mul x y z ∨ Factor D mul e x y z ∨ Join D mul e x y z ∨
    ∃ Y, PureKuratowski.PairMember M x Y deps ∧ (Project.FirstOrderSemantics.reduct M).mem z Y

def Row (D mul e deps x y Y : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z Y ↔ Operation D mul e deps x y z

def OperationGraph (D mul e deps B F : M.Carrier .set) : Prop := ∀ q Y,
  PureKuratowski.PairMember M q Y F ↔ (Project.FirstOrderSemantics.reduct M).mem q B ∧
    ∃ x y, PureKuratowski.Code M q x y ∧ Row D mul e deps x y Y

theorem factor_exists {D mul e x y : M.Carrier .set} (hm : LeftCancelMonoid D mul e) :
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧ Factor D mul e x y z := by
  classical
  by_cases h : Divides D mul x y
  · obtain ⟨z,hz,hp⟩ := h
    exact ⟨z,hz,Or.inl ⟨hz,hp⟩⟩
  · exact ⟨e,hm.1.1,Or.inr ⟨h,rfl⟩⟩

theorem factor_unique {D mul e x y z t : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hz : Factor D mul e x y z) (ht : Factor D mul e x y t) : z = t := by
  rcases hz with ⟨hz,hzP⟩ | ⟨hn,rfl⟩
  · rcases ht with ⟨ht,htP⟩ | ⟨hn,_⟩
    · exact (hm.2.1 x hx).2.2 z t y hz ht hzP htP
    · exact (hn ⟨z,hz,hzP⟩).elim
  · rcases ht with ⟨ht,htP⟩ | ⟨_,rfl⟩
    · exact (hn ⟨t,ht,htP⟩).elim
    · rfl

theorem factor_eq {D mul e x y z t : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hz : (Project.FirstOrderSemantics.reduct M).mem z D) (hp : Product mul x z y)
    (ht : Factor D mul e x y t) : t = z :=
  factor_unique hm hx ht (Or.inl ⟨hz,hp⟩)

theorem join_exists {D mul e x y : M.Carrier .set} (hm : LeftCancelMonoid D mul e) :
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j D ∧ Join D mul e x y j := by
  classical
  by_cases h : ∃ j, (Project.FirstOrderSemantics.reduct M).mem j D ∧ JoinProperty D mul x y j
  · obtain ⟨j,hj,hp⟩ := h
    exact ⟨j,hj,Or.inl ⟨hj,hp⟩⟩
  · exact ⟨e,hm.1.1,Or.inr ⟨h,rfl⟩⟩

theorem join_unique {D mul e x y j k : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hj : Join D mul e x y j) (hk : Join D mul e x y k) : j = k := by
  rcases hj with ⟨hj,hjp⟩ | ⟨hn,rfl⟩
  · rcases hk with ⟨hk,hkp⟩ | ⟨hn,_⟩
    · have hjj : Divides D mul j j := ⟨e,hm.1.1,(hm.1.2 j hj j).2.mpr rfl⟩
      have hkk : Divides D mul k k := ⟨e,hm.1.1,(hm.1.2 k hk k).2.mpr rfl⟩
      exact ConstructionProbeGateCap.divides_antisymm hm hc hj
        ((hjp k hk).mp ((hkp k hk).mpr hkk)) ((hkp j hj).mp ((hjp j hj).mpr hjj))
    · exact (hn ⟨j,hj,hjp⟩).elim
  · rcases hk with ⟨hk,hkp⟩ | ⟨_,rfl⟩
    · exact (hn ⟨k,hk,hkp⟩).elim
    · rfl

theorem row_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e deps x y Y Z : M.Carrier .set}
    (hY : Row D mul e deps x y Y) (hZ : Row D mul e deps x y Z) : Y = Z :=
  (ModelTransfer.extensionality hM).eq_of_same_members Y Z (fun z => (hY z).trans (hZ z).symm)

theorem row_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e P deps x y : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hP : (Project.FirstOrderSemantics.reduct M).IsPowerSetOf P D) (hdeps : MapsTo D P deps)
    (hCount : ∀ x Y, PureKuratowski.PairMember M x Y deps →
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Y w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y D) :
    ∃ Y, Row D mul e deps x y Y ∧ (Project.FirstOrderSemantics.reduct M).mem Y P ∧
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Y w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  let I := KuratowskiZF.interpretation hM
  obtain ⟨m,hmD,hmP⟩ := (hm.2.1 x hx).1 y hy
  obtain ⟨f,hfD,hf⟩ := factor_exists (x := x) (y := y) hm
  obtain ⟨j,hjD,hj⟩ := join_exists (x := x) (y := y) hm
  obtain ⟨Y0,hY0,_⟩ := hdeps.1.2 x hx
  obtain ⟨Y1,hY1⟩ := KP.exists_insert hKP Y0 m
  obtain ⟨Y2,hY2⟩ := KP.exists_insert hKP Y1 f
  obtain ⟨Y3,hY3⟩ := KP.exists_insert hKP Y2 j
  have hRow : Row D mul e deps x y Y3 := by
    intro z
    constructor
    · intro hz
      rcases (hY3 z).mp hz with hz | hz
      · rcases (hY2 z).mp hz with hz | hz
        · rcases (hY1 z).mp hz with hz | hz
          · exact Or.inr (Or.inr (Or.inr ⟨Y0,hY0,hz⟩))
          · exact Or.inl (hz.symm ▸ hmP)
        · exact Or.inr (Or.inl (hz.symm ▸ hf))
      · exact Or.inr (Or.inr (Or.inl (hz.symm ▸ hj)))
    · rintro (hp | hf' | hj' | ⟨Y,hY,hz⟩)
      · exact (hY3 z).mpr (Or.inl ((hY2 z).mpr (Or.inl ((hY1 z).mpr
          (Or.inr ((hm.2.1 x hx).2.1 y z m hy hp hmP))))))
      · exact (hY3 z).mpr (Or.inl ((hY2 z).mpr (Or.inr (factor_unique hm hx hf' hf))))
      · exact (hY3 z).mpr (Or.inr (join_unique hm hc hj' hj))
      · have he := ForcingConditionGraphs.function_unique hdeps.1 hY hY0
        exact (hY3 z).mpr (Or.inl ((hY2 z).mpr (Or.inl ((hY1 z).mpr (Or.inl (he ▸ hz))))))
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset Y3 D := by
    intro z hz
    rcases (hY3 z).mp hz with hz | rfl
    · rcases (hY2 z).mp hz with hz | rfl
      · rcases (hY1 z).mp hz with hz | rfl
        · exact (hP Y0).mp (hdeps.2 x Y0 hY0) z hz
        · exact hmD
      · exact hfD
    · exact hjD
  exact ⟨Y3,hRow,(hP Y3).mpr hSub,
    ZF.countable_insert_l I hZF hw
      (ZF.countable_insert_l I hZF hw (ZF.countable_insert_l I hZF hw (hCount x Y0 hY0) hY1) hY2) hY3⟩

def factor {m : Nat} (D mul e x y z : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (.mem (.bound z) (.bound D)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul x z y))) (.conj (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D mul x y)))
  (Project.Formula.extensionalEq (.bound z) (.bound e))))

theorem factor_freeClosed {m : Nat} (D mul e x y z : Fin m) :
    (factor D mul e x y z).FreeClosed := by
  simp -implicitDefEqProofs [factor,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem factor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e x y z : Fin m) :
    Project.Formula.satisfies env (factor D mul e x y z) ↔ Factor (env.bound D) (env.bound mul) (env.bound e) (env.bound x) (env.bound y) (env.bound z) := by
  simp only [factor,Factor,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def join {m : Nat} (D mul e x y j : Fin m) : Project.Formula 1 m :=
  (.disj (.conj (.mem (.bound j) (.bound D)) (ConstructionProbeCones.joinProperty D mul x y j))
  (.conj (.neg (.existsE (.conj (.mem (.bound (0 : Fin (m+1))) (.bound D.succ))
  (ConstructionProbeCones.joinProperty D.succ mul.succ x.succ y.succ (0 : Fin (m+1))))))
  (Project.Formula.extensionalEq (.bound j) (.bound e))))

theorem join_freeClosed {m : Nat} (D mul e x y j : Fin m) :
    (join D mul e x y j).FreeClosed := by
  simp -implicitDefEqProofs [join,Definitional.Formula.FreeClosed,ConstructionProbeCones.joinProperty_freeClosed]

theorem join_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e x y j : Fin m) :
    Project.Formula.satisfies env (join D mul e x y j) ↔ Join (env.bound D) (env.bound mul) (env.bound e) (env.bound x) (env.bound y) (env.bound j) := by
  simp only [join,Join,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionProbeCones.joinProperty_semantics hM]
  rfl

def operation {m : Nat} (D mul e deps x y z : Fin m) : Project.Formula 1 m :=
  (.disj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul x y z)) (.disj (factor D mul e x
  y z) (.disj (join D mul e x y z) (.existsE (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge deps.succ x.succ (0 : Fin (m+1)))) (.mem (.bound z.succ) (.bound (0 : Fin
  (m+1)))))))))

theorem operation_freeClosed {m : Nat} (D mul e deps x y z : Fin m) :
    (operation D mul e deps x y z).FreeClosed := by
  simp -implicitDefEqProofs [operation,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,factor_freeClosed,join_freeClosed]

theorem operation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e deps x y z : Fin m) :
    Project.Formula.satisfies env (operation D mul e deps x y z) ↔ Operation (env.bound D) (env.bound mul) (env.bound e) (env.bound deps) (env.bound x) (env.bound y) (env.bound z) := by
  simp only [operation,Operation,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),factor_semantics hM,join_semantics hM]
  rfl

def row {m : Nat} (D mul e deps x y Y : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound Y.succ)) (operation D.succ mul.succ e.succ
  deps.succ x.succ y.succ (0 : Fin (m+1)))))

theorem row_freeClosed {m : Nat} (D mul e deps x y Y : Fin m) :
    (row D mul e deps x y Y).FreeClosed := by
  simp -implicitDefEqProofs [row,Definitional.Formula.FreeClosed,operation_freeClosed]

theorem row_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e deps x y Y : Fin m) :
    Project.Formula.satisfies env (row D mul e deps x y Y) ↔ Row (env.bound D) (env.bound mul) (env.bound e) (env.bound deps) (env.bound x) (env.bound y) (env.bound Y) := by
  simp only [row,Row,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,operation_semantics hM]
  rfl

def Candidate (D mul e deps q Y : M.Carrier .set) : Prop :=
  ∃ x y, PureKuratowski.Code M q x y ∧ Row D mul e deps x y Y

def candidate {m : Nat} (D mul e deps q Y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound q.succ.succ) (.bound (1 : Fin
  (m+2))) (.bound (0 : Fin (m+2)))) (row D.succ.succ mul.succ.succ e.succ.succ deps.succ.succ (1 :
  Fin (m+2)) (0 : Fin (m+2)) Y.succ.succ))))

theorem candidate_freeClosed {m : Nat} (D mul e deps q Y : Fin m) :
    (candidate D mul e deps q Y).FreeClosed := by
  simp -implicitDefEqProofs [candidate,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,row_freeClosed]

theorem candidate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e deps q Y : Fin m) :
    Project.Formula.satisfies env (candidate D mul e deps q Y) ↔ Candidate (env.bound D) (env.bound mul) (env.bound e) (env.bound deps) (env.bound q) (env.bound Y) := by
  simp only [candidate,Candidate,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,KuratowskiZF.code_correct hM,Project.Term.eval_bound,row_semantics hM]
  rfl

theorem exists_operation_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e P deps B : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hB : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) B D D)
    (hP : (Project.FirstOrderSemantics.reduct M).IsPowerSetOf P D) (hdeps : MapsTo D P deps)
    (hCount : ∀ x Y, PureKuratowski.PairMember M x Y deps →
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Y w) :
    ∃ F, MapsTo B P F ∧ OperationGraph D mul e deps B F ∧
      ∀ q Y, PureKuratowski.PairMember M q Y F →
        (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Y w := by
  let schema : Project.BinarySchema 4 := {
    body := candidate 2 3 4 5 1 0
    freeClosed := candidate_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases D (Fin.cases mul (Fin.cases e (fun _ => deps))), free := fun _ => D }
  have he q Y : schema.denote env q Y ↔ Candidate D mul e deps q Y :=
    candidate_semantics hM ((env.push q).push Y) 2 3 4 5 1 0
  have hrow {q Y} (hq : (Project.FirstOrderSemantics.reduct M).mem q B)
      (h : Candidate D mul e deps q Y) :
      (Project.FirstOrderSemantics.reduct M).mem Y P ∧
        (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual (KuratowskiZF.interpretation hM) Y w := by
    obtain ⟨x,hx,y,hy,hqxy⟩ := (hB q).mp hq
    obtain ⟨x',y',hqxy',hY⟩ := h
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hqxy hqxy'
    obtain ⟨Z,hZ,hZP,hZc⟩ := row_exists hM hw hm hc hP hdeps hCount hx hy
    exact (row_unique hM hY hZ).symm ▸ ⟨hZP,hZc⟩
  obtain ⟨F,hF,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := B) (target := P) (by
      intro q hq
      obtain ⟨x,hx,y,hy,hqxy⟩ := (hB q).mp hq
      obtain ⟨Y,hY,_,_⟩ := row_exists hM hw hm hc hP hdeps hCount hx hy
      exact ⟨Y,(he q Y).mpr ⟨x,y,hqxy,hY⟩⟩) (by
      intro q _ Y Z hY hZ
      obtain ⟨x,y,hqxy,hY⟩ := (he q Y).mp hY
      obtain ⟨x',y',hqxy',hZ⟩ := (he q Z).mp hZ
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hqxy hqxy'
      exact row_unique hM hY hZ) (by
      intro q Y hq hY
      exact (hrow hq ((he q Y).mp hY)).1)
  have hGraph' : OperationGraph D mul e deps B F :=
    fun q Y => (hGraph q Y).trans (and_congr_right (fun _ => he q Y))
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM B P F).mpr hF,hGraph',fun q Y h =>
    (hrow ((hGraph' q Y).mp h).1 ((hGraph' q Y).mp h).2).2⟩

def Dependencies (w D deps : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn D deps ∧ ∀ x Y, PureKuratowski.PairMember M x Y deps →
    (Project.FirstOrderSemantics.reduct M).MemberSubset Y D ∧ ForcingSupportSize.Small Y w

def DependenciesClosed (deps S : M.Carrier .set) : Prop := ∀ x Y,
  (Project.FirstOrderSemantics.reduct M).mem x S → PureKuratowski.PairMember M x Y deps →
    (Project.FirstOrderSemantics.reduct M).MemberSubset Y S

def Trace (hM : FirstOrder.Theory.Models M nativeZF)
    (w D mul e deps A seed XX P F Q S : M.Carrier .set) : Prop :=
  (∀ x, (Project.FirstOrderSemantics.reduct M).mem x seed ↔
    (Project.FirstOrderSemantics.reduct M).mem x A ∨ x = e) ∧
  (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) XX D D ∧
  (Project.FirstOrderSemantics.reduct M).IsPowerSetOf P D ∧ MapsTo XX P F ∧
  OperationGraph D mul e deps XX F ∧
  ConstructionCountableHull.Stages (KuratowskiZF.interpretation hM) w P F seed Q ∧
  Cc_union_d (KuratowskiZF.interpretation hM) Q S

def Result (w D mul e deps A S B G inc : M.Carrier .set) : Prop :=
  ForcingSupportSize.Small S w ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset A S ∧
  ConstructionConservativeHull.Closure D mul e S ∧
  ConstructionProbeLetters.Representatives S S B ∧ MapsTo B S G ∧
  ConstructionConservativeHull.ProductGraph S mul G ∧ LeftCancelMonoid S G e ∧ Conical S G e ∧
  ForcingConditionGraphs.IdentityGraph S inc ∧ ConstructionProbePushout.Hom S D G mul e e inc ∧
  ConstructionProbeConservative.Conservative S D G mul inc ∧ ConditionalJoins S G ∧
  DependenciesClosed deps S

theorem exists_traced_hull (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D mul e deps A : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hJ : ConditionalJoins D mul)
    (hdeps : Dependencies w D deps) (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A D)
    (ha : ForcingSupportSize.Small A w) :
    ∃ seed XX P F Q S B G inc, Trace hM w D mul e deps A seed XX P F Q S ∧
      Result w D mul e deps A S B G inc := by
  let I := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨P,hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨XX,hXX⟩ := ZF.exists_cartesianProduct hZF I D D
  have hDepMap : MapsTo D P deps := ⟨hdeps.1,fun x Y h => (hP Y).mpr (hdeps.2 x Y h).1⟩
  have hDepCount : ∀ x Y, PureKuratowski.PairMember M x Y deps →
      (Project.FirstOrderSemantics.reduct M).CardinalLessOrEqual I Y w :=
    fun x Y h => (ForcingSupportSize.native_small hM Y w).mp (hdeps.2 x Y h).2
  obtain ⟨F,hF,hOp,hCount⟩ := exists_operation_graph hM hw hm hc hXX hP hDepMap hDepCount
  obtain ⟨seed,hSeed⟩ := KP.exists_insert (ZF.modelsKP hZF) A e
  have hSeedD : (Project.FirstOrderSemantics.reduct M).MemberSubset seed D := by
    intro x hx
    rcases (hSeed x).mp hx with hx | rfl
    · exact hA x hx
    · exact hm.1.1
  have hSeedCount := ZF.countable_insert_l I hZF hw ((ForcingSupportSize.native_small hM A w).mp ha) hSeed
  obtain ⟨Q,S,hStages,hUnion,hSeedS,hSD,hSc,hClosed⟩ := ConstructionCountableHull.exists_hull I
    (ConstructionDirectedCardinality.models_zfc hM hChoice) hw hXX hP
    ((ForcingSupportSize.native_mapsTo hM XX P F).mp hF) hCount hSeedD hSeedCount
  have heS := hSeedS e ((hSeed e).mpr (Or.inr rfl))
  have hApply : ∀ x y z, (Project.FirstOrderSemantics.reduct M).mem x S →
      (Project.FirstOrderSemantics.reduct M).mem y S → Operation D mul e deps x y z →
        (Project.FirstOrderSemantics.reduct M).mem z S := by
    intro x y z hx hy hz
    obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM x y
    have hqXX := (hXX q).mpr ⟨x,hSD x hx,y,hSD y hy,hq⟩
    obtain ⟨Y,hY,_⟩ := hF.1.2 q hqXX
    obtain ⟨_,x',y',hq',hRow⟩ := (hOp q Y).mp hY
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    exact hClosed x y Y hx hy ⟨q,hq,hY⟩ z ((hRow z).mpr hz)
  have hClosure : ConstructionConservativeHull.Closure D mul e S := by
    refine ⟨hSD,heS,?_,?_,?_⟩
    · exact fun x y z hx hy hp => hApply x y z hx hy (Or.inl hp)
    · exact fun x y z hx hy hz hp => hApply x y z hx hy (Or.inr (Or.inl (Or.inl ⟨hz,hp⟩)))
    · exact fun x y j hx hy hj hp => hApply x y j hx hy (Or.inr (Or.inr (Or.inl (Or.inl ⟨hj,hp⟩))))
  have hDepsClosed : DependenciesClosed deps S := by
    intro x Y hx hY z hz
    exact hApply x e z hx heS (Or.inr (Or.inr (Or.inr ⟨Y,hY,hz⟩)))
  obtain ⟨B,G,inc,hB,hGMap,hG,hMon,hConical,hId,hHom,hCons,hJoins⟩ :=
    ConstructionConservativeHull.exists_submonoid hM hm hc hJ hClosure
  exact ⟨seed,XX,P,F,Q,S,B,G,inc,⟨hSeed,hXX,hP,hF,hOp,hStages,hUnion⟩,
    (ForcingSupportSize.native_small hM S w).mpr hSc,
    (fun x hx => hSeedS x ((hSeed x).mpr (Or.inl hx))),hClosure,hB,hGMap,hG,hMon,hConical,
    hId,hHom,hCons,hJoins,hDepsClosed⟩

theorem exists_countable_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D mul e deps A : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hJ : ConditionalJoins D mul)
    (hdeps : Dependencies w D deps) (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A D)
    (ha : ForcingSupportSize.Small A w) : ∃ S B G inc, Result w D mul e deps A S B G inc := by
  obtain ⟨_,_,_,_,_,S,B,G,inc,_,hResult⟩ := exists_traced_hull hM hChoice hw hm hc hJ hdeps hA ha
  exact ⟨S,B,G,inc,hResult⟩

def operationGraph {m : Nat} (D mul e deps B F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ (1 : Fin
  (m+2)) (0 : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound B.succ.succ)) (candidate
  D.succ.succ mul.succ.succ e.succ.succ deps.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem operationGraph_freeClosed {m : Nat} (D mul e deps B F : Fin m) :
    (operationGraph D mul e deps B F).FreeClosed := by
  simp -implicitDefEqProofs [operationGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,candidate_freeClosed]

theorem operationGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e deps B F : Fin m) :
    Project.Formula.satisfies env (operationGraph D mul e deps B F) ↔ OperationGraph (env.bound D) (env.bound mul) (env.bound e) (env.bound deps) (env.bound B) (env.bound F) := by
  simp only [operationGraph,OperationGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,candidate_semantics hM,Candidate]
  rfl

def dependencies {m : Nat} (w D deps : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn deps D)) (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge deps.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (.conj (Project.Formula.subset (.bound (0 : Fin (m+2))) (.bound D.succ.succ))
  (ProjectSyntax.encode id (ForcingSupportSize.small (0 : Fin (m+2)) w.succ.succ)))))))

theorem dependencies_freeClosed {m : Nat} (w D deps : Fin m) :
    (dependencies w D deps).FreeClosed := by
  simp -implicitDefEqProofs [dependencies,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem dependencies_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D deps : Fin m) :
    Project.Formula.satisfies env (dependencies w D deps) ↔ Dependencies (env.bound w) (env.bound D) (env.bound deps) := by
  simp only [dependencies,Dependencies,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingSupportSize.small_semantics (M := M)]
  rfl

def dependenciesClosed {m : Nat} (deps S : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound S.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge deps.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (Project.Formula.subset (.bound (0 : Fin (m+2))) (.bound S.succ.succ))))))

theorem dependenciesClosed_freeClosed {m : Nat} (deps S : Fin m) :
    (dependenciesClosed deps S).FreeClosed := by
  simp -implicitDefEqProofs [dependenciesClosed,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem dependenciesClosed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (deps S : Fin m) :
    Project.Formula.satisfies env (dependenciesClosed deps S) ↔ DependenciesClosed (env.bound deps) (env.bound S) := by
  simp only [dependenciesClosed,DependenciesClosed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def result {m : Nat} (w D mul e deps A S B G inc : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingSupportSize.small S w)) (.conj (Project.Formula.subset
  (.bound A) (.bound S)) (.conj (ConstructionConservativeHull.closure D mul e S) (.conj
  (ConstructionProbeLetters.representatives S S B) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo G B S)) (.conj (ConstructionConservativeHull.productGraph S mul G)
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid S G e)) (.conj
  (ProjectSyntax.encode id (ForcingDiagramPoset.conical S G e)) (.conj (ProjectSyntax.encode id
  (ForcingConditionGraphs.identityGraph S inc)) (.conj (ConstructionProbePushoutSyntax.hom S D G mul
  e e inc) (.conj (ConstructionProbeConservativeSyntax.conservative S D G mul inc) (.conj
  (ConstructionProbeSharedIntersections.conditionalJoins S G) (dependenciesClosed deps
  S)))))))))))))

theorem result_freeClosed {m : Nat} (w D mul e deps A S B G inc : Fin m) :
    (result w D mul e deps A S B G inc).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,dependenciesClosed_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e deps A S B G inc : Fin m) :
    Project.Formula.satisfies env (result w D mul e deps A S B G inc) ↔ Result (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound deps) (env.bound A) (env.bound S) (env.bound B) (env.bound G) (env.bound inc) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionConservativeHull.closure_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,dependenciesClosed_semantics hM]
  rfl

def trace {m : Nat} (w D mul e deps A seed XX P F Q S : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound seed.succ)) (.disj (.mem (.bound (0
  : Fin (m+1))) (.bound A.succ)) (Project.Formula.extensionalEq (.bound (0 : Fin (m+1))) (.bound
  e.succ))))) (.conj (Project.Formula.isCartesianProduct PureKuratowskiProject.convention (.bound
  XX) (.bound D) (.bound D)) (.conj (Project.Formula.isPowerSet (.bound P) (.bound D)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo F XX P)) (.conj (operationGraph D mul e deps
  XX F) (.conj (ConstructionCountableHull.stages PureKuratowskiProject.convention (.bound w) (.bound
  P) (.bound F) (.bound seed) (.bound Q)) (cc_union_m PureKuratowskiProject.convention (.bound Q)
  (.bound S))))))))

theorem trace_freeClosed {m : Nat} (w D mul e deps A seed XX P F Q S : Fin m) :
    (trace w D mul e deps A seed XX P F Q S).FreeClosed := by
  simp -implicitDefEqProofs [trace,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isCartesianProduct_freeClosed,Project.Formula.isPowerSet_freeClosed,operationGraph_freeClosed,ConstructionCountableHull.stages_freeClosed,cc_union_m_freeClosed]

theorem trace_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul e deps A seed XX P F Q S : Fin m) :
    Project.Formula.satisfies env (trace w D mul e deps A seed XX P F Q S) ↔ Trace hM (env.bound w) (env.bound D) (env.bound mul) (env.bound e) (env.bound deps) (env.bound A) (env.bound seed) (env.bound XX) (env.bound P) (env.bound F) (env.bound Q) (env.bound S) := by
  simp only [trace,Trace,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_disj_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),Project.Formula.satisfies_isCartesianProduct_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_isPowerSet_iff,operationGraph_semantics hM,ConstructionCountableHull.stages_semantics (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),cc_union_sat_l (KuratowskiZF.interpretation hM)]
  rfl

def constructionSentence : Project.Sentence where
  formula :=
    (Project.Formula.forallClosure 6 (.imp (Project.Formula.isOmega (.bound (0 : Fin 6))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 6) (2 : Fin 6) (3 : Fin
    6))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 6) (2 : Fin 6) (3 :
    Fin 6))) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (1 : Fin 6) (2 : Fin 6))
    (.imp (dependencies (0 : Fin 6) (1 : Fin 6) (4 : Fin 6)) (.imp (Project.Formula.subset (.bound
    (5 : Fin 6)) (.bound (1 : Fin 6))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (5 :
    Fin 6) (0 : Fin 6))) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.conj (trace (0 : Fin 6).succ.succ.succ.succ.succ.succ.succ.succ.succ (1 :
    Fin 6).succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin 15) (7 : Fin 15) (6 : Fin 15) (5 : Fin
    15) (4 : Fin 15) (3 : Fin 15)) (result (0 : Fin 6).succ.succ.succ.succ.succ.succ.succ.succ.succ
    (1 : Fin 6).succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin
    6).succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin 15) (2 : Fin 15) (1 : Fin 15) (0 : Fin
    15))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      dependencies_freeClosed,trace_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.small_semantics (M := M),
    dependencies_semantics hM,trace_semantics hM,result_semantics hM]
  exact fun hw hm hc hJ hDeps hA ha => exists_traced_hull hM hChoice hw hm hc hJ hDeps hA ha

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionCountableConservativeHull
