/- Pinned ConservativeHulls.ConservativeHull.conservative:249.
The actual subset is closed under products, specified ambient right factors,
and ambient conditional joins. Restrict the existing multiplication graph and
construct the literal inclusion; prove all four original conservation fields. -/
import PPAC.Migration.ConstructionProbePushoutSyntax
import PPAC.Migration.ConstructionProbeGateCap
import PPAC.Migration.ConstructionProbeSharedIntersections

namespace PPAC.Migration.ConstructionConservativeHull
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (IdentityGraph)
open ConstructionRealCuts (Subset)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeConservative (Conservative)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def MulClosed (S mul : M.Carrier .set) : Prop := ∀ x y z,
  (Project.FirstOrderSemantics.reduct M).mem x S →
  (Project.FirstOrderSemantics.reduct M).mem y S → Product mul x y z →
  (Project.FirstOrderSemantics.reduct M).mem z S

def FactorClosed (S D mul : M.Carrier .set) : Prop := ∀ x y z,
  (Project.FirstOrderSemantics.reduct M).mem x S →
  (Project.FirstOrderSemantics.reduct M).mem y S →
  (Project.FirstOrderSemantics.reduct M).mem z D → Product mul x z y →
  (Project.FirstOrderSemantics.reduct M).mem z S

def JoinClosed (S D mul : M.Carrier .set) : Prop := ∀ x y j,
  (Project.FirstOrderSemantics.reduct M).mem x S →
  (Project.FirstOrderSemantics.reduct M).mem y S →
  (Project.FirstOrderSemantics.reduct M).mem j D → JoinProperty D mul x y j →
  (Project.FirstOrderSemantics.reduct M).mem j S

def Closure (D mul e S : M.Carrier .set) : Prop :=
  Subset S D ∧ (Project.FirstOrderSemantics.reduct M).mem e S ∧
  MulClosed S mul ∧ FactorClosed S D mul ∧ JoinClosed S D mul

def ProductGraph (S mul G : M.Carrier .set) : Prop := ∀ x y z,
  Product G x y z ↔ (Project.FirstOrderSemantics.reduct M).mem x S ∧
    (Project.FirstOrderSemantics.reduct M).mem y S ∧ Product mul x y z

theorem exists_product (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e S : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hClosed : Closure D mul e S) :
    ∃ B G, ConstructionProbeLetters.Representatives S S B ∧ MapsTo B S G ∧
      ProductGraph S mul G := by
  obtain ⟨B,hB⟩ := ConstructionProbeLetters.exists_representatives hM S S
  obtain ⟨G,hR⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) mul B
  have hGraph : ProductGraph S mul G := by
    intro x y z
    constructor
    · rintro ⟨p,hcode,hpz⟩
      obtain ⟨hpB,hpm⟩ := (hR.2 p z).mp hpz
      obtain ⟨x',y',hx,hy,hcode'⟩ := (hB p).mp hpB
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact ⟨hx,hy,p,hcode,hpm⟩
    · rintro ⟨hx,hy,p,hcode,hpz⟩
      exact ⟨p,hcode,(hR.2 p z).mpr ⟨(hB p).mpr ⟨x,y,hx,hy,hcode⟩,hpz⟩⟩
  refine ⟨B,G,hB,⟨⟨?_,?_⟩,?_⟩,hGraph⟩
  · intro row hrow
    obtain ⟨p,z,hcode⟩ := hR.1 row hrow
    exact ⟨p,z,((hR.2 p z).mp ⟨row,hcode,hrow⟩).1,hcode⟩
  · intro p hp
    obtain ⟨x,y,hx,hy,hcode⟩ := (hB p).mp hp
    obtain ⟨z,_,hpz⟩ := (hm.2.1 x (hClosed.1 x hx)).1 y (hClosed.1 y hy)
    have hgz := (hGraph x y z).mpr ⟨hx,hy,hpz⟩
    obtain ⟨p',hcode',hp'z⟩ := hgz
    have he : p' = p := KuratowskiZF.code_unique hM hcode' hcode
    subst p'
    refine ⟨z,hp'z,fun t hpt => ?_⟩
    exact (hm.2.1 x (hClosed.1 x hx)).2.1 y t z (hClosed.1 y hy)
      ((hGraph x y t).mp ⟨p,hcode,hpt⟩).2.2 hpz
  · intro p z hpz
    obtain ⟨hp,_⟩ := (hR.2 p z).mp hpz
    obtain ⟨x,y,hx,hy,hcode⟩ := (hB p).mp hp
    exact hClosed.2.2.1 x y z hx hy ((hGraph x y z).mp ⟨p,hcode,hpz⟩).2.2

theorem monoid {D mul e S G : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hClosed : Closure D mul e S) (hG : ProductGraph S mul G) : LeftCancelMonoid S G e := by
  refine ⟨⟨hClosed.2.1,?_⟩,?_,?_⟩
  · intro x hx y
    constructor
    · exact ⟨fun h => (hm.1.2 x (hClosed.1 x hx) y).1.mp ((hG e x y).mp h).2.2,
        fun h => (hG e x y).mpr ⟨hClosed.2.1,hx,(hm.1.2 x (hClosed.1 x hx) y).1.mpr h⟩⟩
    · exact ⟨fun h => (hm.1.2 x (hClosed.1 x hx) y).2.mp ((hG x e y).mp h).2.2,
        fun h => (hG x e y).mpr ⟨hx,hClosed.2.1,(hm.1.2 x (hClosed.1 x hx) y).2.mpr h⟩⟩
  · intro x hx
    refine ⟨?_,?_,?_⟩
    · intro y hy
      obtain ⟨z,_,hz⟩ := (hm.2.1 x (hClosed.1 x hx)).1 y (hClosed.1 y hy)
      exact ⟨z,hClosed.2.2.1 x y z hx hy hz,(hG x y z).mpr ⟨hx,hy,hz⟩⟩
    · intro y z t hy hz ht
      exact (hm.2.1 x (hClosed.1 x hx)).2.1 y z t (hClosed.1 y hy)
        ((hG x y z).mp hz).2.2 ((hG x y t).mp ht).2.2
    · intro y z t hy hz hyt hzt
      exact (hm.2.1 x (hClosed.1 x hx)).2.2 y z t (hClosed.1 y hy) (hClosed.1 z hz)
        ((hG x y t).mp hyt).2.2 ((hG x z t).mp hzt).2.2
  · intro a b c ab bc z ha hb hc hab hbc
    have hab' := ((hG a b ab).mp hab).2.2
    have hbc' := ((hG b c bc).mp hbc).2.2
    have ha' := hClosed.1 a ha
    have hb' := hClosed.1 b hb
    have hc' := hClosed.1 c hc
    have habS := hClosed.2.2.1 a b ab ha hb hab'
    have hbcS := hClosed.2.2.1 b c bc hb hc hbc'
    exact ⟨fun h => (hG a bc z).mpr ⟨ha,hbcS,
      (hm.2.2 a b c ab bc z ha' hb' hc' hab' hbc').mp ((hG ab c z).mp h).2.2⟩,
      fun h => (hG ab c z).mpr ⟨habS,hc,
      (hm.2.2 a b c ab bc z ha' hb' hc' hab' hbc').mpr ((hG a bc z).mp h).2.2⟩⟩

theorem conical {D mul e S G : M.Carrier .set} (hc : Conical D mul e)
    (hSub : Subset S D) (hG : ProductGraph S mul G) : Conical S G e := by
  intro x y hx hy hp
  exact hc x y (hSub x hx) (hSub y hy) ((hG x y e).mp hp).2.2

theorem divides_iff {D mul e S G x y : M.Carrier .set}
    (hClosed : Closure D mul e S) (hG : ProductGraph S mul G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x S)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y S) :
    Divides D mul x y ↔ Divides S G x y := by
  constructor
  · rintro ⟨z,hz,hp⟩
    have hzS := hClosed.2.2.2.1 x y z hx hy hz hp
    exact ⟨z,hzS,(hG x z y).mpr ⟨hx,hzS,hp⟩⟩
  · rintro ⟨z,hz,hp⟩
    exact ⟨z,hClosed.1 z hz,((hG x z y).mp hp).2.2⟩

theorem join_reflect {D mul e S G x y j : M.Carrier .set}
    (hClosed : Closure D mul e S) (hG : ProductGraph S mul G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x S)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y S)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j S)
    (hJoin : JoinProperty D mul x y j) : JoinProperty S G x y j := by
  intro z hz
  exact (and_congr (divides_iff hClosed hG hx hz).symm (divides_iff hClosed hG hy hz).symm).trans
    ((hJoin z (hClosed.1 z hz)).trans (divides_iff hClosed hG hj hz))

theorem join_preserve {D mul e S G x y j : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e) (hJ : ConditionalJoins D mul)
    (hClosed : Closure D mul e S) (hG : ProductGraph S mul G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x S)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y S)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j S)
    (hJoin : JoinProperty S G x y j) : JoinProperty D mul x y j := by
  have hmS := monoid hm hClosed hG
  have hjj : Divides S G j j := ⟨e,hClosed.2.1,(hmS.1.2 j hj j).2.mpr rfl⟩
  have hxyj := (hJoin j hj).mpr hjj
  have hxj := (divides_iff hClosed hG hx hj).mpr hxyj.1
  have hyj := (divides_iff hClosed hG hy hj).mpr hxyj.2
  obtain ⟨l,hlD,hlJoin⟩ := hJ x y j (hClosed.1 x hx) (hClosed.1 y hy) (hClosed.1 j hj) hxj hyj
  have hlS := hClosed.2.2.2.2 x y l hx hy hlD hlJoin
  have hll : Divides D mul l l := ⟨e,hm.1.1,(hm.1.2 l hlD l).2.mpr rfl⟩
  have hxyl := (hlJoin l hlD).mpr hll
  have hlj := (hlJoin j (hClosed.1 j hj)).mp ⟨hxj,hyj⟩
  have hjl := (divides_iff hClosed hG hj hlS).mpr ((hJoin l hlS).mp
    ⟨(divides_iff hClosed hG hx hlS).mp hxyl.1,(divides_iff hClosed hG hy hlS).mp hxyl.2⟩)
  have he := ConstructionProbeGateCap.divides_antisymm hm hc hlD hlj hjl
  exact he ▸ hlJoin

theorem common {D mul e S G x y : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hClosed : Closure D mul e S) (hG : ProductGraph S mul G)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x S)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y S)
    (hCommon : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z D ∧
      Divides D mul x z ∧ Divides D mul y z) :
    ∃ z, (Project.FirstOrderSemantics.reduct M).mem z S ∧ Divides S G x z ∧ Divides S G y z := by
  obtain ⟨m,hmD,hxm,hym⟩ := hCommon
  obtain ⟨j,hjD,hJoin⟩ := hJ x y m (hClosed.1 x hx) (hClosed.1 y hy) hmD hxm hym
  have hjS := hClosed.2.2.2.2 x y j hx hy hjD hJoin
  have hjj : Divides D mul j j := ⟨e,hm.1.1,(hm.1.2 j hjD j).2.mpr rfl⟩
  have hxy := (hJoin j hjD).mpr hjj
  exact ⟨j,hjS,(divides_iff hClosed hG hx hjS).mp hxy.1,(divides_iff hClosed hG hy hjS).mp hxy.2⟩

theorem conditional_joins {D mul e S G : M.Carrier .set}
    (hJ : ConditionalJoins D mul) (hClosed : Closure D mul e S)
    (hG : ProductGraph S mul G) : ConditionalJoins S G := by
  intro x y z hx hy hz hxz hyz
  obtain ⟨j,hjD,hJoin⟩ := hJ x y z (hClosed.1 x hx) (hClosed.1 y hy) (hClosed.1 z hz)
    ((divides_iff hClosed hG hx hz).mpr hxz) ((divides_iff hClosed hG hy hz).mpr hyz)
  have hjS := hClosed.2.2.2.2 x y j hx hy hjD hJoin
  exact ⟨j,hjS,join_reflect hClosed hG hx hy hjS hJoin⟩

theorem exists_submonoid (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e S : M.Carrier .set} (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hJ : ConditionalJoins D mul) (hClosed : Closure D mul e S) :
    ∃ B G inc, ConstructionProbeLetters.Representatives S S B ∧ MapsTo B S G ∧
      ProductGraph S mul G ∧ LeftCancelMonoid S G e ∧ Conical S G e ∧ IdentityGraph S inc ∧
      ConstructionProbePushout.Hom S D G mul e e inc ∧ Conservative S D G mul inc ∧
      ConditionalJoins S G := by
  obtain ⟨B,G,hB,hMap,hG⟩ := exists_product hM hm hClosed
  obtain ⟨inc,hPerm,hId⟩ := ForcingConditionGraphs.exists_identity hM S
  have hInj : Injection S D inc := ⟨⟨hPerm.1.1,fun x y hxy =>
    hClosed.1 y (hPerm.1.2 x y hxy)⟩,hPerm.2.1⟩
  have hHom : ConstructionProbePushout.Hom S D G mul e e inc := by
    refine ⟨hInj.1,(hId e e).mpr ⟨hClosed.2.1,rfl⟩,?_⟩
    intro x y z fx fy fz hp hx hy hz
    obtain ⟨_,rfl⟩ := (hId x fx).mp hx
    obtain ⟨_,rfl⟩ := (hId y fy).mp hy
    obtain ⟨_,rfl⟩ := (hId z fz).mp hz
    exact ((hG x y z).mp hp).2.2
  have hCons : Conservative S D G mul inc := by
    refine ⟨hInj,?_,?_,?_⟩
    · intro x y z fx fy hx hy hz hp
      obtain ⟨hxS,rfl⟩ := (hId x fx).mp hx
      obtain ⟨hyS,rfl⟩ := (hId y fy).mp hy
      exact ⟨z,(hId z z).mpr ⟨hClosed.2.2.2.1 x y z hxS hyS hz hp,rfl⟩⟩
    · intro x y j fx fy fj hx hy hj hJoin
      obtain ⟨hxS,rfl⟩ := (hId x fx).mp hx
      obtain ⟨hyS,rfl⟩ := (hId y fy).mp hy
      obtain ⟨hjS,rfl⟩ := (hId j fj).mp hj
      exact join_preserve hm hc hJ hClosed hG hxS hyS hjS hJoin
    · intro x y fx fy hx hy hCommon
      obtain ⟨hxS,rfl⟩ := (hId x fx).mp hx
      obtain ⟨hyS,rfl⟩ := (hId y fy).mp hy
      exact common hm hJ hClosed hG hxS hyS hCommon
  exact ⟨B,G,inc,hB,hMap,hG,monoid hm hClosed hG,conical hc hClosed.1 hG,hId,hHom,hCons,
    conditional_joins hJ hClosed hG⟩


def mulClosed {m : Nat} (S mul : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound S.succ.succ.succ))
    (.imp (.mem (.bound 1) (.bound S.succ.succ.succ))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ 2 1 0))
        (.mem (.bound 0) (.bound S.succ.succ.succ)))))))

theorem mulClosed_freeClosed {m : Nat} (S mul : Fin m) : (mulClosed S mul).FreeClosed := by
  simp -implicitDefEqProofs [mulClosed,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem mulClosed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S mul : Fin m) :
    Project.Formula.satisfies env (mulClosed S mul) ↔ MulClosed (env.bound S) (env.bound mul) := by
  simp only [mulClosed,MulClosed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def factorClosed {m : Nat} (S D mul : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound S.succ.succ.succ))
    (.imp (.mem (.bound 1) (.bound S.succ.succ.succ))
      (.imp (.mem (.bound 0) (.bound D.succ.succ.succ))
        (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ 2 0 1))
          (.mem (.bound 0) (.bound S.succ.succ.succ))))))))

theorem factorClosed_freeClosed {m : Nat} (S D mul : Fin m) : (factorClosed S D mul).FreeClosed := by
  simp -implicitDefEqProofs [factorClosed,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem factorClosed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S D mul : Fin m) :
    Project.Formula.satisfies env (factorClosed S D mul) ↔ FactorClosed (env.bound S) (env.bound D) (env.bound mul) := by
  simp only [factorClosed,FactorClosed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def joinClosed {m : Nat} (S D mul : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound S.succ.succ.succ))
    (.imp (.mem (.bound 1) (.bound S.succ.succ.succ))
      (.imp (.mem (.bound 0) (.bound D.succ.succ.succ))
        (.imp (ConstructionProbeCones.joinProperty D.succ.succ.succ mul.succ.succ.succ 2 1 0)
          (.mem (.bound 0) (.bound S.succ.succ.succ))))))))

theorem joinClosed_freeClosed {m : Nat} (S D mul : Fin m) : (joinClosed S D mul).FreeClosed := by
  simp -implicitDefEqProofs [joinClosed,Definitional.Formula.FreeClosed,
    ConstructionProbeCones.joinProperty_freeClosed]

theorem joinClosed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S D mul : Fin m) :
    Project.Formula.satisfies env (joinClosed S D mul) ↔ JoinClosed (env.bound S) (env.bound D) (env.bound mul) := by
  simp only [joinClosed,JoinClosed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionProbeCones.joinProperty_semantics hM]
  rfl

def closure {m : Nat} (D mul e S : Fin m) : Project.Formula 1 m :=
  .conj (Project.Formula.subset (.bound S) (.bound D))
    (.conj (.mem (.bound e) (.bound S))
      (.conj (mulClosed S mul) (.conj (factorClosed S D mul) (joinClosed S D mul))))

theorem closure_freeClosed {m : Nat} (D mul e S : Fin m) : (closure D mul e S).FreeClosed := by
  simp -implicitDefEqProofs [closure,Definitional.Formula.FreeClosed,
    mulClosed_freeClosed,factorClosed_freeClosed,joinClosed_freeClosed]

theorem closure_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e S : Fin m) :
    Project.Formula.satisfies env (closure D mul e S) ↔
      Closure (env.bound D) (env.bound mul) (env.bound e) (env.bound S) := by
  simp only [closure,Closure,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    mulClosed_semantics hM,factorClosed_semantics hM,joinClosed_semantics hM]

def productGraph {m : Nat} (S mul G : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.iff
    (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ 2 1 0))
    (.conj (.mem (.bound 2) (.bound S.succ.succ.succ))
      (.conj (.mem (.bound 1) (.bound S.succ.succ.succ))
        (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ 2 1 0)))))))

theorem productGraph_freeClosed {m : Nat} (S mul G : Fin m) : (productGraph S mul G).FreeClosed := by
  simp -implicitDefEqProofs [productGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem productGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S mul G : Fin m) :
    Project.Formula.satisfies env (productGraph S mul G) ↔ ProductGraph (env.bound S) (env.bound mul) (env.bound G) := by
  simp only [productGraph,ProductGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramOrder.product_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionConservativeHull
