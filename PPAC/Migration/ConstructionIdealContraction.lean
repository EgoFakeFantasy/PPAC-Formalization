/- Pinned AvailableRecords.ConeIdeal.contract/mem_contract/eq_of_contract_eq/
contract_one/contract_contract:323-373. The contracted ideal is the literal
right quotient of the given bounded ideal, constructed by native Separation.
Reuse original left-multiplication divisibility and cone-join transport. -/
import PPAC.Migration.ConstructionIdealProbes
import PPAC.Migration.ConstructionProbeConditionalJoins

namespace PPAC.Migration.ConstructionIdealContraction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ConstructionIdealProbes (ConeIdeal)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeConditionalJoins (left_mul_dvd_iff translate_cone_intersection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact right quotient, quantified over every object; no independently chosen ideal. -/
def Contract (D mul n U V : M.Carrier .set) : Prop := ∀ x,
  (Project.FirstOrderSemantics.reduct M).mem x V ↔
    (Project.FirstOrderSemantics.reduct M).mem x D ∧
      ∃ nx, Product mul n x nx ∧ (Project.FirstOrderSemantics.reduct M).mem nx U

def contract {m : Nat} (D mul n U V : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound V.succ))
    (.conj (.mem (.bound 0) (.bound D.succ))
      (.existsE (.conj (ProjectSyntax.encode id
        (ForcingDiagramOrder.product mul.succ.succ n.succ.succ 1 0))
        (.mem (.bound 0) (.bound U.succ.succ))))))

theorem contract_freeClosed {m : Nat} (D mul n U V : Fin m) :
    (contract D mul n U V).FreeClosed := by
  simp -implicitDefEqProofs [contract,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem contract_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul n U V : Fin m) :
    Project.Formula.satisfies env (contract D mul n U V) ↔
      Contract (env.bound D) (env.bound mul) (env.bound n) (env.bound U) (env.bound V) := by
  simp only [contract,Contract,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),Project.Term.eval_bound]
  rfl

theorem exists_contract (hM : FirstOrder.Theory.Models M nativeZF)
    (D mul n U : M.Carrier .set) : ∃ V, Contract D mul n U V := by
  let schema : Project.UnarySchema 3 := {
    body := .existsE (.conj (ProjectSyntax.encode id
      (ForcingDiagramOrder.product (2 : Fin 5) 3 1 0)) (.mem (.bound 0) (.bound 4)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases mul (Fin.cases n (fun _ => U)), free := fun _ => D }
  obtain ⟨V,hV⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env D
  refine ⟨V,fun x => ?_⟩
  simpa only [schema,Project.UnarySchema.denote,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),Project.Term.eval_bound] using! hV x

theorem contract_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul n U V W : M.Carrier .set} (hV : Contract D mul n U V) (hW : Contract D mul n U W) :
    V = W :=
  (ModelTransfer.extensionality hM).eq_of_same_members V W (fun x => (hV x).trans (hW x).symm)

/-- All original ConeIdeal fields, with the given residual bound c. -/
theorem contract_ideal {D mul e a U n c V : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hU : ConeIdeal D mul a U)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n U)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c D) (hnc : Product mul n c a)
    (hV : Contract D mul n U V) : ConeIdeal D mul c V := by
  have hnD := hU.1 n hn
  refine ⟨fun x hx => ((hV x).mp hx).1,hc,?_,?_,?_,?_⟩
  · exact ⟨e,(hV e).mpr ⟨hm.1.1,n,(hm.1.2 n hnD n).2.mpr rfl,hn⟩⟩
  · intro x hx
    obtain ⟨hxD,nx,hnx,hnxU⟩ := (hV x).mp hx
    exact (left_mul_dvd_iff hm hnD hxD hc hnx hnc).mp (hU.2.2.2.1 nx hnxU)
  · intro x y hxD hy hxy
    obtain ⟨hyD,ny,hny,hnyU⟩ := (hV y).mp hy
    obtain ⟨nx,hnxD,hnx⟩ := (hm.2.1 n hnD).1 x hxD
    have hnxny := (left_mul_dvd_iff hm hnD hxD hyD hnx hny).mpr hxy
    exact (hV x).mpr ⟨hxD,nx,hnx,hU.2.2.2.2.1 nx ny hnxD hnyU hnxny⟩
  · intro x y j hx hy hjD hJoin
    obtain ⟨hxD,nx,hnx,hnxU⟩ := (hV x).mp hx
    obtain ⟨hyD,ny,hny,hnyU⟩ := (hV y).mp hy
    obtain ⟨nj,hnjD,hnj⟩ := (hm.2.1 n hnD).1 j hjD
    have hTranslated := translate_cone_intersection hm hnD hxD hyD hjD
      (hU.1 nx hnxU) (hU.1 ny hnyU) hnx hny hnj hJoin
    exact (hV j).mpr ⟨hjD,nj,hnj,hU.2.2.2.2.2 nx ny nj hnxU hnyU hnjD hTranslated⟩

theorem exists_contract_ideal (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e a U n c : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hU : ConeIdeal D mul a U) (hn : (Project.FirstOrderSemantics.reduct M).mem n U)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c D) (hnc : Product mul n c a) :
    ∃ V, Contract D mul n U V ∧ ConeIdeal D mul c V := by
  obtain ⟨V,hV⟩ := exists_contract hM D mul n U
  exact ⟨V,hV,contract_ideal hm hU hn hc hnc hV⟩

/-- The literal contracted set at the unit is the original set. -/
theorem contract_one (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e a U V : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hU : ConeIdeal D mul a U) (hV : Contract D mul e U V) : V = U := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨hxD,ex,hex,hexU⟩ := (hV x).mp hx
    exact (hm.1.2 x hxD ex).1.mp hex ▸ hexU
  · intro hx
    exact (hV x).mpr ⟨hU.1 x hx,x,(hm.1.2 x (hU.1 x hx) x).1.mpr rfl,hx⟩

/-- Two actual contractions are literally contraction by the specified product. -/
theorem contract_comp {D mul e U V W n m nm : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hnD : (Project.FirstOrderSemantics.reduct M).mem n D)
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m D) (hnm : Product mul n m nm)
    (hV : Contract D mul n U V) (hW : Contract D mul m V W) : Contract D mul nm U W := by
  intro x
  constructor
  · intro hx
    obtain ⟨hxD,mx,hmx,hmxV⟩ := (hW x).mp hx
    obtain ⟨_,nx,hnx,hnxU⟩ := (hV mx).mp hmxV
    exact ⟨hxD,nx,(hm.2.2 n m x nm mx nx hnD hmD hxD hnm hmx).mpr hnx,hnxU⟩
  · rintro ⟨hxD,nx,hnx,hnxU⟩
    obtain ⟨mx,hmxD,hmx⟩ := (hm.2.1 m hmD).1 x hxD
    have hnmxx := (hm.2.2 n m x nm mx nx hnD hmD hxD hnm hmx).mp hnx
    exact (hW x).mpr ⟨hxD,mx,hmx,(hV mx).mpr ⟨hmxD,nx,hnmxx,hnxU⟩⟩

/-- A common contraction index remembers the whole bounded ideal, using the
original conditional joins with each candidate element. -/
theorem eq_of_contract_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul e a n U V CU CV : M.Carrier .set} (hm : LeftCancelMonoid D mul e)
    (hJ : ConditionalJoins D mul) (hU : ConeIdeal D mul a U) (hV : ConeIdeal D mul a V)
    (hnU : (Project.FirstOrderSemantics.reduct M).mem n U)
    (hnV : (Project.FirstOrderSemantics.reduct M).mem n V)
    (hCU : Contract D mul n U CU) (hCV : Contract D mul n V CV) (hEq : CU = CV) : U = V := by
  have transfer {U V CU CV : M.Carrier .set} (hU : ConeIdeal D mul a U) (hV : ConeIdeal D mul a V)
      (hnU : (Project.FirstOrderSemantics.reduct M).mem n U)
      (hCU : Contract D mul n U CU) (hCV : Contract D mul n V CV)
      (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset CU CV) :
      (Project.FirstOrderSemantics.reduct M).MemberSubset U V := by
    intro z hzU
    have hzD := hU.1 z hzU
    have hnD := hU.1 n hnU
    obtain ⟨j,hjD,hJoin⟩ := hJ z n a hzD hnD hU.2.1
      (hU.2.2.2.1 z hzU) (hU.2.2.2.1 n hnU)
    have hjU := hU.2.2.2.2.2 z n j hzU hnU hjD hJoin
    have hjj : Divides D mul j j := ⟨e,hm.1.1,(hm.1.2 j hjD j).2.mpr rfl⟩
    obtain ⟨hzj,hnj⟩ := (hJoin j hjD).mpr hjj
    obtain ⟨x,hxD,hnx⟩ := hnj
    have hxCU := (hCU x).mpr ⟨hxD,j,hnx,hjU⟩
    obtain ⟨_,nx,hnx',hnxV⟩ := (hCV x).mp (hSub x hxCU)
    have he : nx = j := (hm.2.1 n hnD).2.1 x nx j hxD hnx' hnx
    exact hV.2.2.2.2.1 z j hzD (he ▸ hnxV) hzj
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro z
  exact ⟨fun hz => transfer hU hV hnU hCU hCV (fun x hx => hEq ▸ hx) z hz,
    fun hz => transfer hV hU hnV hCV hCU (fun x hx => hEq.symm ▸ hx) z hz⟩

end PPAC.Migration.ConstructionIdealContraction
