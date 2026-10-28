/- Pinned ComponentGluing.Vertex / Component:15-19,175-177.
The actual ground set of ALL vertices over the given root is a separation of
Diagram(D,I) × (D × Power(D)). Reuse the existing full diagram carrier,
native powerset/cartesian products and separation. No countability or rank
bound is imposed. Consumers: component chains and the full glued component. -/
import PPAC.Migration.ConstructionComponentVertices
import PPAC.Migration.ForcingDiagramCarrier

namespace PPAC.Migration.ConstructionComponentCarrier
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionComponentVertices (Vertex)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The literal internal triple v=(r,(a,U)); proof fields have no data slots. -/
def Code (v r a U : M.Carrier .set) : Prop :=
  ∃ t, PureKuratowski.Code M t a U ∧ PureKuratowski.Code M v r t

def EncodedVertex (D I mul q v : M.Carrier .set) : Prop :=
  ∃ r a U, Code v r a U ∧ Vertex D I mul q r a U

def Carrier (D I mul q V : M.Carrier .set) : Prop := ∀ v,
  (Project.FirstOrderSemantics.reduct M).mem v V ↔ EncodedVertex D I mul q v

theorem code_total (hM : FirstOrder.Theory.Models M nativeZF) (r a U : M.Carrier .set) :
    ∃ v, Code v r a U := by
  obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM a U
  obtain ⟨v,hv⟩ := KuratowskiZF.exists_code hM r t
  exact ⟨v,t,ht,hv⟩

theorem code_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {v w r a U : M.Carrier .set} (hv : Code v r a U) (hw : Code w r a U) : v = w := by
  obtain ⟨t,ht,hv⟩ := hv
  obtain ⟨s,hs,hw⟩ := hw
  have he := KuratowskiZF.code_unique hM ht hs
  subst s
  exact KuratowskiZF.code_unique hM hv hw

theorem code_injective {v r a U s b W : M.Carrier .set}
    (hv : Code v r a U) (hw : Code v s b W) : r = s ∧ a = b ∧ U = W := by
  obtain ⟨t,ht,hv⟩ := hv
  obtain ⟨z,hz,hw⟩ := hw
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hv hw
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht hz
  exact ⟨rfl,rfl,rfl⟩

def code {m : Nat} (v r a U : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (PureKuratowskiProject.code (.bound 0) (.bound a.succ) (.bound U.succ))
    (PureKuratowskiProject.code (.bound v.succ) (.bound r.succ) (.bound 0)))

theorem code_freeClosed {m : Nat} (v r a U : Fin m) : (code v r a U).FreeClosed := by
  simp -implicitDefEqProofs [code,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem code_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (v r a U : Fin m) :
    Project.Formula.satisfies env (code v r a U) ↔ Code (env.bound v) (env.bound r) (env.bound a) (env.bound U) := by
  simp only [code,Code,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

def encodedVertex {m : Nat} (D I mul q v : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (code v.succ.succ.succ 2 1 0)
    (ConstructionComponentVertices.vertex D.succ.succ.succ I.succ.succ.succ
      mul.succ.succ.succ q.succ.succ.succ 2 1 0))))

theorem encodedVertex_freeClosed {m : Nat} (D I mul q v : Fin m) :
    (encodedVertex D I mul q v).FreeClosed := by
  simp -implicitDefEqProofs [encodedVertex,Definitional.Formula.FreeClosed,code_freeClosed,
    ConstructionComponentVertices.vertex_freeClosed]

theorem encodedVertex_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q v : Fin m) :
    Project.Formula.satisfies env (encodedVertex D I mul q v) ↔
      EncodedVertex (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound v) := by
  simp only [encodedVertex,EncodedVertex,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,code_semantics hM,ConstructionComponentVertices.vertex_semantics hM]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (D I mul q : M.Carrier .set) :
    ∃ V, Carrier D I mul q V := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let K := KuratowskiZF.interpretation hM
  obtain ⟨X,hX⟩ := ForcingDiagramCarrier.exists_carrier hM D I
  obtain ⟨P,hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨A,hA⟩ := ZF.exists_cartesianProduct hZF K D P
  obtain ⟨B,hB⟩ := ZF.exists_cartesianProduct hZF K X A
  let schema : Project.UnarySchema 4 := {
    body := encodedVertex 1 2 3 4 0
    freeClosed := encodedVertex_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (fun _ => q))), free := fun _ => D }
  have he v : schema.denote env v ↔ EncodedVertex D I mul q v :=
    encodedVertex_semantics hM (env.push v) 1 2 3 4 0
  have bound v (hv : EncodedVertex D I mul q v) : (Project.FirstOrderSemantics.reduct M).mem v B := by
    obtain ⟨r,a,U,⟨t,ht,hv⟩,hVertex⟩ := hv
    have htA : (Project.FirstOrderSemantics.reduct M).mem t A :=
      (hA t).mpr ⟨a,hVertex.2.2.2.1,U,(hP U).mpr hVertex.2.2.1,ht⟩
    exact (hB v).mpr ⟨r,(hX r).mpr hVertex.1,t,htA,hv⟩
  obtain ⟨V,hV⟩ := ZF.separation_exists_d hZF schema env B
  refine ⟨V,fun v => ?_⟩
  exact ⟨fun hv => (he v).mp ((hV v).mp hv).2,
    fun hv => (hV v).mpr ⟨bound v hv,(he v).mpr hv⟩⟩

theorem carrier_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q V W : M.Carrier .set} (hV : Carrier D I mul q V) (hW : Carrier D I mul q W) : V = W :=
  (ModelTransfer.extensionality hM).eq_of_same_members V W (fun v => (hV v).trans (hW v).symm)

theorem mem_of_vertex {D I mul q V v r a U : M.Carrier .set}
    (hV : Carrier D I mul q V) (hv : Code v r a U) (hVertex : Vertex D I mul q r a U) :
    (Project.FirstOrderSemantics.reduct M).mem v V := (hV v).mpr ⟨r,a,U,hv,hVertex⟩

def carrier {m : Nat} (D I mul q V : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound V.succ)) (encodedVertex D.succ I.succ mul.succ q.succ 0))

theorem carrier_freeClosed {m : Nat} (D I mul q V : Fin m) :
    (carrier D I mul q V).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,encodedVertex_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q V : Fin m) :
    Project.Formula.satisfies env (carrier D I mul q V) ↔
      Carrier (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound V) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,encodedVertex_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 4 (.existsE (carrier 1 2 3 4 0))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,carrier_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,carrier_semantics hM]
  exact exists_carrier hM (bound 0) (bound 1) (bound 2) (bound 3)

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionComponentCarrier
