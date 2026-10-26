/- Pinned ProbeGates.Path.transitions_from_adjacent.
Reuse native IsOmega.induction on an explicit pure formula; no target cancellation. -/
import PPAC.Migration.ConstructionProbeIndexedGeneratorsSyntax

namespace PPAC.Migration.ConstructionProbePresentationTransitions
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePath
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionFractionOrder (NatLe)
open ConstructionBaseCostBound (natLeF natLeF_freeClosed natLeF_semantics)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Unit Associative)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Transport (factor f p mulN i j : M.Carrier .set) : Prop := ∀ d fd pi pj,
  Product factor i j d → PureKuratowski.PairMember M d fd f →
  PureKuratowski.PairMember M i pi p → PureKuratowski.PairMember M j pj p → Product mulN fd pj pi

def transport {m : Nat} (factor f p mulN i j : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
    factor.succ.succ.succ.succ i.succ.succ.succ.succ j.succ.succ.succ.succ 3)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    p.succ.succ.succ.succ i.succ.succ.succ.succ 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    p.succ.succ.succ.succ j.succ.succ.succ.succ 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    mulN.succ.succ.succ.succ 2 0 1))))))))))

theorem transport_freeClosed {m : Nat} (factor f p mulN i j : Fin m) :
    (transport factor f p mulN i j).FreeClosed := by
  simp -implicitDefEqProofs [transport,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem transport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (factor f p mulN i j : Fin m) :
    Project.Formula.satisfies env (transport factor f p mulN i j) ↔
      Transport (env.bound factor) (env.bound f) (env.bound p) (env.bound mulN) (env.bound i) (env.bound j) := by
  simp only [transport,Transport,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def Stage (w factor f p mulN j : M.Carrier .set) : Prop := ∀ i,
  (Project.FirstOrderSemantics.reduct M).mem i w → NatLe i j → Transport factor f p mulN i j

def stage {m : Nat} (w factor f p mulN j : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound w.succ)) (.imp (natLeF 0 j.succ)
    (transport factor.succ f.succ p.succ mulN.succ 0 j.succ)))

theorem stage_freeClosed {m : Nat} (w factor f p mulN j : Fin m) :
    (stage w factor f p mulN j).FreeClosed := by
  simp -implicitDefEqProofs [stage,Definitional.Formula.FreeClosed,natLeF_freeClosed,transport_freeClosed]

theorem stage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w factor f p mulN j : Fin m) :
    Project.Formula.satisfies env (stage w factor f p mulN j) ↔
      Stage (env.bound w) (env.bound factor) (env.bound f) (env.bound p) (env.bound mulN) (env.bound j) := by
  simp only [stage,Stage,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,natLeF_semantics hM,transport_semantics hM]
  rfl

def Adjacent (w factor f p mulN : M.Carrier .set) : Prop := ∀ i j,
  (Project.FirstOrderSemantics.reduct M).mem i w → (Project.FirstOrderSemantics.reduct M).mem j w →
  (Project.FirstOrderSemantics.reduct M).SuccessorOf j i → Transport factor f p mulN i j

theorem transport_self {w D mul e zero a node factor N eN mulN f p i : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hPath : Path w D mul e zero a node)
    (hFactor : FactorTable w D mul node factor) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hOne : PureKuratowski.PairMember M e eN f) (hUnit : Unit N mulN eN)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w) : Transport factor f p mulN i i := by
  intro d fd pi pj hd hfd hpi hpj
  have hd' := ((hFactor i i d).mp hd).2.2.2
  have hed := factor_unique hm hPath.1 hd' (factor_self hm hPath.1 hi)
  subst d
  have hef := ForcingConditionGraphs.function_unique hf.1 hfd hOne
  have hep := ForcingConditionGraphs.function_unique hp.1 hpi hpj
  subst fd
  subst pj
  exact ((hUnit.2 pi (hp.2 i pi hpi) pi).1).mpr rfl

/-- The source successor calculation uses factor_trans, map_mul and associativity only. -/
theorem transport_step
    {w D mul e zero a node factor N mulN f p i j k : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hPath : Path w D mul e zero a node)
    (hFactor : FactorTable w D mul node factor) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j w)
    (hk : (Project.FirstOrderSemantics.reduct M).mem k w) (hij : NatLe i j) (hjk : NatLe j k)
    (hijT : Transport factor f p mulN i j) (hjkT : Transport factor f p mulN j k) :
    Transport factor f p mulN i k := by
  intro d fd pi pk hd hfd hpi hpk
  obtain ⟨u,hu⟩ := hPath.2.2.2.1 i j hi hj hij
  obtain ⟨v,hv⟩ := hPath.2.2.2.1 j k hj hk hjk
  have huD := hu.choose_spec.choose_spec.2.2.1
  have hvD := hv.choose_spec.choose_spec.2.2.1
  obtain ⟨uv,_,huv⟩ := (hm.2.1 u huD).1 v hvD
  have hed := factor_unique hm hPath.1 (factor_trans hm hPath.1 hu hv huv) (((hFactor i k d).mp hd).2.2.2)
  subst uv
  obtain ⟨fu,hfu,_⟩ := hf.1.2 u huD
  obtain ⟨fv,hfv,_⟩ := hf.1.2 v hvD
  obtain ⟨pj,hpj,_⟩ := hp.1.2 j hj
  have hmul := hPres u v d fu fv fd huv hfu hfv hfd
  have hijP := hijT u fu pi pj ((hFactor i j u).mpr ⟨hi,hj,hij,hu⟩) hfu hpi hpj
  have hjkP := hjkT v fv pj pk ((hFactor j k v).mpr ⟨hj,hk,hjk,hv⟩) hfv hpj hpk
  exact (hAssoc fu fv pk fd pj pi (hf.2 u fu hfu) (hf.2 v fv hfv) (hp.2 k pk hpk) hmul hjkP).mpr hijP

/-- Pinned transitions_from_adjacent on every internal finite stage. -/
theorem transitions_from_adjacent (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero a node factor N eN mulN f p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : LeftCancelMonoid D mul e) (hPath : Path w D mul e zero a node)
    (hFactor : FactorTable w D mul node factor) (hf : MapsTo D N f) (hp : MapsTo w N p)
    (hOne : PureKuratowski.PairMember M e eN f) (hUnit : Unit N mulN eN)
    (hAssoc : Associative N mulN) (hPres : PreservesProducts mul mulN f)
    (hAdj : Adjacent w factor f p mulN) :
    ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → Stage w factor f p mulN j := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases w (Fin.cases factor (Fin.cases f (Fin.cases p (fun _ => mulN)))), free := fun _ => w }
  let schema : Project.UnarySchema 5 := {
    body := stage 1 2 3 4 5 0
    freeClosed := stage_freeClosed _ _ _ _ _ _ }
  have he (j : M.Carrier .set) : schema.denote env j ↔ Stage w factor f p mulN j :=
    stage_semantics hM (env.push j) 1 2 3 4 5 0
  have hZF := ModelTransfer.project_models_iff.mp hM
  apply hw.induction (Stage w factor f p mulN)
  · obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF schema env w
    exact ⟨B,fun j => (hB j).trans (and_congr_right (fun _ => he j))⟩
  · intro z hz i hi hiz
    rcases hiz with hiz | hiz
    · subst z
      exact transport_self hm hPath hFactor hf hp hOne hUnit hi
    · exact (hz i hiz).elim
  · intro j hj ih k hkj i hi hik
    have hk : (Project.FirstOrderSemantics.reduct M).mem k w := by
      obtain ⟨k',hk'j,hk'⟩ := hw.1.2 j hj
      exact (SetTheory.Structure.SuccessorOf.eq hZF.1 hkj hk'j).symm ▸ hk'
    rcases hik with hik | hik
    · subst i
      exact transport_self hm hPath hFactor hf hp hOne hUnit hk
    · have hij : NatLe i j := by
        rcases (hkj i).mp hik with hij | hij
        · exact Or.inr hij
        · exact Or.inl (hZF.1.eq_of_same_members i j hij)
      exact transport_step hm hPath hFactor hf hp hAssoc hPres hi hj hk hij
        (Or.inr hkj.predecessor_mem) (ih i hi hij) (hAdj j k hj hk hkj)

end PPAC.Migration.ConstructionProbePresentationTransitions
