/- Pinned ProbePresentations.Word.simulated_old_intersection.
The two uses of Conservative.comp are expanded through existing common and
intersection fields. The same original base join is used in both extensions. -/
import PPAC.Migration.ConstructionProbeConservativeSyntax

namespace PPAC.Migration.ConstructionProbeSharedIntersections
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeConservative (Conservative)
open ConstructionProbeConservativeSyntax (conservative conservative_freeClosed conservative_semantics)
open ConstructionProbeCones (JoinProperty joinProperty joinProperty_freeClosed joinProperty_semantics)
open ConstructionBaseMonoid (Divides Joins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The cone-join formulation of the source HasConditionalJoins premise. -/
def ConditionalJoins (D mul : M.Carrier .set) : Prop := ∀ x y m,
  (Project.FirstOrderSemantics.reduct M).mem x D → (Project.FirstOrderSemantics.reduct M).mem y D →
  (Project.FirstOrderSemantics.reduct M).mem m D → Divides D mul x m → Divides D mul y m →
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j D ∧ JoinProperty D mul x y j

theorem conditionalJoins_of_joins {D mul : M.Carrier .set} (h : Joins D mul) : ConditionalJoins D mul :=
  fun x y _ hx hy _ _ _ => h x y hx hy

def SharedIntersections (D W WN G GN f H HN : M.Carrier .set) : Prop :=
  ∀ x y fx fy ox oy Ox Oy q,
    PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M y fy f →
    PureKuratowski.PairMember M x ox H → PureKuratowski.PairMember M y oy H →
    PureKuratowski.PairMember M fx Ox HN → PureKuratowski.PairMember M fy Oy HN →
    (Project.FirstOrderSemantics.reduct M).mem q WN → Divides WN GN Ox q → Divides WN GN Oy q →
      ∃ j fj oj Oj, (Project.FirstOrderSemantics.reduct M).mem j D ∧
        PureKuratowski.PairMember M j fj f ∧ PureKuratowski.PairMember M j oj H ∧
        PureKuratowski.PairMember M fj Oj HN ∧ JoinProperty W G ox oy oj ∧ JoinProperty WN GN Ox Oy Oj

theorem shared_intersections {D N W WN mul mulN G GN f H HN : M.Carrier .set}
    (hJ : ConditionalJoins D mul) (hf : Conservative D N mul mulN f)
    (hA : Conservative D W mul G H) (hC : Conservative N WN mulN GN HN) :
    SharedIntersections D W WN G GN f H HN := by
  intro x y fx fy ox oy Ox Oy q hfx hfy hox hoy hOx hOy hq hxq hyq
  have hx := ForcingConditionGraphs.function_input hf.1.1.1 hfx
  have hy := ForcingConditionGraphs.function_input hf.1.1.1 hfy
  obtain ⟨m,hm,hxm,hym⟩ := hf.2.2.2 x y fx fy hfx hfy
    (hC.2.2.2 fx fy Ox Oy hOx hOy ⟨q,hq,hxq,hyq⟩)
  obtain ⟨j,hj,hJoin⟩ := hJ x y m hx hy hm hxm hym
  obtain ⟨fj,hfj,_⟩ := hf.1.1.1.2 j hj
  obtain ⟨oj,hoj,_⟩ := hA.1.1.1.2 j hj
  obtain ⟨Oj,hOj,_⟩ := hC.1.1.1.2 fj (hf.1.1.2 j fj hfj)
  exact ⟨j,fj,oj,Oj,hj,hfj,hoj,hOj,hA.2.2.1 x y j ox oy oj hox hoy hoj hJoin,
    hC.2.2.1 fx fy fj Ox Oy Oj hOx hOy hOj (hf.2.2.1 x y j fx fy fj hfx hfy hfj hJoin)⟩

def conditionalJoins {m : Nat} (D mul : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound D.succ.succ.succ)) (.imp (.mem (.bound 1)
  (.bound D.succ.succ.succ)) (.imp (.mem (.bound 0) (.bound D.succ.succ.succ)) (.imp (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides D.succ.succ.succ mul.succ.succ.succ 2 0)) (.imp (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides D.succ.succ.succ mul.succ.succ.succ 1 0)) (.existsE (.conj (.mem (.bound 0)
  (.bound D.succ.succ.succ.succ)) (joinProperty D.succ.succ.succ.succ mul.succ.succ.succ.succ 3 2 0)))))))))))

def sharedIntersections {m : Nat} (D W WN G GN f H HN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 4)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 3)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge HN.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 2))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge HN.succ.succ.succ.succ.succ.succ.succ.succ.succ 5
  1)) (.imp (.mem (.bound 0) (.bound WN.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ.succ.succ.succ 2 0)) (.imp (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 0)) (.existsE (.existsE (.existsE (.existsE (.conj (.mem
  (.bound 3) (.bound D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 2)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 1)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 2 0)) (.conj (joinProperty
  W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 7 1) (joinProperty
  WN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 5 0))))))))))))))))))))))))))))

theorem conditionalJoins_freeClosed {m : Nat} (D mul : Fin m) : (conditionalJoins D mul).FreeClosed := by
  simp -implicitDefEqProofs [conditionalJoins,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,joinProperty_freeClosed]

theorem conditionalJoins_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul : Fin m) :
    Project.Formula.satisfies env (conditionalJoins D mul) ↔
      ConditionalJoins (env.bound D) (env.bound mul) := by
  simp only [conditionalJoins,ConditionalJoins,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),joinProperty_semantics hM]
  rfl

theorem sharedIntersections_freeClosed {m : Nat} (D W WN G GN f H HN : Fin m) : (sharedIntersections D W WN G GN f H HN).FreeClosed := by
  simp -implicitDefEqProofs [sharedIntersections,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,joinProperty_freeClosed]

theorem sharedIntersections_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D W WN G GN f H HN : Fin m) :
    Project.Formula.satisfies env (sharedIntersections D W WN G GN f H HN) ↔
      SharedIntersections (env.bound D) (env.bound W) (env.bound WN) (env.bound G) (env.bound GN) (env.bound f) (env.bound H) (env.bound HN) := by
  simp only [sharedIntersections,SharedIntersections,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),joinProperty_semantics hM,KuratowskiZF.source_edge]
  rfl

def sharedSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (conditionalJoins (0 : Fin 11) (4 : Fin 11)) (.imp (conservative (0 : Fin 11) (1 : Fin 11) (4 : Fin
    11) (5 : Fin 11) (8 : Fin 11)) (.imp (conservative (0 : Fin 11) (2 : Fin 11) (4 : Fin 11) (6 : Fin 11) (9
    : Fin 11)) (.imp (conservative (1 : Fin 11) (3 : Fin 11) (5 : Fin 11) (7 : Fin 11) (10 : Fin 11))
    (sharedIntersections (0 : Fin 11) (2 : Fin 11) (3 : Fin 11) (6 : Fin 11) (7 : Fin 11) (8 : Fin 11) (9 :
    Fin 11) (10 : Fin 11))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,conditionalJoins_freeClosed,
      conservative_freeClosed,sharedIntersections_freeClosed]

theorem shared_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence sharedSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) sharedSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,conditionalJoins_semantics hM,
    conservative_semantics hM,sharedIntersections_semantics hM]
  exact fun hJ hf hA hC => shared_intersections hJ hf hA hC

theorem shared_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence sharedSentence) := ModelTransfer.derives (fun _ hM => shared_models hM)

end PPAC.Migration.ConstructionProbeSharedIntersections
