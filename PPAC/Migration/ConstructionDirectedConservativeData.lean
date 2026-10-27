/- Pinned DirectLimits.ConservativeLimit hf: every ORIGINAL transition is
Conservative. Reuse the existing four-field object contract, derive transition
injectivity and actual graph-value correspondence; never assume limit fields. -/
import PPAC.Migration.ConstructionDirectedMonoid
import PPAC.Migration.ConstructionProbeConservativeSyntax
import PPAC.Migration.ConstructionProbeSharedIntersections

namespace PPAC.Migration.ConstructionDirectedConservativeData
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family)
open ConstructionProbeConservative (Conservative)
open ForcingSupportSize (Injection)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ConservativeTransitions (J E Domains F Muls : M.Carrier .set) : Prop :=
  ∀ i j D1 D2 m1 m2 f, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → PureKuratowski.PairMember M i j E →
    PureKuratowski.PairMember M i D1 Domains → PureKuratowski.PairMember M j D2 Domains →
    PureKuratowski.PairMember M i m1 Muls → PureKuratowski.PairMember M j m2 Muls →
    Product F i j f → Conservative D1 D2 m1 m2 f

/-- Evaluate the SAME actual conservative transition graph, not a selected
alternative graph; totality/range come directly from its existing injection. -/
theorem transition_value {J Domains F i j D1 D2 f x : M.Carrier .set}
    (hf : Injection D1 D2 f) (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hD1 : PureKuratowski.PairMember M i D1 Domains) (hD2 : PureKuratowski.PairMember M j D2 Domains)
    (hF : Product F i j f) (hx : (Project.FirstOrderSemantics.reduct M).mem x D1) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y D2 ∧ PureKuratowski.PairMember M x y f ∧
      Transition J Domains F i j x y := by
  obtain ⟨y,hxy,_⟩ := hf.1.1.2 x hx
  have hy := hf.1.2 x y hxy
  exact ⟨y,hy,hxy,⟨hi,D1,hD1,hx⟩,⟨hj,D2,hD2,hy⟩,f,hF,hxy⟩

theorem transition_edge {J E Domains F i j D1 D2 f x y : M.Carrier .set}
    (hT : TransitionLaws J E Domains F) (hf : Injection D1 D2 f)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J) (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hD1 : PureKuratowski.PairMember M i D1 Domains) (hD2 : PureKuratowski.PairMember M j D2 Domains)
    (hF : Product F i j f) (hij : PureKuratowski.PairMember M i j E)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D1) (hxy : Transition J Domains F i j x y) :
    PureKuratowski.PairMember M x y f := by
  obtain ⟨y',_,hfy,hxy'⟩ := transition_value hf hi hj hD1 hD2 hF hx
  exact (hT.2.1 i j x y' y hij hxy' hxy) ▸ hfy

/-- The source hf already entails the injective transitions used by of_injective.
No new injectivity premise is added to the conservative-limit theorem. -/
theorem injective_transitions {J E Domains F Muls Units : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls) : InjectiveTransitions J E Domains F := by
  intro i j x y z hij hxz hyz
  obtain ⟨D1,m1,e1,hD1,hm1,_,_⟩ := ConstructionDirectedMonoidData.family_at hFam hxz.1.1
  obtain ⟨D2,m2,e2,hD2,hm2,_,_⟩ := ConstructionDirectedMonoidData.family_at hFam hxz.2.1.1
  obtain ⟨f,hF,hfx⟩ := hxz.2.2
  have hf := hCons i j D1 D2 m1 m2 f hxz.1.1 hxz.2.1.1 hij hD1 hD2 hm1 hm2 hF
  have hyD := ConstructionDirectedMonoidData.domain_mem hFam hD1 hyz.1
  have hfy := transition_edge hT hf.1 hxz.1.1 hxz.2.1.1 hD1 hD2 hF hij hyD hyz
  exact hf.1.2 x y z hfx hfy

def conservativeTransitions {m : Nat} (J E Domains F Muls : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (6 : Fin (m+7))) (.bound J.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (5 : Fin (m+7))) (.bound J.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (5 : Fin (m+7)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (4 : Fin (m+7)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+7)) (3 : Fin (m+7)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (2 : Fin (m+7)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+7)) (1 : Fin (m+7)))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product F.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (5 : Fin (m+7)) (0 : Fin (m+7)))) (ConstructionProbeConservativeSyntax.conservative (4 : Fin (m+7)) (3 : Fin (m+7)) (2 : Fin (m+7)) (1 : Fin (m+7)) (0 : Fin (m+7))))))))))))))))))

theorem conservativeTransitions_freeClosed {m : Nat} (J E Domains F Muls : Fin m) :
    (conservativeTransitions J E Domains F Muls).FreeClosed := by
  simp -implicitDefEqProofs [conservativeTransitions,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeConservativeSyntax.conservative_freeClosed]

theorem conservativeTransitions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls : Fin m) :
    Project.Formula.satisfies env (conservativeTransitions J E Domains F Muls) ↔
      ConservativeTransitions (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) := by
  simp only [conservativeTransitions,ConservativeTransitions,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeConservativeSyntax.conservative_semantics hM]
  rfl

/-- Original all-stage conditional-join assumption, independent of Conical. -/
def JoinsFamily (J Domains Muls Units : M.Carrier .set) : Prop :=
  ∀ i D mul e, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
    PureKuratowski.PairMember M i e Units → ConstructionProbeSharedIntersections.ConditionalJoins D mul

def joinsFamily {m : Nat} (J Domains Muls Units : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound J.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Units.succ.succ.succ.succ (3 : Fin (m+4)) (0 : Fin (m+4)))) (ConstructionProbeSharedIntersections.conditionalJoins (2 : Fin (m+4)) (1 : Fin (m+4)))))))))))

theorem joinsFamily_freeClosed {m : Nat} (J Domains Muls Units : Fin m) :
    (joinsFamily J Domains Muls Units).FreeClosed := by
  simp -implicitDefEqProofs [joinsFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeSharedIntersections.conditionalJoins_freeClosed]

theorem joinsFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls Units : Fin m) :
    Project.Formula.satisfies env (joinsFamily J Domains Muls Units) ↔
      JoinsFamily (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) := by
  simp only [joinsFamily,JoinsFamily,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedConservativeData
