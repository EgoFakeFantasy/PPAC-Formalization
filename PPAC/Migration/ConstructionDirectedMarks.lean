/- Pinned MonoidTowers.DirectedColimit.old_e/object.e/e_ne_one/inclusion.map_e.
Object.e is the distinguished NONUNIT, distinct from the monoid unit.
Use SAME actual limit/projection and source actual transition mark equations. -/
import PPAC.Migration.ConstructionDirectedHeightCost

namespace PPAC.Migration.ConstructionDirectedMarks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family)
open ConstructionDirectedConservativeData
open ConstructionDirectedLimitCarrier (Representatives EqualityLaw)
open ConstructionDirectedMonoid (UnitImage)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def MarkFamily (J Domains Units Marks : M.Carrier .set) : Prop :=
  FunctionOn J Marks ∧ ∀ i D e a, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i e Units →
    PureKuratowski.PairMember M i a Marks → (Project.FirstOrderSemantics.reduct M).mem a D ∧ a ≠ e

def Stable (J E Domains F Marks : M.Carrier .set) : Prop :=
  ∀ i j a b, PureKuratowski.PairMember M i j E → PureKuratowski.PairMember M i a Marks →
    Transition J Domains F i j a b → PureKuratowski.PairMember M j b Marks

def MarkImage (J Marks projection mark : M.Carrier .set) : Prop :=
  ∀ i a, (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i a Marks → Product projection i a mark

theorem exists_mark (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F Muls Units Marks C L projection unit : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw J E Domains F projection) (hUnit : UnitImage J Domains Units projection unit)
    (hMarks : MarkFamily J Domains Units Marks) (hStable : Stable J E Domains F Marks) :
    ∃ mark, (Project.FirstOrderSemantics.reduct M).mem mark L ∧ mark ≠ unit ∧ MarkImage J Marks projection mark := by
  obtain ⟨i,hi⟩ := hne
  obtain ⟨D,mul,e,hD,_,he,hMon⟩ := ConstructionDirectedMonoidData.family_at hFam hi
  obtain ⟨a,ha,_⟩ := hMarks.1.2 i hi
  obtain ⟨haD,hane⟩ := hMarks.2 i D e a hi hD he ha
  obtain ⟨mark,hmk,hpa⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp ⟨hi,D,hD,haD⟩
  have hI := injective_transitions hFam hT hCons
  have hU := hUnit i e ⟨⟨hi,D,hD,hMon.1.1⟩,he⟩
  refine ⟨mark,hmk,fun h => hane (ConstructionDirectedLimitCarrier.of_injective hC hp hE hT hI hEq (h ▸ hpa) hU),?_⟩
  intro j b hj hb
  obtain ⟨Dj,mj,ej,hDj,_,hej,_⟩ := ConstructionDirectedMonoidData.family_at hFam hj
  have hbD := (hMarks.2 j Dj ej b hj hDj hej hb).1
  obtain ⟨out,_,hpb⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp ⟨hj,Dj,hDj,hbD⟩
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hj
  obtain ⟨aa,haa⟩ := hT.1 i k a ⟨hi,D,hD,haD⟩ hk hik
  obtain ⟨bb,hbb⟩ := hT.1 j k b ⟨hj,Dj,hDj,hbD⟩ hk hjk
  have heq := ForcingConditionGraphs.function_unique hMarks.1
    (hStable i k a aa hik ha haa) (hStable j k b bb hjk hb hbb)
  have hmo := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hpa hpb).mpr
    ⟨⟨hi,D,hD,haD⟩,⟨hj,Dj,hDj,hbD⟩,k,aa,hk,hik,hjk,haa,heq.symm ▸ hbb⟩
  exact hmo.symm ▸ hpb


def markFamily {m : Nat} (J Domains Units Marks : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Marks J)) (.forallE (.forallE (.forallE
  (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound J.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge Domains.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Units.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin
  (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Marks.succ.succ.succ.succ (3 : Fin (m+4))
  (0 : Fin (m+4)))) (.conj (.mem (.bound (0 : Fin (m+4))) (.bound (2 : Fin (m+4)))) (.neg
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+4))) (.bound (1 : Fin (m+4)))))))))))))))

theorem markFamily_freeClosed {m : Nat} (J Domains Units Marks : Fin m) :
    (markFamily J Domains Units Marks).FreeClosed := by
  simp -implicitDefEqProofs [markFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem markFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Units Marks : Fin m) :
    Project.Formula.satisfies env (markFamily J Domains Units Marks) ↔ MarkFamily (env.bound J) (env.bound Domains) (env.bound Units) (env.bound Marks) := by
  simp only [markFamily,MarkFamily,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def stable {m : Nat} (J E Domains F Marks : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  E.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Marks.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin (m+4)))) (.imp
  (ConstructionDirectedSystem.transition J.succ.succ.succ.succ Domains.succ.succ.succ.succ
  F.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (1 : Fin (m+4)) (0 : Fin (m+4)))
  (ProjectSyntax.encode id (Source.SetLanguage.edge Marks.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin
  (m+4)))))))))))

theorem stable_freeClosed {m : Nat} (J E Domains F Marks : Fin m) :
    (stable J E Domains F Marks).FreeClosed := by
  simp -implicitDefEqProofs [stable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.transition_freeClosed]

theorem stable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Marks : Fin m) :
    Project.Formula.satisfies env (stable J E Domains F Marks) ↔ Stable (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Marks) := by
  simp only [stable,Stable,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedSystem.transition_semantics hM]
  rfl


def markImage {m : Nat} (J Marks projection mark : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge Marks.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (ProjectSyntax.encode id
  (ForcingDiagramOrder.product projection.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)) mark.succ.succ))))))

theorem markImage_freeClosed {m : Nat} (J Marks projection mark : Fin m) :
    (markImage J Marks projection mark).FreeClosed := by
  simp -implicitDefEqProofs [markImage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem markImage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Marks projection mark : Fin m) :
    Project.Formula.satisfies env (markImage J Marks projection mark) ↔ MarkImage (env.bound J) (env.bound Marks) (env.bound projection) (env.bound mark) := by
  simp only [markImage,MarkImage,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionDirectedMarks
