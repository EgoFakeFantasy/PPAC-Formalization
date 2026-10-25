/- Exact pinned Kuratowski convention in every nativeZF model.
Reuses PureKuratowskiProject.code/convention and PureKuratowski.code_injective;
only their ZFC-specific existence/uniqueness/realization premises are adapted
using the existing KP constructions and the accepted ZF model bridge.
No selected pair function or extra object Choice premise is introduced. -/
import PPAC.Migration.DefinableMinimaChoice
import YesMetaZFC.Model.ZFC.Pure.PureKuratowskiProject

namespace PPAC.Migration.KuratowskiZF
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem code_correct (hM : FirstOrder.Theory.Models M nativeZF) {depth : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) depth)
    (output left right : Project.Term depth) :
    Project.Formula.satisfies env (PureKuratowskiProject.code output left right) ↔
      PureKuratowski.Code M (output.eval env) (left.eval env) (right.eval env) := by
  simp only [PureKuratowskiProject.code, Project.Formula.isSingleton, Project.Formula.isUnorderedPair,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    or_self, Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push]
  rfl

theorem exists_code (hM : FirstOrder.Theory.Models M nativeZF)
    (left right : M.Carrier .set) : ∃ output, PureKuratowski.Code M output left right := by
  have hKP := SetTheory.ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨single, hSingle⟩ := SetTheory.KP.exists_singleton hKP left
  obtain ⟨pair, hPair⟩ := SetTheory.KP.exists_pair hKP left right
  obtain ⟨output, hOutput⟩ := SetTheory.KP.exists_pair hKP single pair
  exact ⟨output, single, pair, hSingle, hPair, hOutput⟩

theorem code_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {first second left right : M.Carrier .set}
    (hFirst : PureKuratowski.Code M first left right)
    (hSecond : PureKuratowski.Code M second left right) : first = second := by
  obtain ⟨single, pair, hSingle, hPair, hFirst⟩ := hFirst
  obtain ⟨single', pair', hSingle', hPair', hSecond⟩ := hSecond
  have hS := SetTheory.Structure.IsSingletonOf.eq
    (ModelTransfer.extensionality hM) hSingle hSingle'
  have hP := (ModelTransfer.extensionality hM).eq_of_same_members pair pair'
    (fun member => (hPair member).trans (hPair' member).symm)
  subst single'
  subst pair'
  exact (ModelTransfer.extensionality hM).eq_of_same_members first second
    (fun member => (hFirst member).trans (hSecond member).symm)

def interpretation (hM : FirstOrder.Theory.Models M nativeZF) :
    PureKuratowskiProject.convention.Interpretation (Project.FirstOrderSemantics.reduct M) where
  Codes := PureKuratowski.Code M
  realizes := code_correct hM
  total := exists_code hM
  unique := code_unique hM
  injective := PureKuratowski.code_injective

theorem source_pair {n : Nat} (v : Fin n → M.Carrier .set) (p x y : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (PairSyntax.pair p x y) ↔
      PureKuratowski.Pair M (v p) (v x) (v y) := by
  simp only [PairSyntax.pair, Source.Formula.Realize,
    Fin.lastCases_last, Fin.lastCases_castSucc, PureKuratowski.Pair]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩)

theorem source_code {n : Nat} (v : Fin n → M.Carrier .set) (p x y : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (PairSyntax.ordered p x y) ↔
      PureKuratowski.Code M (v p) (v x) (v y) := by
  simp only [PairSyntax.ordered, Source.Formula.Realize, source_pair,
    Fin.lastCases_last, Fin.lastCases_castSucc,
    PureKuratowski.Code, PureKuratowski.Single, PureKuratowski.Pair, or_self]
  rfl

theorem source_edge {n : Nat} (v : Fin n → M.Carrier .set) (r x y : Fin n) :
    Source.Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (Source.SetLanguage.edge r x y) ↔
      PureKuratowski.PairMember M (v x) (v y) (v r) := by
  simp only [Source.SetLanguage.edge, DefinableMinimaChoice.realize_rename,
    Source.Formula.Realize, PairSyntax.ordered_original, source_code]
  change (∃ pair, (Project.FirstOrderSemantics.reduct M).mem pair (v r) ∧
    PureKuratowski.Code M pair (v x) (v y)) ↔ _
  exact exists_congr (fun _ => and_comm)

end PPAC.Migration.KuratowskiZF
