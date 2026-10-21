import PPAC.Migration.ProjectNormalization
import PPAC.Migration.ZFEquivalence

/-! 任意参数、任意矩阵的源分离模式映射到原ZF分离模式；不截断公式复杂度。 -/
namespace PPAC.Migration.SeparationSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

/-- 源矩阵穿过A、B、x三个新槽；新元素仍是末变量。 -/
def matrixIndex {n} : Fin (n+1) → Fin (n+3) :=
  Fin.lastCases (Fin.last (n+2)) (fun i => i.castSucc.castSucc.castSucc)

def core {n} (p : Source.Formula (n+1)) : Source.Formula n :=
  .all (.ex (.all ((Source.Formula.mem (Fin.last (n+2)) (Fin.last (n+1)).castSucc).iff
    ((Source.Formula.mem (Fin.last (n+2)) (Fin.last n).castSucc.castSucc).conj
      (p.rename matrixIndex)))))

theorem core_index {n} : (fun i : Fin (n+1) => Fin.rev (matrixIndex i)) =
    (fun i => BoundEmbedding.unaryUnderTwo (Fin.rev i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [matrixIndex, Fin.lastCases_last, Fin.rev_last,
      BoundEmbedding.unaryUnderTwo, Fin.cases_zero]
  · simp only [matrixIndex, Fin.lastCases_castSucc, Fin.rev_castSucc,
      BoundEmbedding.unaryUnderTwo, Fin.cases_succ]
    apply Fin.ext
    simp only [Fin.val_succ]

theorem source_core {n} (p : Source.Formula (n+1)) :
    Source.SetLanguage.separation p = (core p).close := rfl

theorem encode_core {n} (p : Source.Formula (n+1)) :
    ProjectSyntax.formula (core p) = ProjectNormalization.formula
      (SetTheory.Axioms.Schema.separationCore (ProjectSyntax.unary p)) := by
  simp only [core, ProjectSyntax.formula, ProjectSyntax.encode, ProjectSyntax.lift_reverse,
    Source.Formula.iff, ProjectSyntax.rename_source, core_index,
    SetTheory.Axioms.Schema.separationCore, ProjectSyntax.unary,
    ProjectSyntax.rename_project, ProjectNormalization.formula, ProjectNormalization.encode_fixed,
    Fin.rev_last, Fin.rev_castSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

theorem encode_separation {n} (p : Source.Formula (n+1)) :
    ProjectSyntax.formula (Source.SetLanguage.separation p) = ProjectNormalization.formula
      (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p)).formula := by
  rw [source_core, ProjectSyntax.close_formula, encode_core]
  exact (ProjectNormalization.close_formula _).symm

theorem fo_closed (p : Source.Sentence) :
    SetTheory.Definitional.Project.fo_formula (ProjectSyntax.formula p)
      (ProjectSyntax.freeClosed Fin.rev p) = Translation.sentence p := by
  change SetTheory.Definitional.Project.fo_formula (ProjectSyntax.encode Fin.rev p) _ = _
  rw [ProjectSyntax.fo_encode]
  have e : (fun i : Fin 0 => SetTheory.Definitional.Project.fo_bound_variable (Fin.rev i)) =
      (Fin.elim0 : Fin 0 → Variable ([] : Syntax.Ctx) SetSort.set) := by
    funext i
    exact Fin.elim0 i
  rw [e]
  rfl

/-- 所有源分离模式实例的原生公式，与原分离公理的规范形严格相等。 -/
theorem separation_ast {n} (p : Source.Formula (n+1)) :
    Translation.sentence (Source.SetLanguage.separation p) = Normalization.formula
      (SetTheory.Definitional.Project.fo_sentence
        (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p))) := by
  calc
    _ = SetTheory.Definitional.Project.fo_formula
        (ProjectSyntax.formula (Source.SetLanguage.separation p))
        (ProjectSyntax.freeClosed Fin.rev (Source.SetLanguage.separation p)) := (fo_closed _).symm
    _ = SetTheory.Definitional.Project.fo_formula
        (ProjectNormalization.formula (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p)).formula)
        (ProjectNormalization.freeClosed _ (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p)).freeClosed) :=
      ProjectSyntax.fo_congr (encode_separation p)
    _ = _ := ProjectNormalization.fo_formula _ _

/-- 每个任意参数源分离实例，在原Collection版ZF中有实际原核证明。 -/
theorem source_separation {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (Source.SetLanguage.separation p)) :=
  ZFEquivalence.to_source (.separation (ProjectSyntax.unary p)) (separation_ast p)

/-- 同一任意矩阵的原生分离实例，可从源Replacement版ZF的句子像回放。 -/
theorem native_separation_of_source_matrix {n} (p : Source.Formula (n+1)) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (SetTheory.Definitional.Project.fo_sentence
        (SetTheory.Axioms.Schema.separation (ProjectSyntax.unary p))) :=
  ZFEquivalence.to_native (.separation p) (separation_ast p)
end PPAC.Migration.SeparationSyntax
