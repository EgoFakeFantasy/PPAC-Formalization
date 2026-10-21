import PPAC.Migration.ProjectDecode
import PPAC.Migration.SeparationSyntax

/-! 任意原生Project矩阵的分离模式反向覆盖，保留全部参数。 -/
namespace PPAC.Migration.SeparationReverse
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

theorem matrix_index {n} :
    (fun i : Fin (n+1) => Fin.rev (BoundEmbedding.unaryUnderTwo i)) =
      (fun i => SeparationSyntax.matrixIndex (Fin.rev i)) := by
  funext i
  have h := congrFun (@SeparationSyntax.core_index n) (Fin.rev i)
  have h' := congrArg Fin.rev h
  simpa only [Fin.rev_rev] using h'.symm

theorem rev_one {n} : Fin.rev (1 : Fin (n+3)) = (Fin.last (n+1)).castSucc := by
  rw [← Fin.succ_zero_eq_one, Fin.rev_succ, Fin.rev_zero]

theorem rev_two {n} : Fin.rev (2 : Fin (n+3)) = (Fin.last n).castSucc.castSucc := by
  rw [← Fin.succ_one_eq_two, Fin.rev_succ, ← Fin.succ_zero_eq_one, Fin.rev_succ, Fin.rev_zero]

theorem decode_core {n} (s : Definitional.Project.UnarySchema n)
    (h : (Axioms.Schema.separationCore s).FreeClosed) :
    ProjectDecode.reverse (Axioms.Schema.separationCore s) h =
      SeparationSyntax.core (ProjectDecode.reverse s.body s.freeClosed) := by
  have hm : (s.body.rename BoundEmbedding.unaryUnderTwo).FreeClosed :=
    (Definitional.Formula.freeClosed_rename _ _).mpr s.freeClosed
  have he := ProjectDecode.rename_project Fin.rev BoundEmbedding.unaryUnderTwo s.body s.freeClosed hm
  simp only [ProjectDecode.reverse, Axioms.Schema.separationCore,
    ProjectDecode.formula, ProjectDecode.lift_reverse,
    SeparationSyntax.core, Source.Formula.iff, he,
    ProjectDecode.rename_source, matrix_index, ProjectDecode.term, Fin.rev_zero, rev_one, rev_two]

theorem decode_separation {n} (s : Definitional.Project.UnarySchema n) :
    ProjectDecode.reverse (Axioms.Schema.separation s).formula
      (Axioms.Schema.separation s).freeClosed =
      Source.SetLanguage.separation (ProjectDecode.reverse s.body s.freeClosed) := by
  have hc : (Axioms.Schema.separationCore s).FreeClosed := by
    simp [Axioms.Schema.separationCore, Definitional.Formula.FreeClosed, s.freeClosed]
  have hall : (Definitional.Project.Formula.forallClosure n (Axioms.Schema.separationCore s)).FreeClosed :=
    (Definitional.Formula.freeClosed_forallClosure _).mpr hc
  calc
    _ = (ProjectDecode.reverse (Axioms.Schema.separationCore s) hc).close := by
      simpa only [Axioms.Schema.separation, Definitional.Project.Sentence.forallClosure] using
        ProjectDecode.close_formula (Axioms.Schema.separationCore s) hc hall
    _ = (SeparationSyntax.core (ProjectDecode.reverse s.body s.freeClosed)).close :=
      congrArg Source.Formula.close (decode_core s hc)
    _ = _ := (SeparationSyntax.source_core _).symm

theorem separation_ast {n} (s : Definitional.Project.UnarySchema n) :
    Translation.sentence (Source.SetLanguage.separation (ProjectDecode.reverse s.body s.freeClosed)) =
      Normalization.formula (Definitional.Project.fo_sentence (Axioms.Schema.separation s)) := by
  rw [← decode_separation]
  exact ProjectDecode.closed_fo _

/-- 任意参数、任意原Project矩阵，确实从源ZF句子像得到原核Derives。 -/
theorem native_separation {n} (s : Definitional.Project.UnarySchema n) :
    FirstOrder.Derives ZFEquivalence.sourceZF []
      (Definitional.Project.fo_sentence (Axioms.Schema.separation s)) :=
  ZFEquivalence.to_native (.separation (ProjectDecode.reverse s.body s.freeClosed)) (separation_ast s)
end PPAC.Migration.SeparationReverse
