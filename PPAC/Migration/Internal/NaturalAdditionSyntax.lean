import PPAC.Migration.Internal.NaturalSuccessorStep

/-! 内部加法由自然后继步进的实际递归图定义；自然数值域在结论中实际证明。 -/
namespace PPAC.Migration.Internal.NaturalAdditionSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates

def params {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w
def sum {m} (w a n y : Fin m) : Formula m := NaturalEvaluationSyntax.evaluation NaturalSuccessorStep.matrix (params w) w a n y
def existsSum {m} (w a n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc n.castSucc (Fin.last m)))
def fiber {m} (w a n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc n.castSucc (Fin.last m))).conj (.all
    ((sum w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem sum_rename {m k} (w a n y : Fin m) (r : Fin m → Fin k) :
    (sum w a n y).rename r = sum (r w) (r a) (r n) (r y) := by
  simp only [sum, NaturalEvaluationSyntax.evaluation_rename]
  rfl
theorem existsSum_rename {m k} (w a n : Fin m) (r : Fin m → Fin k) :
    (existsSum w a n).rename r = existsSum (r w) (r a) (r n) := by
  simp only [existsSum, Formula.rename, sum_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem fiber_rename {m k} (w a n : Fin m) (r : Fin m → Fin k) :
    (fiber w a n).rename r = fiber (r w) (r a) (r n) := by
  simp only [fiber, Formula.rename, sum_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem output_subst {m} {Γ : Context m} (w a n y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (sum w a n y)) : Derives Γ (sum w a n z) := by
  have hi : Derives Γ ((sum w.castSucc a.castSucc n.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have hout := Derives.eqSubst (sum w.castSucc a.castSucc n.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout

theorem intro_exists {m} {Γ : Context m} (w a n y : Fin m) (hw : Derives Γ (.mem y w))
    (hy : Derives Γ (sum w a n y)) : Derives Γ (existsSum w a n) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hw hy
end PPAC.Migration.Internal.NaturalAdditionSyntax
