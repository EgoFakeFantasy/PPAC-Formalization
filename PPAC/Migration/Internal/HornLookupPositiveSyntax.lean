import PPAC.Migration.Internal.HornLookupTraceValue

/-! 实际原lookup赋值向量与子行成员引入；每个值仍是内部对象变量。 -/
namespace PPAC.Migration.Internal.HornLookupPositiveSyntax
open Source SourceAlgebra SourceLogic HornLookupRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def env2 {m} (h t : Fin m) : Fin 2 → Fin m := Source.SetLanguage.args2 h t

def env4 {m} (h t j y : Fin m) : Fin 4 → Fin m := Fin.cases h (Fin.cases t (Fin.cases j (fun _ => y)))

theorem env2_natural {m} {Γ : Context m} (w h t : Fin m) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (HornExprSyntax.environmentNat 2 w (env2 h t)) :=
  HornApplicationRules.intro_nat w (env2 h t) (fun i => Fin.cases hh (fun j => Fin.cases ht (fun z => Fin.elim0 z) j) i)

theorem env4_natural {m} {Γ : Context m} (w h t j y : Fin m) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hj : Derives Γ (.mem j w)) (hy : Derives Γ (.mem y w)) : Derives Γ (HornExprSyntax.environmentNat 4 w (env4 h t j y)) :=
  HornApplicationRules.intro_nat w (env4 h t j y) (fun i => Fin.cases hh (fun k => Fin.cases ht (fun l => Fin.cases hj (fun _ => hy) l) k) i)

theorem intro_child_member {m} {Γ : Context m} (w R r : Fin m) (env : Fin 4 → Fin m)
    (hr : Derives Γ (row w (env 1) (env 2) (env 3) r)) (hm : Derives Γ (.mem r R)) :
    Derives Γ (OriginalLookupRuleMatrix.childMember w R env) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNodeSyntax.constructor_rename, OriginalLookupRuleMatrix.rowFields_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI hr hm)

end PPAC.Migration.Internal.HornLookupPositiveSyntax
