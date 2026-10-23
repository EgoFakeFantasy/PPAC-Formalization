import PPAC.Migration.Internal.ObjectOriginalNumericTermFiber

/-! 原运行输入／输出及结构Cons组件的正式等词替换。 -/
namespace PPAC.Migration.Internal.OriginalRunValueSubstitution
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem run_input {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output replacement : Fin m)
    (he : Derives Γ (.equal input replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) :
    Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter replacement output) := by
  let P := OriginalTransformRowSyntax.run kind w.castSucc mode.castSucc depth.castSucc parameter.castSucc (Fin.last m) output.castSucc
  have h0 : P.instantiate input = OriginalTransformRowSyntax.run kind w mode depth parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.run kind w mode depth parameter replacement output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem run_output {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output replacement : Fin m)
    (he : Derives Γ (.equal output replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) :
    Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input replacement) := by
  let P := OriginalTransformRowSyntax.run kind w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc (Fin.last m)
  have h0 : P.instantiate output = OriginalTransformRowSyntax.run kind w mode depth parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.run kind w mode depth parameter input replacement := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem cons_head {m} {Γ : Context m} (w h t n replacement : Fin m)
    (he : Derives Γ (.equal h replacement)) (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) :
    Derives Γ (StructuralListSyntax.consCode w replacement t n) := by
  let P := StructuralListSyntax.consCode w.castSucc (Fin.last m) t.castSucc n.castSucc
  have h0 : P.instantiate h = StructuralListSyntax.consCode w h t n := by simp only [P, Formula.instantiate, StructuralListSyntax.consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = StructuralListSyntax.consCode w replacement t n := by simp only [P, Formula.instantiate, StructuralListSyntax.consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem cons_tail {m} {Γ : Context m} (w h t n replacement : Fin m)
    (he : Derives Γ (.equal t replacement)) (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) :
    Derives Γ (StructuralListSyntax.consCode w h replacement n) := by
  let P := StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) n.castSucc
  have h0 : P.instantiate t = StructuralListSyntax.consCode w h t n := by simp only [P, Formula.instantiate, StructuralListSyntax.consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = StructuralListSyntax.consCode w h replacement n := by simp only [P, Formula.instantiate, StructuralListSyntax.consCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

end PPAC.Migration.Internal.OriginalRunValueSubstitution
