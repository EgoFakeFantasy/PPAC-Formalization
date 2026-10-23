import PPAC.Migration.Internal.OriginalArgumentsRowCases

/-! 原数值行及运行的对象等词传输；元数据相等不抽取宿主值。 -/
namespace PPAC.Migration.Internal.OriginalRowMetadataSubstitution
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem row_mode {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output r replacement : Fin m)
    (he : Derives Γ (.equal mode replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.row kind w mode depth parameter input output r)) :
    Derives Γ (OriginalTransformRowSyntax.row kind w replacement depth parameter input output r) := by
  let P := OriginalTransformRowSyntax.row kind w.castSucc (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc r.castSucc
  have h0 : P.instantiate mode = OriginalTransformRowSyntax.row kind w mode depth parameter input output r := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.row kind w replacement depth parameter input output r := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem row_depth {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output r replacement : Fin m)
    (he : Derives Γ (.equal depth replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.row kind w mode depth parameter input output r)) :
    Derives Γ (OriginalTransformRowSyntax.row kind w mode replacement parameter input output r) := by
  let P := OriginalTransformRowSyntax.row kind w.castSucc mode.castSucc (Fin.last m) parameter.castSucc input.castSucc output.castSucc r.castSucc
  have h0 : P.instantiate depth = OriginalTransformRowSyntax.row kind w mode depth parameter input output r := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.row kind w mode replacement parameter input output r := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem row_parameter {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output r replacement : Fin m)
    (he : Derives Γ (.equal parameter replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.row kind w mode depth parameter input output r)) :
    Derives Γ (OriginalTransformRowSyntax.row kind w mode depth replacement input output r) := by
  let P := OriginalTransformRowSyntax.row kind w.castSucc mode.castSucc depth.castSucc (Fin.last m) input.castSucc output.castSucc r.castSucc
  have h0 : P.instantiate parameter = OriginalTransformRowSyntax.row kind w mode depth parameter input output r := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.row kind w mode depth replacement input output r := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem row_fields {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output r M D P : Fin m)
    (hm : Derives Γ (.equal mode M)) (hd : Derives Γ (.equal depth D)) (hp : Derives Γ (.equal parameter P))
    (hr : Derives Γ (OriginalTransformRowSyntax.row kind w mode depth parameter input output r)) : Derives Γ (OriginalTransformRowSyntax.row kind w M D P input output r) :=
  row_parameter kind w M D parameter input output r P hp (row_depth kind w M depth parameter input output r D hd (row_mode kind w mode depth parameter input output r M hm hr))

theorem run_mode {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output replacement : Fin m)
    (he : Derives Γ (.equal mode replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) :
    Derives Γ (OriginalTransformRowSyntax.run kind w replacement depth parameter input output) := by
  let P := OriginalTransformRowSyntax.run kind w.castSucc (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc
  have h0 : P.instantiate mode = OriginalTransformRowSyntax.run kind w mode depth parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.run kind w replacement depth parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem run_depth {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output replacement : Fin m)
    (he : Derives Γ (.equal depth replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) :
    Derives Γ (OriginalTransformRowSyntax.run kind w mode replacement parameter input output) := by
  let P := OriginalTransformRowSyntax.run kind w.castSucc mode.castSucc (Fin.last m) parameter.castSucc input.castSucc output.castSucc
  have h0 : P.instantiate depth = OriginalTransformRowSyntax.run kind w mode depth parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.run kind w mode replacement parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem run_parameter {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output replacement : Fin m)
    (he : Derives Γ (.equal parameter replacement)) (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) :
    Derives Γ (OriginalTransformRowSyntax.run kind w mode depth replacement input output) := by
  let P := OriginalTransformRowSyntax.run kind w.castSucc mode.castSucc depth.castSucc (Fin.last m) input.castSucc output.castSucc
  have h0 : P.instantiate parameter = OriginalTransformRowSyntax.run kind w mode depth parameter input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate replacement = OriginalTransformRowSyntax.run kind w mode depth replacement input output := by simp only [P, Formula.instantiate, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem run_fields {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output M D P : Fin m)
    (hm : Derives Γ (.equal mode M)) (hd : Derives Γ (.equal depth D)) (hp : Derives Γ (.equal parameter P))
    (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) : Derives Γ (OriginalTransformRowSyntax.run kind w M D P input output) :=
  run_parameter kind w M D parameter input output P hp (run_depth kind w M depth parameter input output D hd (run_mode kind w mode depth parameter input output M hm hr))

end PPAC.Migration.Internal.OriginalRowMetadataSubstitution
