import PPAC.Migration.Internal.OriginalArgumentCaseSyntax

/-! 实际原运行的输入/输出自然性来自真实五字段行，不从宿主执行抽取。 -/
namespace PPAC.Migration.Internal.OriginalArgumentRunNaturality
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem input_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (w mode depth parameter input output : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) : Derives Γ (.mem input w) := by
  let B := (OriginalTransformRowSyntax.row kind w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact OriginalArgumentsMetadata.field_natural (ZFContext.under hZ B) kind _ _ _ _ _ _ _ 3 hw1 (.conjL hB)

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (w mode depth parameter input output : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (OriginalTransformRowSyntax.run kind w mode depth parameter input output)) : Derives Γ (.mem output w) := by
  let B := (OriginalTransformRowSyntax.row kind w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact OriginalArgumentsMetadata.field_natural (ZFContext.under hZ B) kind _ _ _ _ _ _ _ 4 hw1 (.conjL hB)

end PPAC.Migration.Internal.OriginalArgumentRunNaturality
