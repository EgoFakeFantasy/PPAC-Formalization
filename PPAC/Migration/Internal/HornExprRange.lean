import PPAC.Migration.Internal.HornExprSyntax

/-! 上游固定表达式在全部内部自然赋值下保持自然数值域。 -/
namespace PPAC.Migration.Internal.HornExprRange
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem range {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hy : Derives Γ (graph e w env y)) : Derives Γ (.mem y w) := by
  induction e generalizing m with
  | literal k => exact SyntaxNumerals.range hZ k w y hw hy
  | var i => exact mem_subst (eq_symm (.conjR hy)) (.conjL hy)
  | succ e ih =>
    let B := (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)).conj (successor y.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise Γ)
    apply Derives.exE (p := B) hy
    have hZ1 := ZFContext.under hZ B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact OmegaStructureAlgebra.successor_member w.castSucc y.castSucc (Fin.last m) (ZFContext.arithmetic hZ1).base.extensionality hw1 (ih hZ1 _ _ _ hw1 hn1 (.conjL hB)) (.conjR hB)
  | pair e f _ _ =>
    let B := (graph e w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last m).castSucc).conj
      ((graph f w.castSucc.castSucc (fun i => (env i).castSucc.castSucc) (Fin.last (m+1))).conj
        (GodelPairSyntax.code w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
    apply SyntaxRenameBinders.eliminate_2 B _ hy
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact GodelPairCore.range (SyntaxRenameBinders.zf_under_2 hZ B) _ _ _ _ hw2 (.conjR (.conjR hB))

end PPAC.Migration.Internal.HornExprRange
