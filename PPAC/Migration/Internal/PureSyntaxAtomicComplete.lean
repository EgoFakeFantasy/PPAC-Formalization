import PPAC.Migration.Internal.PureSyntaxMembershipComplete

/-! 四种完整Source原子公式均实际取得纯公式查询；不是完整kind4查询双条件。 -/
namespace PPAC.Migration.Internal.PureSyntaxAtomicComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem checked_equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxAtomSyntax.equality w b f n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let B := SyntaxAtomSyntax.equalBody w b f n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply SyntaxAtomLogic.eliminate_equality w b f n _ ht
  have hZ2 := HornBinderRules.zf_body 2 hZ B
  have hw2 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := PureSyntaxEqualityComplete.checked_equality hZ2 (old 2 w) (old 2 b) (old 2 f) (slot 2 0) (slot 2 1) (old 2 n) hw2 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB)
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.formula_rename, old]) ho

theorem checked_atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxAtomSyntax.atomic w b f n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  apply Derives.disjE ht
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact PureSyntaxConstantComplete.checked_nullary (ZFContext.add (ZFContext.add hZ _) _) false w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact PureSyntaxConstantComplete.checked_nullary (ZFContext.add (ZFContext.add hZ _) _) true w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact PureSyntaxMembershipComplete.checked_membership (ZFContext.add (ZFContext.add hZ _) _) w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact checked_equality (ZFContext.add (ZFContext.add hZ _) _) w b f n (add (add hw _) _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PureSyntaxAtomicComplete
