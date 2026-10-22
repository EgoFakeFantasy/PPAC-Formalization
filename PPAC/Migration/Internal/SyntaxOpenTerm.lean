import PPAC.Migration.Internal.SyntaxTerms

/-! 纯成员语言的空 bound 项精确恢复实际 fvar 分支；不使用宿主项解码。 -/
namespace PPAC.Migration.Internal.SyntaxOpenTerm
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem free_branch {m} {Γ : Context m} (w z c t : Fin m)
    (hz : Derives Γ (empty z)) (ht : Derives Γ (term w z c t)) :
    Derives Γ (branch false w c t) := by
  apply Derives.disjE (.conjR ht)
  · exact .botE (.impE (add (SyntaxTermBranches.empty true w z t hz) _) (.hyp (Or.inl rfl)))
  · exact .hyp (Or.inl rfl)

theorem term_iff {m} {Γ : Context m} (w z c t : Fin m)
    (hz : Derives Γ (empty z)) (hzW : Derives Γ (.mem z w)) (hc : Derives Γ (.mem c w)) :
    Derives Γ ((term w z c t).iff (branch false w c t)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact free_branch w z c t (add hz _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .conjI (.conjI (add hzW _) (add hc _)) (.disjR (.hyp (Or.inl rfl)))

theorem at_zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z c t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (.mem c w)) :
    Derives Γ ((term w z c t).iff (branch false w c t)) :=
  term_iff w z c t hz (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz) hc

end PPAC.Migration.Internal.SyntaxOpenTerm
