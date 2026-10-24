import PPAC.Migration.Internal.ProjectSourceAtomSyntax

/-! Source atomic guards and natural range do not use target FormulaCode or compilation. -/
namespace PPAC.Migration.Internal.ProjectSourceAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectSourceAtomSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem binary_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (binaryAtom kind w b n)) : Derives Γ (.mem n w) := by
  let B := binaryBody kind w b n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hi
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := SyntaxRenameQuerySyntax.of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  exact SyntaxNodeInjective.constructor_range (HornBinderRules.zf_body 2 hZ B) 2 (ProjectAtomicSyntax.sourceTag kind)
    (old 2 w) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1)) (old 2 n) hw2 (.conjR (.conjR (.conjR hB)))

theorem context {m} {Γ : Context m} (w b f n : Fin m) (hi : Derives Γ (atomic w b f n)) :
    Derives Γ (SyntaxTermSyntax.contexts w b f) := by
  apply Derives.disjE hi
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
  · exact .conjL (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (atomic w b f n)) : Derives Γ (.mem n w) := by
  apply Derives.disjE hi
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact SyntaxNodeInjective.constructor_range (ZFContext.add (ZFContext.add hZ _) _) 0 0 w Fin.elim0 n
        (add (add hw _) _) (.conjR (.hyp (Or.inl rfl)))
    · exact SyntaxNodeInjective.constructor_range (ZFContext.add (ZFContext.add hZ _) _) 0 1 w Fin.elim0 n
        (add (add hw _) _) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.conjR (.hyp (Or.inl rfl)))
    · exact binary_range (ZFContext.add (ZFContext.add hZ _) _) 0 w b n (add (add hw _) _) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact binary_range (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 1 w b n (add (add (add hw _) _) _) (.hyp (Or.inl rfl))
      · exact binary_range (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 2 w b n (add (add (add hw _) _) _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProjectSourceAtoms
