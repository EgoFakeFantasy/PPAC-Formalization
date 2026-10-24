import PPAC.Migration.Internal.ProjectSourceLocalSyntax

/-! 完整Project十二构造局部判据保留全部内部上下文守卫和真实自然码范围。 -/
namespace PPAC.Migration.Internal.ProjectSourceLocal
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax ProjectSourceLocalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem context {m} {Γ : Context m} (w b f h n : Fin m)
    (ht : Derives Γ (localType w b f h n)) : Derives Γ (contexts w b f) := by
  apply Derives.disjE ht
  · exact ProjectSourceAtoms.context w b f n (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .conjL (.hyp (Or.inl rfl))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact .conjL (.hyp (Or.inl rfl))
        · apply Derives.disjE (.hyp (Or.inl rfl))
          · exact .conjL (.hyp (Or.inl rfl))
          · apply Derives.disjE (.hyp (Or.inl rfl))
            · exact .conjL (.hyp (Or.inl rfl))
            · apply Derives.disjE (.hyp (Or.inl rfl))
              · exact .conjL (.hyp (Or.inl rfl))
              · exact .conjL (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f h n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (localType w b f h n)) : Derives Γ (.mem n w) := by
  apply Derives.disjE ht
  · exact ProjectSourceAtoms.range (ZFContext.add (hZ) _) w b f n (add (hw) _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact SyntaxLogicalFields.single_range (ZFContext.add (ZFContext.add (hZ) _) _) 4 false w b f h n (add (add (hw) _) _) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact SyntaxLogicalFields.binary_range (ZFContext.add (ZFContext.add (ZFContext.add (hZ) _) _) _) 0 w b f h n (add (add (add (hw) _) _) _) (.hyp (Or.inl rfl))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact SyntaxLogicalFields.binary_range (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (hZ) _) _) _) _) 1 w b f h n (add (add (add (add (hw) _) _) _) _) (.hyp (Or.inl rfl))
        · apply Derives.disjE (.hyp (Or.inl rfl))
          · exact SyntaxLogicalFields.binary_range (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (hZ) _) _) _) _) _) 2 w b f h n (add (add (add (add (add (hw) _) _) _) _) _) (.hyp (Or.inl rfl))
          · apply Derives.disjE (.hyp (Or.inl rfl))
            · exact SyntaxLogicalFields.binary_range (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (hZ) _) _) _) _) _) _) 3 w b f h n (add (add (add (add (add (add (hw) _) _) _) _) _) _) (.hyp (Or.inl rfl))
            · apply Derives.disjE (.hyp (Or.inl rfl))
              · exact SyntaxLogicalFields.single_range (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (hZ) _) _) _) _) _) _) _) 9 true w b f h n (add (add (add (add (add (add (add (hw) _) _) _) _) _) _) _) (.hyp (Or.inl rfl))
              · exact SyntaxLogicalFields.single_range (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (hZ) _) _) _) _) _) _) _) 10 true w b f h n (add (add (add (add (add (add (add (hw) _) _) _) _) _) _) _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.ProjectSourceLocal
