import PPAC.Migration.Internal.FormulaCodeKnownAtomic

/-! 未知内部自然标签的完整拒绝；payload/字段长度不受外部标准界限制。 -/
namespace PPAC.Migration.Internal.FormulaCodeUnknownTag
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax
open FormulaCodeCaseLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

def unknownTags {m} : Nat → Fin m → Formula m
  | 0, t => .equal t t
  | k+1, t => (unknownTags k t).conj (numeral k t).neg

theorem unknownTags_rename {m l} (k : Nat) (t : Fin m) (r : Fin m → Fin l) :
    (unknownTags k t).rename r = unknownTags k (r t) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [unknownTags, Formula.neg, Formula.rename, numeral_rename, ih]

theorem numeral_neg {m} {Γ : Context m} (k i : Nat) (hi : i < k) (t : Fin m) (hb : Derives Γ (unknownTags k t)) :
    Derives Γ (numeral i t).neg := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i = k
    · subst i
      exact .conjR hb
    · exact ih (by omega) (.conjL hb)

theorem reject {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hb : Derives Γ (unknownTags 11 t)) (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) :
    Derives Γ (formulaCode w n b f).neg := by
  have he := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  apply Derives.impI
  let F := formulaCode w n b f
  let Ξ := Context.add F Γ
  have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  have himp : Derives Ξ ((allCases w n b f).imp .bot) := by
    apply all_imp w n b f .bot
    · apply Derives.impI
      have ha : Derives (Context.add (SyntaxAtomSyntax.atomic w b f n) Ξ) (SyntaxAtomSyntax.atomic w b f n).neg := SyntaxAtomReject.atomic_unknown_tag (ZFContext.add (ZFContext.add hZ F) _)
        w b f t p n (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 0 (by decide) t (add (add hb F) _)) (numeral_neg 11 1 (by decide) t (add (add hb F) _))
        (numeral_neg 11 2 (by decide) t (add (add hb F) _)) (numeral_neg 11 3 (by decide) t (add (add hb F) _))
        (add (add hr F) _)
      exact .impE ha (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeBranchReject.single_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 4 false w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 4 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
    · apply Derives.impI
      exact FormulaCodeBranchReject.binary_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 0 w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 5 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
    · apply Derives.impI
      exact FormulaCodeBranchReject.binary_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 1 w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 6 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
    · apply Derives.impI
      exact FormulaCodeBranchReject.binary_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 2 w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 7 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
    · apply Derives.impI
      exact FormulaCodeBranchReject.binary_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 3 w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 8 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
    · apply Derives.impI
      exact FormulaCodeBranchReject.single_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 9 true w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 9 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
    · apply Derives.impI
      exact FormulaCodeBranchReject.single_unknown_tag (ZFContext.add (ZFContext.add hZ F) _) 10 true w b f t p n
        (add (add hw F) _) (add (add ht F) _) (add (add hp F) _)
        (numeral_neg 11 10 (by decide) t (add (add hb F) _)) (.hyp (Or.inl rfl)) (add (add hr F) _)
  exact .impE himp hall
end PPAC.Migration.Internal.FormulaCodeUnknownTag
