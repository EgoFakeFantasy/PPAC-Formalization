import PPAC.Migration.Internal.FormulaCodeKnownLogical

/-! 已知原四种原子构造码时，FormulaCode精确还原原子类型条件。 -/
namespace PPAC.Migration.Internal.FormulaCodeKnownAtomic
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeCaseLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem atomic_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (arity label : Nat) (hl : label < 4)
    (w b f n : Fin m) (xs : Fin arity → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor arity label w xs n)) :
    Derives Γ ((formulaCode w n b f).iff (atomic w b f n)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have hn := SyntaxNodeInjective.constructor_range hZ arity label w xs n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (atomic w b f n)) := by
      apply all_imp w n b f (atomic w b f n)
      · exact .impI (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false arity label (by omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 arity label (by simp only [SyntaxLogicalSyntax.binaryTag]; omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 arity label (by simp only [SyntaxLogicalSyntax.binaryTag]; omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 arity label (by simp only [SyntaxLogicalSyntax.binaryTag]; omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 arity label (by simp only [SyntaxLogicalSyntax.binaryTag]; omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true arity label (by omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true arity label (by omega) w b f n xs
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    exact .impE (add (.conjR hr) _) (.conjI (add hn _) (.disjL (.hyp (Or.inl rfl))))

theorem nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((formulaCode w n b f).iff (contexts w b f)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (atomic_iff hZ 0 (nullaryTag truth) (by cases truth <;> decide) w b f n Fin.elim0 hw hc)
    (SyntaxAtomCases.nullary_atomic_iff truth w b f n hc)

theorem member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) :
    Derives Γ ((formulaCode w n b f).iff (memberTypes w b f s x y)) :=
  SyntaxTypeLocalTransfer.iff_trans (atomic_iff hZ 3 2 (by decide) w b f n (three s x y) hw hc)
    (SyntaxAtomCases.member_atomic_iff hZ w b f s x y n hw hc)

theorem equal_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) :
    Derives Γ ((formulaCode w n b f).iff (equalTypes w b f x y)) :=
  SyntaxTypeLocalTransfer.iff_trans (atomic_iff hZ 2 3 (by decide) w b f n (two x y) hw hc)
    (SyntaxAtomCases.equal_atomic_iff hZ w b f x y n hw hc)
end PPAC.Migration.Internal.FormulaCodeKnownAtomic
