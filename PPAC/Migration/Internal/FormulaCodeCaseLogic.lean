import PPAC.Migration.Internal.FormulaCodeBranchReject

/-! 原构造标签排除与完整八分支析取的原规则组合。 -/
namespace PPAC.Migration.Internal.FormulaCodeCaseLogic
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open FormulaCodeSyntax FormulaCodeRecursiveSyntax

theorem disj_imp {m} {Γ : Context m} {p q t : Formula m}
    (hp : Derives Γ (p.imp t)) (hq : Derives Γ (q.imp t)) : Derives Γ ((p.disj q).imp t) := by
  apply Derives.impI
  apply Derives.disjE (.hyp (Or.inl rfl))
  · exact .impE (add (add hp _) _) (.hyp (Or.inl rfl))
  · exact .impE (add (add hq _) _) (.hyp (Or.inl rfl))

theorem all_imp {m} {Γ : Context m} (w n b f : Fin m) (q : Formula m)
    (h0 : Derives Γ ((atomic w b f n).imp q))
    (h1 : Derives Γ ((singleCase 4 false w b f n).imp q))
    (h2 : Derives Γ ((binaryCase 0 w b f n).imp q))
    (h3 : Derives Γ ((binaryCase 1 w b f n).imp q))
    (h4 : Derives Γ ((binaryCase 2 w b f n).imp q))
    (h5 : Derives Γ ((binaryCase 3 w b f n).imp q))
    (h6 : Derives Γ ((singleCase 9 true w b f n).imp q))
    (h7 : Derives Γ ((singleCase 10 true w b f n).imp q)) :
    Derives Γ ((allCases w n b f).imp q) :=
  disj_imp h0 (disj_imp h1 (disj_imp h2 (disj_imp h3 (disj_imp h4 (disj_imp h5 (disj_imp h6 h7))))))

theorem atomic_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (arity label : Nat) (h0 : label ≠ 0) (h1 : label ≠ 1) (h2 : label ≠ 2) (h3 : label ≠ 3)
    (w b f n : Fin m) (xs : Fin arity → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor arity label w xs n)) (ha : Derives Γ (atomic w b f n)) : Derives Γ .bot := by
  apply Derives.disjE ha
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add hZ _) _) arity 0 label 0 h0
        w xs Fin.elim0 n (add (add hw _) _) (add (add hc _) _) (.conjR (.hyp (Or.inl rfl)))
    · exact SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add hZ _) _) arity 0 label 1 h1
        w xs Fin.elim0 n (add (add hw _) _) (add (add hc _) _) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact SyntaxAtomCases.member_conflict (ZFContext.add (ZFContext.add hZ _) _) arity label h2
        w b f n xs (add (add hw _) _) (add (add hc _) _) (.hyp (Or.inl rfl))
    · exact SyntaxAtomCases.equal_conflict (ZFContext.add (ZFContext.add hZ _) _) arity label h3
        w b f n xs (add (add hw _) _) (add (add hc _) _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.FormulaCodeCaseLogic
