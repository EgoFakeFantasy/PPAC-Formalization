import PPAC.Migration.Internal.ObjectSyntaxRenameAtomic

/-! 原11个固定标签下的完整重命名分支精确筛选；内部码和字段不限制外部标准性。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTagCases
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def tagBranch {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : Formula m := Fin.cases (SyntaxRenameAtomSyntax.nullary false w a b c d n q) (Fin.cases (SyntaxRenameAtomSyntax.nullary true w a b c d n q) (Fin.cases (SyntaxRenameAtomSyntax.membership w r s a b c d n q) (Fin.cases (SyntaxRenameAtomSyntax.equality w r s a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q) (Fin.cases (SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q) (Fin.elim0))))))))))) kind

theorem tagBranch_rename {m k} (kind : Fin 11) (w R S r s a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (tagBranch kind w R S r s a b c d n q).rename ρ = tagBranch kind (ρ w) (ρ R) (ρ S) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  have hk : kind = (0 : Fin 11) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5 ∨ kind = 6 ∨ kind = 7 ∨ kind = 8 ∨ kind = 9 ∨ kind = 10 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact SyntaxRenameAtomSyntax.nullary_rename false w a b c d n q ρ
  · exact SyntaxRenameAtomSyntax.nullary_rename true w a b c d n q ρ
  · exact SyntaxRenameAtomSyntax.membership_rename w r s a b c d n q ρ
  · exact SyntaxRenameAtomSyntax.equality_rename w r s a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.single_rename 4 false w R S a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.binary_rename 0 w R S a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.binary_rename 1 w R S a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.binary_rename 2 w R S a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.binary_rename 3 w R S a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.single_rename 9 true w R S a b c d n q ρ
  · exact SyntaxRenameRecursiveSyntax.single_rename 10 true w R S a b c d n q ρ

theorem filter {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 11) (arity : Nat)
    (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity kind.val w xs n))
    (hr : Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) : Derives Γ (tagBranch kind w R S r s a b c d n q) := by
  have hk : kind = (0 : Fin 11) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5 ∨ kind = 6 ∨ kind = 7 ∨ kind = 8 ∨ kind = 9 ∨ kind = 10 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 0 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 0 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 0 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 0 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 0 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (0 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 0 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 1 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 1 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 1 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 1 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 1 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (1 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 1 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 2 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 2 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 2 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 2 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 2 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (2 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 2 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 3 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 3 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 3 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 3 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 3 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (3 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 3 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 4 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 4 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 4 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 4 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 4 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 4 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 4 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 4 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 4 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (4 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 4 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 5 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 5 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 5 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 5 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 5 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 5 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 5 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 5 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 5 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (5 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 5 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 6 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 6 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 6 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 6 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 6 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 6 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 6 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 6 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 6 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (6 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 6 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 7 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 7 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 7 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 7 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 7 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 7 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 7 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 7 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 7 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (7 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 7 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 8 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 8 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 8 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 8 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 8 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 8 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 8 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 8 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 8 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (8 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 8 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 9 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 9 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 9 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 9 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 9 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 9 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 9 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 9 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 9 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (9 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 9 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 10 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 10 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 10 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 10 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 10 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 10 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 10 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 10 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 10 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 10 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (tagBranch (10 : Fin 11) w R S r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    exact .impE (SyntaxRenameAtomicCases.or_imp (SyntaxRenameAtomicCases.or_imp h_f h_t) (SyntaxRenameAtomicCases.or_imp h_m (SyntaxRenameAtomicCases.or_imp h_e (SyntaxRenameAtomicCases.or_imp h_neg (SyntaxRenameAtomicCases.or_imp h_b0 (SyntaxRenameAtomicCases.or_imp h_b1 (SyntaxRenameAtomicCases.or_imp h_b2 (SyntaxRenameAtomicCases.or_imp h_b3 (SyntaxRenameAtomicCases.or_imp h_all h_ex))))))))) hr

theorem of_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 11) (arity : Nat)
    (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R))
    (hS : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (constructor arity kind.val w xs n))
    (hr : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) :
    Derives Γ (tagBranch kind w R S r s a b c d n q) :=
  filter hZ kind arity w R S r s a b c d n q xs hw hc (SyntaxRenameActualGraphs.cases_of_renamed hZ w R S r s a b c d n q hw hR hS hr)
end PPAC.Migration.Internal.SyntaxRenameTagCases
