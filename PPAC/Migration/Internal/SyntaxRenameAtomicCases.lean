import PPAC.Migration.Internal.SyntaxRenameBranchReject

/-! 给定原源标签0至3时，完整11类重命名矩阵精确筛回对应原子分支。 -/
namespace PPAC.Migration.Internal.SyntaxRenameAtomicCases
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def atomicCase {m} (kind : Fin 4) (w r s a b c d n q : Fin m) : Formula m :=
  Fin.cases (SyntaxRenameAtomSyntax.nullary false w a b c d n q)
    (Fin.cases (SyntaxRenameAtomSyntax.nullary true w a b c d n q)
      (Fin.cases (SyntaxRenameAtomSyntax.membership w r s a b c d n q)
        (Fin.cases (SyntaxRenameAtomSyntax.equality w r s a b c d n q) Fin.elim0))) kind

theorem or_imp {m} {Γ : Context m} {p q t : Formula m}
    (hp : Derives Γ (p.imp t)) (hq : Derives Γ (q.imp t)) : Derives Γ ((p.disj q).imp t) :=
  .impE (.impE (SourcePropositional.disjunction_elimination p q t) hp) hq

theorem filter {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (arity : Nat)
    (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity kind.val w xs n))
    (hr : Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) :
    Derives Γ (atomicCase kind w r s a b c d n q) := by
  have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 0 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 0 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 0 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 0 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 0 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 0 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (atomicCase (0 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 0 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (or_imp (or_imp h_f h_t) (or_imp h_m (or_imp h_e (or_imp h_neg (or_imp h_b0 (or_imp h_b1 (or_imp h_b2 (or_imp h_b3 (or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 1 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 1 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 1 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 1 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 1 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 1 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (atomicCase (1 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 1 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (or_imp (or_imp h_f h_t) (or_imp h_m (or_imp h_e (or_imp h_neg (or_imp h_b0 (or_imp h_b1 (or_imp h_b2 (or_imp h_b3 (or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 2 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 2 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.equality (ZFContext.add hZ _) arity 2 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 2 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 2 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 2 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (atomicCase (2 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 2 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (or_imp (or_imp h_f h_t) (or_imp h_m (or_imp h_e (or_imp h_neg (or_imp h_b0 (or_imp h_b1 (or_imp h_b2 (or_imp h_b3 (or_imp h_all h_ex))))))))) hr
  · have h_f : Derives Γ ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary false w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary false w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 3 0 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_t : Derives Γ ((SyntaxRenameAtomSyntax.nullary true w a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      have hp : Derives (Context.add (SyntaxRenameAtomSyntax.nullary true w a b c d n q) Γ) (SyntaxRenameAtomSyntax.nullary true w a b c d n q) := .hyp (Or.inl rfl)
      exact .botE (SyntaxConstructors.disjoint (ZFContext.add hZ _) arity 0 3 1 (by decide) w xs Fin.elim0 n (add hw _) (add hc _) (.conjR (.conjL hp)))
    have h_m : Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.membership (ZFContext.add hZ _) arity 3 (by decide) w r s a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_e : Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .hyp (Or.inl rfl)
    have h_neg : Derives Γ ((SyntaxRenameRecursiveSyntax.single 4 false w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 3 4 false (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b0 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 0 w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 0 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b1 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 1 w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 1 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b2 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 2 w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 2 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_b3 : Derives Γ ((SyntaxRenameRecursiveSyntax.binary 3 w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.binary (ZFContext.add hZ _) arity 3 3 (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_all : Derives Γ ((SyntaxRenameRecursiveSyntax.single 9 true w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 3 9 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    have h_ex : Derives Γ ((SyntaxRenameRecursiveSyntax.single 10 true w R S a b c d n q).imp (atomicCase (3 : Fin 4) w r s a b c d n q)) := by
      apply Derives.impI
      exact .botE (SyntaxRenameBranchReject.single (ZFContext.add hZ _) arity 3 10 true (by decide) w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
    exact .impE (or_imp (or_imp h_f h_t) (or_imp h_m (or_imp h_e (or_imp h_neg (or_imp h_b0 (or_imp h_b1 (or_imp h_b2 (or_imp h_b3 (or_imp h_all h_ex))))))))) hr
end PPAC.Migration.Internal.SyntaxRenameAtomicCases
