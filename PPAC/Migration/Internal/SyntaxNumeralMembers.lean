import PPAC.Migration.Internal.SyntaxPositionSyntax

/-! 有限数码的成员在所有内部候选上精确分类；不假设内部候选外部标准。 -/
namespace PPAC.Migration.Internal.SyntaxNumeralMembers
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax SyntaxPositionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (l i : Fin m)
    (hl : Derives Γ (numeral k l)) : Derives Γ ((Formula.mem i l).iff (below k i)) := by
  induction k generalizing m with
  | zero =>
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (OmegaSyntax.empty_at l i hl) _) (.hyp (Or.inl rfl))
    · exact .impI (.botE (.hyp (Or.inl rfl)))
  | succ k ih =>
    let L := (numeral k (Fin.last m)).conj (successor l.castSucc (Fin.last m))
    let Δ := Context.add L (Context.image Formula.raise Γ)
    apply eliminate_succ k l _ hl
    have hZ1 := ZFContext.under hZ L
    have hL : Derives Δ L := .hyp (Or.inl rfl)
    have hp := ih hZ1 (Fin.last m) i.castSucc (.conjL hL)
    have hs := InsertSyntax.insert_at l.castSucc (Fin.last m) (Fin.last m) i.castSucc (.conjR hL)
    have hn : Derives Δ ((Formula.equal i.castSucc (Fin.last m)).iff (numeral k i.castSucc)) := by
      apply Derives.conjI
      · apply Derives.impI
        exact output_subst k (Fin.last m) i.castSucc (eq_symm (.hyp (Or.inl rfl))) (add (.conjL hL) _)
      · apply Derives.impI
        exact SyntaxNumerals.unique (ZFContext.add hZ1 _) k i.castSucc (Fin.last m) (.hyp (Or.inl rfl)) (add (.conjL hL) _)
    have hout := SyntaxTypeLocalTransfer.iff_trans hs (SyntaxTypeLocalTransfer.disj_congr hp hn)
    simpa only [Formula.raise, Formula.iff, Formula.rename, below, below_rename, numeral_rename] using hout

theorem index_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (j : Fin k) (l i : Fin m)
    (hl : Derives Γ (numeral k l)) (hi : Derives Γ (numeral j.val i)) : Derives Γ (.mem i l) :=
  .impE (.conjR (member_iff hZ k l i hl)) (intro_below k j i hi)
end PPAC.Migration.Internal.SyntaxNumeralMembers
