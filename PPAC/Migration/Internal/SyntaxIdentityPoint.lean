import PPAC.Migration.Internal.SyntaxIdentityLogical

/-! 全11原构造推进公式恒等的四内部参数成员归纳；原存在字段均被消去。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityPoint
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameIdentitySyntax
open SyntaxIdentityMapSyntax FormulaCodeRecursiveSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b n : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (singleCase tag advance w a b n)) : Derives Γ (self w R S a b n) := by
  let B := singleCaseBody tag advance w a b n
  let Δ := Context.add B (Context.image Formula.raise (Γ))
  apply eliminate_single tag advance w a b n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have he1 : Derives Δ (earlier w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he B)
  have hr1 : Derives Δ (identityCode w.castSucc a.castSucc R.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under hr B)
  have hs1 : Derives Δ (identityCode w.castSucc b.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under hs B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxIdentityLogical.single_step (ZFContext.under hZ B) tag advance valid w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc n.castSucc (Fin.last m) hw1 he1 hr1 hs1 (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, self_rename]) ho

theorem binary_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b n : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (binaryCase kind w a b n)) : Derives Γ (self w R S a b n) := by
  let B := binaryCaseBody kind w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply eliminate_binary kind w a b n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 he B)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under_2 hr B)
  have hs2 : Derives Δ (identityCode w.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under_2 hs B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxIdentityLogical.binary_step (zf_under_2 hZ B) kind w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 he2 hr2 hs2 (.conjL hB) (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, self_rename]) ho

theorem from_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ (self w R S a b n) := by
  have hrule := FormulaCodeRecursive.recursive_iff hZ w n a b hw
  have hcases : Derives Γ ((allCases w n a b).imp (self w R S a b n)) := by
    apply FormulaCodeCaseLogic.all_imp w n a b (self w R S a b n)
    · apply Derives.impI
      exact SyntaxIdentityAtomic.at_codes (ZFContext.add hZ _) w R S a b n (add hw _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl,rfl⟩) w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 0 w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 1 w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 2 w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 3 w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w R S a b n (add hw _) (add he _) (add hr _) (add hs _) (.hyp (Or.inl rfl))
  exact .impE hcases (.conjR (.impE (.conjL hrule) hc))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw I)
  have he4 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_4 he I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  exact from_code (zf_under_4 hZ I) w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc hw4 he4 (.conjL (.conjR hI)) (.conjR (.conjR hI)) (.conjL hI)
end PPAC.Migration.Internal.SyntaxIdentityPoint
