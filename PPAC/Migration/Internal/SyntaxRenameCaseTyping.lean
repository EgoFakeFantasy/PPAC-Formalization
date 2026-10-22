import PPAC.Migration.Internal.SyntaxRenameBranchIntro

/-! 原重命名分支在所有内部候选上保持目标 FormulaCode，供精确已知构造律反向接入。 -/
namespace PPAC.Migration.Internal.SyntaxRenameCaseTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem target_contexts {m} {Γ : Context m} (w R S a b c d n : Fin m)
    (hi : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n)) : Derives Γ (SyntaxTermSyntax.contexts w c d) := by
  have hR := SyntaxMapCodeDecode.contexts w a c R (.conjL (.conjR hi))
  have hS := SyntaxMapCodeDecode.contexts w b d S (.conjR (.conjR hi))
  exact .conjI (.conjR hR) (.conjR hS)

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (SyntaxRenameAtomSyntax.nullary truth w a b c d n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q c d) :=
  .impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w c d q hw (.conjR (.conjR hr)))) (.conjL (.conjR hr))

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r s a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxRenameAtomSyntax.membership w r s a b c d n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  let B := SyntaxRenameAtomSyntax.membershipBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))
  apply eliminate_5 B _ hr
  have hZk := zf_under_5 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_5 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameTermTyping.target_term w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (.conjL (.conjR (.conjR (.conjR hB))))
  have hy := SyntaxRenameTermTyping.target_term w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+4)) (.conjR (.conjR (.conjR (.conjR hB))))
  have ho := Derives.impE (.conjR (FormulaCodeKnownAtomic.member_iff hZk w.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) q.castSucc.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR (.conjR hB))))) (.conjI (.conjL hB) (.conjI hx hy))
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r s a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (SyntaxRenameAtomSyntax.equality w r s a b c d n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  let B := SyntaxRenameAtomSyntax.equalityBody w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ hr
  have hZk := zf_under_4 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameTermTyping.target_term w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (.conjL (.conjR (.conjR hB)))
  have hy := SyntaxRenameTermTyping.target_term w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (.conjR (.conjR (.conjR hB)))
  have ho := Derives.impE (.conjR (FormulaCodeKnownAtomic.equal_iff hZk w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) q.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR hB)))) (.conjI hx hy)
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w r s a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hr : Derives Γ (SyntaxRenameRecursiveSyntax.single tag advance w r s a b c d n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  let B := SyntaxRenameRecursiveSyntax.singleBody tag advance w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply eliminate_2 B _ hr
  have hZk := zf_under_2 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hctxk : Derives Δ (SyntaxTermSyntax.contexts w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (under_2 hctx B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameCheckUnique.target_type advance w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) (.conjR (.conjR (.conjR hB)))
  have ho := Derives.impE (.conjR (SyntaxRenameLogicalConstruct.single_types hZk tag advance valid w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc hwk (.conjL (.conjR (.conjR hB))))) (.conjI hctxk hx)
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w r s a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hr : Derives Γ (SyntaxRenameRecursiveSyntax.binary kind w r s a b c d n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  let B := SyntaxRenameRecursiveSyntax.binaryBody kind w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))
  apply eliminate_4 B _ hr
  have hZk := zf_under_4 hZ B
  have hwk : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_4 hw B)
  have hctxk : Derives Δ (SyntaxTermSyntax.contexts w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.contexts_rename]) (under_4 hctx B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hx := SyntaxRenameJudgment.target_type w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (.conjL (.conjR (.conjR (.conjR (.conjR hB)))))
  have hy := SyntaxRenameJudgment.target_type w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (.conjR (.conjR (.conjR (.conjR (.conjR hB)))))
  have ho := Derives.impE (.conjR (SyntaxRenameLogicalConstruct.binary_types hZk kind w.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) q.castSucc.castSucc.castSucc.castSucc hwk (.conjL (.conjR (.conjR (.conjR hB)))))) (.conjI hctxk (.conjI hx hy))
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

theorem selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 11)
    (w R S r s a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n))
    (hb : Derives Γ (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q c d) := by
  have hctx := target_contexts w R S a b c d n hi
  have hk : kind = (0 : Fin 11) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5 ∨ kind = 6 ∨ kind = 7 ∨ kind = 8 ∨ kind = 9 ∨ kind = 10 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nullary hZ false w a b c d n q hw hb
  · exact nullary hZ true w a b c d n q hw hb
  · exact membership hZ w r s a b c d n q hw hb
  · exact equality hZ w r s a b c d n q hw hb
  · exact single hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S a b c d n q hw hctx hb
  · exact binary hZ 0 w R S a b c d n q hw hctx hb
  · exact binary hZ 1 w R S a b c d n q hw hctx hb
  · exact binary hZ 2 w R S a b c d n q hw hctx hb
  · exact binary hZ 3 w R S a b c d n q hw hctx hb
  · exact single hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S a b c d n q hw hctx hb
  · exact single hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S a b c d n q hw hctx hb
end PPAC.Migration.Internal.SyntaxRenameCaseTyping
