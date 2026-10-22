import PPAC.Migration.Internal.SyntaxFormulaComposeLogical

/-! 全11构造的14内部参数复合推进；实际图见证与源字段均由原存在消去取得。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposePoint
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaComposeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true)) (w R S T U K L r s t u g h a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hc : Derives Γ (FormulaCodeRecursiveSyntax.singleCase tag advance w a b n)) : Derives Γ (result w K L a b e f n v) := by
  let B := FormulaCodeRecursiveSyntax.singleCaseBody tag advance w a b n
  let Δ := Context.add B (Context.image Formula.raise (Γ))
  apply FormulaCodeRecursiveSyntax.eliminate_single tag advance w a b n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have hd1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc R.castSucc S.castSucc T.castSucc U.castSucc K.castSucc L.castSucc r.castSucc s.castSucc t.castSucc u.castSucc g.castSucc h.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFormulaComposeDiagrams.diagrams_rename]) (under hd B)
  have he1 : Derives Δ (earlier w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he B)
  have h11 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under h1 B)
  have h21 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc T.castSucc U.castSucc c.castSucc d.castSucc e.castSucc f.castSucc q.castSucc v.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under h2 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxFormulaComposeLogical.single (ZFContext.under hZ B) tag advance valid w.castSucc R.castSucc S.castSucc T.castSucc U.castSucc K.castSucc L.castSucc r.castSucc s.castSucc t.castSucc u.castSucc g.castSucc h.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc n.castSucc q.castSucc v.castSucc (Fin.last m) hw1 hd1 he1 (.conjL (.conjR hB)) h11 h21 (.conjL hB)
  exact of_eq (by simp only [Formula.raise, result_rename]) ho

theorem binary_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hc : Derives Γ (FormulaCodeRecursiveSyntax.binaryCase kind w a b n)) : Derives Γ (result w K L a b e f n v) := by
  let B := FormulaCodeRecursiveSyntax.binaryCaseBody kind w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply FormulaCodeRecursiveSyntax.eliminate_binary kind w a b n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hd2 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFormulaComposeDiagrams.diagrams_rename]) (SyntaxRenameBinders.under_2 hd B)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxRenameBinders.under_2 he B)
  have h12 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 h1 B)
  have h22 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 h2 B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxFormulaComposeLogical.binary (SyntaxRenameBinders.zf_under_2 hZ B) kind w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hd2 he2 (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB))) h12 h22 (.conjL hB)
  exact of_eq (by simp only [Formula.raise, result_rename]) ho

theorem from_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L r s t u g h a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ (result w K L a b e f n v) := by
  have hrule := FormulaCodeRecursive.recursive_iff hZ w n a b hw
  have hcases : Derives Γ ((FormulaCodeRecursiveSyntax.allCases w n a b).imp (result w K L a b e f n v)) := by
    apply FormulaCodeCaseLogic.all_imp w n a b (result w K L a b e f n v)
    · apply Derives.impI
      exact SyntaxFormulaComposeAtoms.from_atomic (ZFContext.add hZ _) w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl,rfl⟩) w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 0 w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 1 w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 2 w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case (ZFContext.add hZ _) 3 w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w R S T U K L r s t u g h a b c d e f n q v (add hw _) (add hd _) (add he _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl))
  exact .impE hcases (.conjR (.impE (.conjL hrule) hc))

theorem at_diagrams {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L r s t u g h a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f)) (he : Derives Γ (earlier w n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v)) :
    Derives Γ (result w K L a b e f n v) :=
  from_code hZ w R S T U K L r s t u g h a b c d e f n q v hw hd he h1 h2 (.conjL (SyntaxRenameOutput.input_of_renamed hZ w R S a b c d n q hw h1))

theorem from_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n R S T U K L a b c d e f q v : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hb : Derives Γ (SyntaxComposeCodeSyntax.coded w a c e R T K)) (hf : Derives Γ (SyntaxComposeCodeSyntax.coded w b d f S U L))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v)) :
    Derives Γ (result w K L a b e f n v) := by
  let B := SyntaxComposeCodeSyntax.body w a c e R T K
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply SyntaxComposeCodeSyntax.eliminate_code w a c e R T K _ hb
  have hf3 : Derives Ξ (SyntaxComposeCodeSyntax.coded w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxComposeCodeSyntax.coded_rename]) (SyntaxAtomLogic.under_three hf B)
  let D := SyntaxComposeCodeSyntax.body w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Ξ)))
  apply SyntaxComposeCodeSyntax.eliminate_code w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc _ hf3
  have hZ6 := SyntaxAtomLogic.zf_under_three (SyntaxAtomLogic.zf_under_three hZ B) D
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three (SyntaxAtomLogic.under_three hw B) D)
  have he6 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxAtomLogic.under_three (SyntaxAtomLogic.under_three he B) D)
  have h16 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxAtomLogic.under_three (SyntaxAtomLogic.under_three h1 B) D)
  have h26 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxAtomLogic.under_three (SyntaxAtomLogic.under_three h2 B) D)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hB6 : Derives Δ ((SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj ((SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj ((SyntaxComposeSyntax.composed w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc).conj (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)))) := of_eq (by simp only [B, SyntaxComposeCodeSyntax.body, Formula.raise, Formula.rename, SyntaxMapCodeSyntax.encoded_rename, SyntaxComposeSyntax.composed_rename]) (SyntaxAtomLogic.under_three hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hd6 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+5)) a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := .conjI (.conjL (.conjR (.conjR hB6))) (.conjI (.conjL (.conjR (.conjR hD))) (.conjI (.conjL hB6) (.conjI (.conjL hD) (.conjI (.conjL (.conjR hB6)) (.conjI (.conjL (.conjR hD)) (.conjI (.conjR (.conjR (.conjR hB6))) (.conjR (.conjR (.conjR hD)))))))))
  have ho := at_diagrams hZ6 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+5)) a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw6 hd6 he6 h16 h26
  exact of_eq (by simp only [Formula.raise, result_rename]) ho

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+9)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+10)).castSucc.castSucc.castSucc (Fin.last (m+11)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+12)).castSucc (Fin.last (m+13))
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))))))))))
  have hZ14 := SyntaxFormulaComposeBinders.zf_under_14 hZ I
  have hw14 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxFormulaComposeBinders.under_14 hw I)
  have he14 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxFormulaComposeBinders.under_14 he I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  exact from_codes hZ14 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+7)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+9)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+10)).castSucc.castSucc.castSucc (Fin.last (m+11)).castSucc.castSucc (Fin.last (m+12)).castSucc (Fin.last (m+13)) hw14 he14 (.conjL hI) (.conjL (.conjR hI)) (.conjL (.conjR (.conjR hI))) (.conjR (.conjR (.conjR hI)))
end PPAC.Migration.Internal.SyntaxFormulaComposePoint
