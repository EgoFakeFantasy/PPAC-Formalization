import PPAC.Migration.Internal.SyntaxFormulaComposeLogicalFields

/-! 七逻辑构造实际消去两阶段目标字段，不以外部字段数组或宿主AST复合替代对象见证。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeLogical
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaComposeSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true)) (w R S T U K L r s t u g h a b c d e f n q v x : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (he : Derives Γ (earlier w n)) (hx : Derives Γ (.mem x n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hn : Derives Γ (singleCode tag w x n)) : Derives Γ (result w K L a b e f n v) := by
  have ht1 := SyntaxRenameTargetFields.single hZ tag advance valid w R S r s a b c d n q x hw
    (SyntaxFormulaComposeDiagrams.encoded_r w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_s w R S T U K L r s t u g h a b c d e f hd) hn h1
  let B := singleCode tag w.castSucc (Fin.last m) q.castSucc
  let Ξ := Context.add B (Context.image Formula.raise (Γ))
  apply Derives.exE (p := B) ht1
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have hd1 : Derives Ξ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc R.castSucc S.castSucc T.castSucc U.castSucc K.castSucc L.castSucc r.castSucc s.castSucc t.castSucc u.castSucc g.castSucc h.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFormulaComposeDiagrams.diagrams_rename]) (under hd B)
  have he1 : Derives Ξ (earlier w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he B)
  have hx1 : Derives Ξ (Formula.mem x.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hx B)
  have h11 : Derives Ξ (SyntaxRenameJudgmentSyntax.renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under h1 B)
  have h21 : Derives Ξ (SyntaxRenameJudgmentSyntax.renamed w.castSucc T.castSucc U.castSucc c.castSucc d.castSucc e.castSucc f.castSucc q.castSucc v.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under h2 B)
  have hn1 : Derives Ξ (singleCode tag w.castSucc x.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, singleCode_rename]) (under hn B)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have ht2 := SyntaxRenameTargetFields.single hZ1 tag advance valid w.castSucc T.castSucc U.castSucc t.castSucc u.castSucc c.castSucc d.castSucc e.castSucc f.castSucc q.castSucc v.castSucc (Fin.last m) hw1 (SyntaxFormulaComposeDiagrams.encoded_t w.castSucc R.castSucc S.castSucc T.castSucc U.castSucc K.castSucc L.castSucc r.castSucc s.castSucc t.castSucc u.castSucc g.castSucc h.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc hd1) (SyntaxFormulaComposeDiagrams.encoded_u w.castSucc R.castSucc S.castSucc T.castSucc U.castSucc K.castSucc L.castSucc r.castSucc s.castSucc t.castSucc u.castSucc g.castSucc h.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc hd1) hB h21
  let D := singleCode tag w.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc
  let Δ := Context.add D (Context.image Formula.raise (Ξ))
  apply Derives.exE (p := D) ht2
  have hZ2 := ZFContext.under hZ1 D
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw1 D)
  have hd2 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFormulaComposeDiagrams.diagrams_rename]) (under hd1 D)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he1 D)
  have hx2 : Derives Δ (Formula.mem x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hx1 D)
  have h12 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under h11 D)
  have h22 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (under h21 D)
  have hn2 : Derives Δ (singleCode tag w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, singleCode_rename]) (under hn1 D)
  have hm2 : Derives Δ (singleCode tag w.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc) := of_eq (by simp only [B, Formula.raise, singleCode_rename]) (under hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := SyntaxFormulaComposeLogicalFields.single hZ2 tag advance valid w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hd2 he2 hx2 h12 h22 hn2 hm2 hD
  exact of_eq (by simp only [Formula.raise, result_rename]) ho

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (he : Derives Γ (earlier w n)) (hx : Derives Γ (.mem x n)) (hy : Derives Γ (.mem y n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hn : Derives Γ (binaryCode kind w x y n)) : Derives Γ (result w K L a b e f n v) := by
  have ht1 := SyntaxRenameTargetFields.binary hZ kind w R S r s a b c d n q x y hw
    (SyntaxFormulaComposeDiagrams.encoded_r w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_s w R S T U K L r s t u g h a b c d e f hd) hn h1
  let B := binaryCode kind w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) q.castSucc.castSucc
  let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply SyntaxRenameBinders.eliminate_2 B _ ht1
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hd2 : Derives Ξ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFormulaComposeDiagrams.diagrams_rename]) (SyntaxRenameBinders.under_2 hd B)
  have he2 : Derives Ξ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxRenameBinders.under_2 he B)
  have hx2 : Derives Ξ (Formula.mem x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hx B)
  have hy2 : Derives Ξ (Formula.mem y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hy B)
  have h12 : Derives Ξ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 h1 B)
  have h22 : Derives Ξ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 h2 B)
  have hn2 : Derives Ξ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hn B)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have ht2 := SyntaxRenameTargetFields.binary hZ2 kind w.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (SyntaxFormulaComposeDiagrams.encoded_t w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc hd2) (SyntaxFormulaComposeDiagrams.encoded_u w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc u.castSucc.castSucc g.castSucc.castSucc h.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc hd2) hB h22
  let D := binaryCode kind w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) v.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Ξ)))
  apply SyntaxRenameBinders.eliminate_2 D _ ht2
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 D
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 D)
  have hd4 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFormulaComposeDiagrams.diagrams_rename]) (SyntaxRenameBinders.under_2 hd2 D)
  have he4 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (SyntaxRenameBinders.under_2 he2 D)
  have hx4 : Derives Δ (Formula.mem x.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hx2 D)
  have hy4 : Derives Δ (Formula.mem y.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (SyntaxRenameBinders.under_2 hy2 D)
  have h14 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 h12 D)
  have h24 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxRenameJudgmentSyntax.renamed_rename]) (SyntaxRenameBinders.under_2 h22 D)
  have hn4 : Derives Δ (binaryCode kind w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hn2 D)
  have hm4 : Derives Δ (binaryCode kind w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [B, Formula.raise, binaryCode_rename]) (SyntaxRenameBinders.under_2 hB D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := SyntaxFormulaComposeLogicalFields.binary hZ4 kind w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc T.castSucc.castSucc.castSucc.castSucc U.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc L.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc u.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 hd4 he4 hx4 hy4 h14 h24 hn4 hm4 hD
  exact of_eq (by simp only [Formula.raise, result_rename]) ho

end PPAC.Migration.Internal.SyntaxFormulaComposeLogical
