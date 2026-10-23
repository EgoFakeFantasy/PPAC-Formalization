import PPAC.Migration.Internal.SyntaxCodedMixedTermExistence

/-! 原数值环境混合项替换的实际唯一性不依赖解码图见证。 -/
namespace PPAC.Migration.Internal.SyntaxCodedMixedTermUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxCodedMixedTermSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w R S a b c d n q))
    (hv : Derives Γ (substituted w R S a b c d n v)) : Derives Γ (.equal q v) := by
  let B := body w R S a b c d n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hv2 : Derives Δ (substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, substituted_rename]) (SyntaxRenameBinders.under_2 hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr := SyntaxCodedMixedTermGraphs.at_graphs hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hB) hv2
  exact SyntaxMixedTermUnique.unique hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc v.castSucc.castSucc hw2 (.conjR hB) hr

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w R S a b c d n q)) : Derives Γ (uniqueOutput w R S a b c d n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (substituted_rename w R S a b c d n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

end PPAC.Migration.Internal.SyntaxCodedMixedTermUnique
