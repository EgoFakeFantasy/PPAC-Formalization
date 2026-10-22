import PPAC.Migration.Internal.SyntaxRenameKnownFields

/-! 逻辑端点精确律消去两幅实际图见证；量词可精确实例化给定实际后继/提升码。 -/
namespace PPAC.Migration.Internal.SyntaxRenameCodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMapCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n q x X : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (mapCode w a c R)) (hs : Derives Γ (mapCode w b d S))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n)) (hd : Derives Γ (SyntaxLogicalSyntax.singleCode tag w X q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X)) := by
  let G := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hr
  have hs1 : Derives Ξ (mapCode w.castSucc b.castSucc d.castSucc S.castSucc) := of_eq (mapCode_rename w b d S Fin.castSucc) (under hs G)
  let H := encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hs1
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under (under hc G) H)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.singleCode tag w.castSucc.castSucc X.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.singleCode_rename]) (under (under hd G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) := of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hG H)
  have ho := SyntaxRenameKnownFields.single_iff hZ2 tag advance valid w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc X.castSucc.castSucc hw2 hr2 (.hyp (Or.inl rfl)) hc2 hd2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxRenameJudgmentSyntax.renamed_rename, SyntaxRenameRecursiveSyntax.check_rename]) ho

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hr : Derives Γ (mapCode w a c R)) (hs : Derives Γ (mapCode w b d S))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) (hd : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y))) := by
  let G := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc R.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hr
  have hs1 : Derives Ξ (mapCode w.castSucc b.castSucc d.castSucc S.castSucc) := of_eq (mapCode_rename w b d S Fin.castSucc) (under hs G)
  let H := encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) hs1
  have hZ2 := ZFContext.under (ZFContext.under hZ G) H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw G) H)
  have hc2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (under (under hc G) H)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc q.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (under (under hd G) H)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc) := of_eq (encoded_rename _ _ _ _ _ Fin.castSucc) (under hG H)
  have ho := SyntaxRenameKnownFields.binary_iff hZ2 kind w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc hw2 hr2 (.hyp (Or.inl rfl)) hc2 hd2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxRenameJudgmentSyntax.renamed_rename]) ho

theorem quantified_at_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w R S a b c d n q x X u v l : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (mapCode w b d S)) (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c R u v l))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hd : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff
      (SyntaxRenameJudgmentSyntax.renamed w l S u b v d x X)) := by
  have hr := SyntaxMapLiftFiber.input_code w a c R u v l hl
  have hp : Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff
      (SyntaxRenameRecursiveSyntax.advanced w x R S a b c d X)) := by
    cases universal
    · exact single_iff hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S a b c d n q x X hw hr hs hc hd
    · exact single_iff hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S a b c d n q x X hw hr hs hc hd
  exact SyntaxTypeLocalTransfer.iff_trans hp (SyntaxRenameAdvancedKnown.at_lift hZ w x R S a b c d X u v l hw hl)

end PPAC.Migration.Internal.SyntaxRenameCodeFields
