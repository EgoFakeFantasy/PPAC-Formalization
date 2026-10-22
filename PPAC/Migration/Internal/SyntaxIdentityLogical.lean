import PPAC.Migration.Internal.SyntaxIdentityAtomic

/-! 恒等码下逻辑构造自重命名；量词体使用实际后继与实际提升恒等码。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityLogical
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameIdentitySyntax
open SyntaxIdentityMapSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b n x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (singleCode 4 w x n)) (hx : Derives Γ (.mem x n))
    (ht : Derives Γ (formulaCode w x a b)) : Derives Γ (self w R S a b n) :=
  .impE (.conjR (SyntaxRenameCodeFields.single_iff hZ 4 false (Or.inl ⟨rfl,rfl⟩) w R S a b a b n n x x hw
    (SyntaxIdentityCode.map_code w a R hr) (SyntaxIdentityCode.map_code w b S hs) hc hc)) (child w n x R S a b he hx ht hr hs)

theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w R S a b n x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (singleCode (quantifierTag universal) w x n)) (hx : Derives Γ (.mem x n))
    (ht : Derives Γ (advancedCode w x a b)) : Derives Γ (self w R S a b n) := by
  let U := (successor (Fin.last m) a.castSucc).conj (formulaCode w.castSucc x.castSucc (Fin.last m) b.castSucc)
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) ht
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ U
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw U)
  have he1 : Derives Ξ (earlier w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he U)
  have hr1 : Derives Ξ (identityCode w.castSucc a.castSucc R.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under hr U)
  have hs1 : Derives Ξ (identityCode w.castSucc b.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under hs U)
  have hc1 : Derives Ξ (singleCode (quantifierTag universal) w.castSucc x.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, singleCode_rename]) (under hc U)
  have hx1 : Derives Ξ (Formula.mem x.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hx U)
  have hl := SyntaxMapLift.exists_code hZ1 w.castSucc a.castSucc a.castSucc R.castSucc (Fin.last m) (Fin.last m) hw1
    (SyntaxIdentityCode.map_code _ _ _ hr1) (.conjL hU) (.conjL hU)
  let L := SyntaxMapLiftSyntax.codedLift w.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add L (Context.image Formula.raise Ξ)
  apply Derives.exE (p := L) hl
  have hZ2 := ZFContext.under hZ1 L
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw1 L)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under he1 L)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under hr1 L)
  have hs2 : Derives Δ (identityCode w.castSucc.castSucc b.castSucc.castSucc S.castSucc.castSucc) := of_eq (by simp only [Formula.raise, identityCode_rename]) (under hs1 L)
  have hc2 : Derives Δ (singleCode (quantifierTag universal) w.castSucc.castSucc x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, singleCode_rename]) (under hc1 L)
  have hx2 : Derives Δ (Formula.mem x.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hx1 L)
  have hU2 : Derives Δ ((successor (Fin.last m).castSucc a.castSucc.castSucc).conj (formulaCode w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc)) :=
    of_eq (by simp only [U, Formula.raise, Formula.rename, successor_rename, formulaCode_rename]) (under hU L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hid := SyntaxIdentityLift.code_same_successor hZ2 w.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hr2 hL
  have hb := child w.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1)) S.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc he2 hx2 (.conjR hU2) hid hs2
  have ho := Derives.impE (.conjR (SyntaxRenameCodeFields.quantified_at_lift hZ2 universal w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (SyntaxIdentityCode.map_code _ _ _ hs2) hL hc2 hc2)) hb
  exact of_eq (by simp only [Formula.raise, self, SyntaxRenameJudgmentSyntax.renamed_rename]) ho

theorem single_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b n x : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (singleCode tag w x n)) (hx : Derives Γ (.mem x n))
    (ht : Derives Γ (stepCheck advance w x a b)) : Derives Γ (self w R S a b n) := by
  rcases valid with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact negation hZ w R S a b n x hw he hr hs hc hx ht
  · exact quantified hZ true w R S a b n x hw he hr hs hc hx ht
  · exact quantified hZ false w R S a b n x hw he hr hs hc hx ht

theorem binary_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w R S a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (identityCode w b S))
    (hc : Derives Γ (binaryCode kind w x y n)) (hx : Derives Γ (.mem x n)) (hy : Derives Γ (.mem y n))
    (ht : Derives Γ ((formulaCode w x a b).conj (formulaCode w y a b))) : Derives Γ (self w R S a b n) :=
  .impE (.conjR (SyntaxRenameCodeFields.binary_iff hZ kind w R S a b a b n n x y x y hw
    (SyntaxIdentityCode.map_code _ _ _ hr) (SyntaxIdentityCode.map_code _ _ _ hs) hc hc))
    (.conjI (child w n x R S a b he hx (.conjL ht) hr hs) (child w n y R S a b he hy (.conjR ht) hr hs))
end PPAC.Migration.Internal.SyntaxIdentityLogical
