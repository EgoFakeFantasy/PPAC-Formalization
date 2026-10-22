import PPAC.Migration.Internal.SyntaxFormulaFreeSubstOutput
import PPAC.Migration.Internal.SyntaxIdentityUnique

/-! 原项列表参数的全公式free替换实际唯一性及精确输入，所有实际码见证内部对齐。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaFreeSubstSyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeSubstSyntax (codeConversion codeConversion_rename)
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q R S : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (identityCode w b R))
    (hS : Derives Γ (codeConversion w a c L S)) (hq : Derives Γ (substituted w b a c L n q)) :
    Derives Γ (renamed w R S b a b c n q) := by
  let H := body w b a c L n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_substituted w b a c L n q _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc b.castSucc.castSucc R.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, identityCode_rename]) (SyntaxRenameBinders.under_2 hR H)
  have hs2 : Derives Δ (codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, codeConversion_rename]) (SyntaxRenameBinders.under_2 hS H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have er := SyntaxIdentityUnique.code_unique hZ2 _ _ _ _ hw2 (.conjL hH) hr2
  have es := SyntaxFreeSubstCodeUnique.map_unique hZ2 _ _ _ _ _ _ hw2 (.conjL (.conjR hH)) hs2
  have ho := SyntaxRenameJudgmentSubst.subst_r _ _ _ _ _ _ _ _ _ _ er (.conjR (.conjR hH))
  have hp := SyntaxWeakenFreeSyntax.renamed_subst_s _ _ _ _ _ _ _ _ _ _ es ho
  exact of_eq (by simp only [Formula.raise, renamed_rename]) hp

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q R S : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (identityCode w b R))
    (hS : Derives Γ (codeConversion w a c L S)) :
    Derives Γ ((substituted w b a c L n q).iff (renamed w R S b a b c n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_codes (ZFContext.add hZ _) w b a c L n q R S (add hw _) (add hR _) (add hS _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_substituted w b a c L n q R S (add hR _) (add hS _) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w b a c L n q))
    (hv : Derives Γ (substituted w b a c L n v)) : Derives Γ (.equal q v) := by
  let H := body w b a c L n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_substituted w b a c L n q _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hv2 : Derives Δ (substituted w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, substituted_rename]) (SyntaxRenameBinders.under_2 hv H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hr := at_codes hZ2 _ _ _ _ _ _ _ _ _ hw2 (.conjL hH) (.conjL (.conjR hH)) hv2
  exact SyntaxRenameOutputInduction.unique hZ2 _ _ _ _ _ _ _ _ _ _ hw2 (.conjR (.conjR hH)) hr

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w b a c L n q)) :
    Derives Γ (uniqueOutput w b a c L n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc q.castSucc) :=
    of_eq (substituted_rename w b a c L n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) _ _ _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hq1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w b a c L n)) : Derives Γ (fiber w b a c L n) := by
  let Q := substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxFormulaFreeSubstOutput.exists_output hZ w b a c L n hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := unique_output (ZFContext.under hZ Q) _ _ _ _ _ _ _ hw1 hQ
  have ho := intro_fiber w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w b a c L n Fin.castSucc).symm ho

theorem input_of_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (existsOutput w b a c L n)) : Derives Γ (input w b a c L n) := by
  let Q := substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have ho := SyntaxFormulaFreeSubstOutput.input_of_substituted (ZFContext.under hZ Q) _ _ _ _ _ _ _ hw1 (Derives.hyp (Or.inl rfl) : Derives Δ Q)
  exact of_eq (input_rename w b a c L n Fin.castSucc).symm ho

theorem exists_of_fiber {m} {Γ : Context m} (w b a c L n : Fin m)
    (hf : Derives Γ (fiber w b a c L n)) : Derives Γ (existsOutput w b a c L n) := by
  let H := (substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hf
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := intro_exists w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) (.conjL hH)
  exact of_eq (existsOutput_rename w b a c L n Fin.castSucc).symm ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsOutput w b a c L n).iff (input w b a c L n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists (ZFContext.add hZ _) w b a c L n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxFormulaFreeSubstOutput.exists_output (ZFContext.add hZ _) w b a c L n (add hw _) (.hyp (Or.inl rfl))

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w b a c L n).iff (input w b a c L n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists (ZFContext.add hZ _) w b a c L n (add hw _)
      (exists_of_fiber w b a c L n (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w b a c L n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxFormulaFreeSubstUnique
