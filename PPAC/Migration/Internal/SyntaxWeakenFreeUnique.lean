import PPAC.Migration.Internal.SyntaxWeakenFreeOutput
import PPAC.Migration.Internal.SyntaxIdentityUnique

/-! 任意内部公式码的弱化唯一性；所有图码见证在对象量词内消去。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxWeakenFreeSyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeShiftSyntax (shiftCode shiftCode_rename)
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q R S : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (identityCode w a R))
    (hS : Derives Γ (shiftCode w b B S)) (hq : Derives Γ (weakened w a b B n q)) :
    Derives Γ (renamed w R S a b a B n q) := by
  let H := body w a b B n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_weakened w a b B n q _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc a.castSucc.castSucc R.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, identityCode_rename]) (SyntaxRenameBinders.under_2 hR H)
  have hs2 : Derives Δ (shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc S.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, shiftCode_rename]) (SyntaxRenameBinders.under_2 hS H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have er := SyntaxIdentityUnique.code_unique hZ2 _ _ _ _ hw2 (.conjL hH) hr2
  have es := SyntaxFreeShiftCode.unique hZ2 _ _ _ _ _ hw2 (.conjL (.conjR hH)) hs2
  have ho := SyntaxRenameJudgmentSubst.subst_r _ _ _ _ _ _ _ _ _ _ er (.conjR (.conjR hH))
  have hp := renamed_subst_s _ _ _ _ _ _ _ _ _ _ es ho
  exact of_eq (by simp only [Formula.raise, renamed_rename]) hp

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q R S : Fin m)
    (hw : Derives Γ (omega w)) (hR : Derives Γ (identityCode w a R))
    (hS : Derives Γ (shiftCode w b B S)) :
    Derives Γ ((weakened w a b B n q).iff (renamed w R S a b a B n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_codes (ZFContext.add hZ _) w a b B n q R S (add hw _) (add hR _) (add hS _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_weakened w a b B n q R S (add hR _) (add hS _) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (weakened w a b B n q))
    (hv : Derives Γ (weakened w a b B n v)) : Derives Γ (.equal q v) := by
  let H := body w a b B n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_weakened w a b B n q _ hq
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hv2 : Derives Δ (weakened w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, weakened_rename]) (SyntaxRenameBinders.under_2 hv H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hr := at_codes hZ2 _ _ _ _ _ _ _ _ hw2 (.conjL hH) (.conjL (.conjR hH)) hv2
  exact SyntaxRenameOutputInduction.unique hZ2 _ _ _ _ _ _ _ _ _ _ hw2 (.conjR (.conjR hH)) hr

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (weakened w a b B n q)) :
    Derives Γ (uniqueOutput w a b B n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc q.castSucc) :=
    of_eq (weakened_rename w a b B n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) _ _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl)) hq1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b B n)) : Derives Γ (fiber w a b B n) := by
  let Q := weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxWeakenFreeOutput.exists_output hZ w a b B n hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := unique_output (ZFContext.under hZ Q) _ _ _ _ _ _ hw1 hQ
  have ho := intro_fiber w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (fiber_rename w a b B n Fin.castSucc).symm ho

theorem input_of_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (existsOutput w a b B n)) : Derives Γ (input w a b B n) := by
  let Q := weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have ho := SyntaxWeakenFreeOutput.input_of_weakened (ZFContext.under hZ Q) _ _ _ _ _ _ hw1 (Derives.hyp (Or.inl rfl) : Derives Δ Q)
  exact of_eq (input_rename w a b B n Fin.castSucc).symm ho

theorem exists_of_fiber {m} {Γ : Context m} (w a b B n : Fin m)
    (hf : Derives Γ (fiber w a b B n)) : Derives Γ (existsOutput w a b B n) := by
  let H := (weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hf
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := intro_exists w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m) (.conjL hH)
  exact of_eq (existsOutput_rename w a b B n Fin.castSucc).symm ho

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsOutput w a b B n).iff (input w a b B n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists (ZFContext.add hZ _) w a b B n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxWeakenFreeOutput.exists_output (ZFContext.add hZ _) w a b B n (add hw _) (.hyp (Or.inl rfl))

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w a b B n).iff (input w a b B n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists (ZFContext.add hZ _) w a b B n (add hw _)
      (exists_of_fiber w a b B n (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w a b B n (add hw _) (.hyp (Or.inl rfl))

theorem actual_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n a b)) : Derives Γ (actualState w a b n) := by
  have he := InsertExistence.exists_insert b b (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let H := successor (Fin.last m) b.castSucc
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hc1 : Derives Δ (formulaCode w.castSucc n.castSucc a.castSucc b.castSucc) :=
    of_eq (formulaCode_rename w n a b Fin.castSucc) (under hc H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hf := actual_fiber (ZFContext.under hZ H) _ _ _ _ _ hw1 (.conjI hc1 hH)
  have ho : Derives Δ (actualState w.castSucc a.castSucc b.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [H, Formula.instantiate, Formula.rename, successor_rename,
      fiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hH hf)
  exact of_eq (actualState_rename w a b n Fin.castSucc).symm ho

end PPAC.Migration.Internal.SyntaxWeakenFreeUnique
