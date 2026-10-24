import PPAC.Migration.Internal.OriginalFormulaCorrectnessInduction
import PPAC.Migration.Internal.WeakenFreeProgramValue

/-! 原mode0完整公式运行与自由头槽弱化的全内部对应；实际四码表在对象EX中取得并消去。 -/
namespace PPAC.Migration.Internal.OriginalWeakenFormulaRun
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxTypeLocalTransfer (iff_trans)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth P a b B n q I J R S : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hE : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b a B)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (SyntaxWeakenFreeSyntax.weakened w a b B n q)) := by
  have hf := OriginalOperationFrameRules.from_weaken hZ w mode depth P a b B I J R S hw hm hd hI hJ (.conjL hE) (.conjR hE)
  have hr := OriginalFormulaCorrectnessInduction.run_iff_execution hZ false w n mode depth P a b B I J R S q hw hf hn
  have hi := IndexFormulaRenameBridge.program_iff hZ w I J R S a b a B n q hw hE
  have hs := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q I J hw hI hJ
  exact iff_trans hr (iff_trans hi (.conjI (.conjR hs) (.conjL hs)))

theorem typed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth P a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hB : Derives Γ (successor B b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (SyntaxWeakenFreeSyntax.weakened w a b B n q)) := by
  have ha := Derives.conjL (.conjR (FormulaCodeProperties.guards w n a b hn))
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w n a b hn))
  let E0 := SyntaxIdentityMapSyntax.identityCode (old 1 w) (old 1 a) (Fin.last m)
  let Γ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) (SyntaxIdentityCode.exists_code hZ w a hw ha)
  have hZ1 := ZFContext.under hZ E0
  have hI : Derives Γ1 E0 := .hyp (Or.inl rfl)
  have hw1 : Derives Γ1 (omega (old 1 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (under hw E0)
  have hm1 : Derives Γ1 (SyntaxNumeralSyntax.numeral 0 (old 1 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (under hm E0)
  have hd1 : Derives Γ1 (OriginalTermTraceSyntax.metadata (old 1 w) (old 1 depth) (old 1 P)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (under hd E0)
  have hn1 : Derives Γ1 (FormulaCodeSyntax.formulaCode (old 1 w) (old 1 n) (old 1 a) (old 1 b)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (under hn E0)
  have hB1 : Derives Γ1 (successor (old 1 B) (old 1 b)) := of_eq (by simp only [Formula.raise, successor_rename, old]) (under hB E0)
  have hb1 : Derives Γ1 (Formula.mem (old 1 b) (old 1 w)) := of_eq (by simp only [Formula.raise, Formula.rename, old]) (under hb E0)
  let E1 := SyntaxFreeShiftSyntax.shiftCode (old 2 w) (old 2 b) (old 2 B) (Fin.last (m+1))
  let Γ2 := Context.add E1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := E1) (SyntaxFreeShiftCode.exists_code hZ1 (old 1 w) (old 1 b) (old 1 B) hw1 hb1 hB1)
  have hZ2 := ZFContext.under hZ1 E1
  have hJ : Derives Γ2 E1 := .hyp (Or.inl rfl)
  have hI2 : Derives Γ2 (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 a) (Fin.last m).castSucc) :=
    of_eq (by simp only [E0, Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename, old]) (under hI E1)
  have hw2 : Derives Γ2 (omega (old 2 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (under hw1 E1)
  have hm2 : Derives Γ2 (SyntaxNumeralSyntax.numeral 0 (old 2 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (under hm1 E1)
  have hd2 : Derives Γ2 (OriginalTermTraceSyntax.metadata (old 2 w) (old 2 depth) (old 2 P)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (under hd1 E1)
  have hn2 : Derives Γ2 (FormulaCodeSyntax.formulaCode (old 2 w) (old 2 n) (old 2 a) (old 2 b)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (under hn1 E1)
  let E2 := IndexTermImageCodeSyntax.environment (old 4 w) (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    (old 4 a) (old 4 b) (old 4 a) (old 4 B)
  let Γ4 := Context.add E2 (Context.image Formula.raise (Context.image Formula.raise Γ2))
  apply SyntaxRenameBinders.eliminate_2 E2 _ (IndexTermImageEnvironment.exists_environment hZ2 (old 2 w)
    (Fin.last m).castSucc (Fin.last (m+1)) (old 2 a) (old 2 b) (old 2 a) (old 2 B) hw2
    (SyntaxIdentityCode.map_code _ _ _ hI2) (SyntaxFreeShiftCode.map_code _ _ _ _ hJ))
  have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 E2
  have hE : Derives Γ4 E2 := .hyp (Or.inl rfl)
  have hI4 : Derives Γ4 (SyntaxIdentityMapSyntax.identityCode (old 4 w) (old 4 a) (Fin.last m).castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename, old]) (SyntaxRenameBinders.under_2 hI2 E2)
  have hJ4 : Derives Γ4 (SyntaxFreeShiftSyntax.shiftCode (old 4 w) (old 4 b) (old 4 B) (Fin.last (m+1)).castSucc.castSucc) :=
    of_eq (by simp only [E1, Formula.raise, SyntaxFreeShiftSyntax.shiftCode_rename, old]) (SyntaxRenameBinders.under_2 hJ E2)
  have hw4 : Derives Γ4 (omega (old 4 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (SyntaxRenameBinders.under_2 hw2 E2)
  have hm4 : Derives Γ4 (SyntaxNumeralSyntax.numeral 0 (old 4 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (SyntaxRenameBinders.under_2 hm2 E2)
  have hd4 : Derives Γ4 (OriginalTermTraceSyntax.metadata (old 4 w) (old 4 depth) (old 4 P)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (SyntaxRenameBinders.under_2 hd2 E2)
  have hn4 : Derives Γ4 (FormulaCodeSyntax.formulaCode (old 4 w) (old 4 n) (old 4 a) (old 4 b)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (SyntaxRenameBinders.under_2 hn2 E2)
  have ht := at_codes_iff hZ4 (old 4 w) (old 4 mode) (old 4 depth) (old 4 P) (old 4 a) (old 4 b) (old 4 B) (old 4 n) (old 4 q)
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 hm4 hd4 hn4 hI4 hJ4 hE
  exact of_eq (by simp only [Formula.iff, Formula.rename, Formula.raise, OriginalTransformRowSyntax.run_rename, SyntaxWeakenFreeSyntax.weakened_rename, old]) ht

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth P a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hB : Derives Γ (successor B b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (WeakenFreeProgramSyntax.executed w a b B n q)) :=
  iff_trans (typed_iff hZ w mode depth P a b B n q hw hm hd hn hB)
    (let he := WeakenFreeProgramCorrectness.executed_iff hZ w a b B n q hw; .conjI (.conjR he) (.conjL he))

theorem output_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth P a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth P))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) (hB : Derives Γ (successor B b))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode depth P n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q a B) :=
  WeakenFreeProgramValue.target_type hZ w a b B n q hw
    (.impE (.conjL (program_iff hZ w mode depth P a b B n q hw hm hd hn hB)) hr)

end PPAC.Migration.Internal.OriginalWeakenFormulaRun
