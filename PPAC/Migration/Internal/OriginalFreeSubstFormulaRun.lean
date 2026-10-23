import PPAC.Migration.Internal.OriginalFormulaCorrectnessInduction
import PPAC.Migration.Internal.EmptyBoundFreeInputs
import PPAC.Migration.Internal.FreeSubstProgramValue

/-! 原mode3整条公式运行与实际自由替换特化的全内部双条件；码表在对象存在量词内取得。 -/
namespace PPAC.Migration.Internal.OriginalFreeSubstFormulaRun
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth b a c L n q I J R : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b I))
    (hJ : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w a c L J))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R b b c)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff
      (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)) := by
  have hf := OriginalOperationFrameRules.from_replace w mode depth L b a c I J R L hm hd hI hJ hR
  have hr := OriginalFormulaCorrectnessInduction.run_iff_execution hZ true w n mode depth L b a c I J R L q hw hf hn
  have hb := Derives.conjL (.conjR (FormulaCodeProperties.guards w n b a hn))
  have he := FreeSubstImageCode.same_code hZ w a b c L J hw hb hJ
  have hi := IndexFormulaRenameBridge.program_iff hZ w I J R L b a b c n q hw (.conjI hR he)
  have hs := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q I J hw hI hJ
  exact iff_trans hr (iff_trans hi (.conjI (.conjR hs) (.conjL hs)))

theorem from_list_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth b a c L n q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hL : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)) := by
  have hb := Derives.conjL (.conjR (FormulaCodeProperties.guards w n b a hn))
  let B0 := SyntaxIdentityMapSyntax.identityCode w.castSucc b.castSucc (Fin.last m)
  let Γ1 := Context.add B0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := B0) (SyntaxIdentityCode.exists_code hZ w b hw hb)
  have hZ1 := ZFContext.under hZ B0
  have hI : Derives Γ1 B0 := .hyp (Or.inl rfl)
  have hw1 : Derives Γ1 (omega (old 1 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (under hw B0)
  have hm1 : Derives Γ1 (SyntaxNumeralSyntax.numeral 3 (old 1 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (under hm B0)
  have hd1 : Derives Γ1 (OriginalTermTraceSyntax.metadata (old 1 w) (old 1 depth) (old 1 L)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (under hd B0)
  have hn1 : Derives Γ1 (FormulaCodeSyntax.formulaCode (old 1 w) (old 1 n) (old 1 b) (old 1 a)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (under hn B0)
  have hL1 : Derives Γ1 (SyntaxFreeSubstSyntax.termList (old 1 w) (old 1 a) (old 1 c) (old 1 L)) := of_eq (by simp only [Formula.raise, SyntaxFreeSubstSyntax.termList_rename, old]) (under hL B0)
  let B1 := SyntaxFreeSubstSyntax.codeConversion (old 2 w) (old 2 a) (old 2 c) (old 2 L) (Fin.last (m+1))
  let Γ2 := Context.add B1 (Context.image Formula.raise Γ1)
  apply Derives.exE (p := B1) (SyntaxFreeSubstCode.from_list hZ1 (old 1 w) (old 1 a) (old 1 c) (old 1 L) hw1 hL1)
  have hZ2 := ZFContext.under hZ1 B1
  have hJ : Derives Γ2 B1 := .hyp (Or.inl rfl)
  have hI2 : Derives Γ2 (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 b) (Fin.last m).castSucc) := of_eq (by simp only [B0, Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename, old]) (under hI B1)
  have hw2 : Derives Γ2 (omega (old 2 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (under hw1 B1)
  have hm2 : Derives Γ2 (SyntaxNumeralSyntax.numeral 3 (old 2 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (under hm1 B1)
  have hd2 : Derives Γ2 (OriginalTermTraceSyntax.metadata (old 2 w) (old 2 depth) (old 2 L)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (under hd1 B1)
  have hn2 : Derives Γ2 (FormulaCodeSyntax.formulaCode (old 2 w) (old 2 n) (old 2 b) (old 2 a)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (under hn1 B1)
  have hc2 := Derives.conjR (SyntaxMapCodeDecode.contexts (old 2 w) (old 2 a) (old 2 c) (Fin.last (m+1))
    (SyntaxFreeSubstCode.map_of_conversion (old 2 w) (old 2 a) (old 2 c) (old 2 L) (Fin.last (m+1)) hJ))
  let B2 := IndexTermImageCodeSyntax.converted true (old 3 w) (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (old 3 b) (old 3 b) (old 3 c)
  let Γ3 := Context.add B2 (Context.image Formula.raise Γ2)
  apply Derives.exE (p := B2) (FreeSubstImageCode.identity_image_exists hZ2 (old 2 w) (old 2 b) (old 2 c) (Fin.last m).castSucc hw2 hc2 hI2)
  have hZ3 := ZFContext.under hZ2 B2
  have hR : Derives Γ3 B2 := .hyp (Or.inl rfl)
  have hI3 : Derives Γ3 (SyntaxIdentityMapSyntax.identityCode (old 3 w) (old 3 b) (Fin.last m).castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename, old]) (under hI2 B2)
  have hJ3 : Derives Γ3 (SyntaxFreeSubstSyntax.codeConversion (old 3 w) (old 3 a) (old 3 c) (old 3 L) (Fin.last (m+1)).castSucc) := of_eq (by simp only [B1, Formula.raise, SyntaxFreeSubstSyntax.codeConversion_rename, old]) (under hJ B2)
  have hw3 : Derives Γ3 (omega (old 3 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (under hw2 B2)
  have hm3 : Derives Γ3 (SyntaxNumeralSyntax.numeral 3 (old 3 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (under hm2 B2)
  have hd3 : Derives Γ3 (OriginalTermTraceSyntax.metadata (old 3 w) (old 3 depth) (old 3 L)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (under hd2 B2)
  have hn3 : Derives Γ3 (FormulaCodeSyntax.formulaCode (old 3 w) (old 3 n) (old 3 b) (old 3 a)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (under hn2 B2)
  have ht := at_codes_iff hZ3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 b) (old 3 a) (old 3 c) (old 3 L) (old 3 n) (old 3 q) (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hm3 hd3 hn3 hI3 hJ3 hR
  exact of_eq (by simp only [Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, SyntaxFormulaFreeSubstSyntax.substituted_rename, old]) ht

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth b a c L n q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hL : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L))
    : Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FreeSubstProgramSyntax.executed w b a c L n q)) := by
  have hr := from_list_iff hZ w mode depth b a c L n q hw hm hd hn hL
  have hp := FreeSubstProgramCorrectness.executed_iff hZ w b a c L n q hw
  exact iff_trans hr (.conjI (.conjR hp) (.conjL hp))

theorem empty_bound_arguments_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth b a z c L n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hz : Derives Γ (empty z)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a z c L)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff
      (FreeSubstProgramSyntax.executed w b a c L n q)) :=
  program_iff hZ w mode depth b a c L n q hw hm hd hn (EmptyBoundFreeInputs.list_free hZ w a z c L hw hz hL)

theorem output_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth b a c L n q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hL : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 3 w mode depth L n q))
    : Derives Γ (FormulaCodeSyntax.formulaCode w q b c) := by
  exact FreeSubstProgramValue.target_type hZ w b a c L n q hw
    (.impE (.conjL (program_iff hZ w mode depth b a c L n q hw hm hd hn hL)) hr)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth b a c L n q v : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hL : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L))
    (hq : Derives Γ (OriginalTransformRowSyntax.run 3 w mode depth L n q))
    (hv : Derives Γ (OriginalTransformRowSyntax.run 3 w mode depth L n v)) : Derives Γ (.equal q v) :=
  FreeSubstProgramValue.unique hZ w b a c L n q v hw
    (.impE (.conjL (program_iff hZ w mode depth b a c L n q hw hm hd hn hL)) hq)
    (.impE (.conjL (program_iff hZ w mode depth b a c L n v hw hm hd hn hL)) hv)

theorem actual_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth b a c L n : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a))
    (hL : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L)) :
    Derives Γ (.ex (OriginalTransformRowSyntax.run 3 w.castSucc mode.castSucc depth.castSucc L.castSucc n.castSucc (Fin.last m))) := by
  let B := FreeSubstProgramValueSyntax.value w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (FreeSubstProgramValue.actual_fiber hZ w b a c L n hw (.conjI hn hL))
  have hw1 : Derives Δ (omega (old 1 w)) := of_eq (by simp only [Formula.raise, omega_rename, old]) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (old 1 mode)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, old]) (under hm B)
  have hd1 : Derives Δ (OriginalTermTraceSyntax.metadata (old 1 w) (old 1 depth) (old 1 L)) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename, old]) (under hd B)
  have hn1 : Derives Δ (FormulaCodeSyntax.formulaCode (old 1 w) (old 1 n) (old 1 b) (old 1 a)) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename, old]) (under hn B)
  have hL1 : Derives Δ (SyntaxFreeSubstSyntax.termList (old 1 w) (old 1 a) (old 1 c) (old 1 L)) := of_eq (by simp only [Formula.raise, SyntaxFreeSubstSyntax.termList_rename, old]) (under hL B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr := Derives.impE (.conjR (program_iff (ZFContext.under hZ B) w.castSucc mode.castSucc depth.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) hw1 hm1 hd1 hn1 hL1)) (.conjL hB)
  apply Derives.exI (Fin.last m)
  exact of_eq (by simp only [Formula.instantiate, OriginalTransformRowSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr

end PPAC.Migration.Internal.OriginalFreeSubstFormulaRun
