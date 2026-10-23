import PPAC.Migration.Internal.OriginalFormulaInductionSyntax

/-! 由实际独立程序递归图和严格有类型子码的对象归纳假设，实际构造历史比较与内部历史见证。 -/
namespace PPAC.Migration.Internal.OriginalHistoryFromInduction
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter h R S a b c d n : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hi : Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n)) :
    Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let G := (Formula.mem (slot 2 0) (old 2 n)).conj (FormulaCodeSyntax.formulaCode (old 2 w) (slot 2 0) (old 2 a) (old 2 b))
  let Δ := Context.add G (raisedContext 2 Γ)
  have hZ1 : ZFContext.Evidence Δ := HornBinderRules.zf_body 2 hZ G
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw G)
  have hn1 : Derives Δ (OrdinalSyntax.ordinal (old 2 n)) := of_eq (OrdinalSyntax.ordinal_rename n (old 2)) (HornBinderRules.under_body 2 hn G)
  have hg1 : Derives Δ (FormulaTransformRecursionSyntax.graph (old 2 w) (old 2 h) (old 2 n)) := of_eq (FormulaTransformRecursionSyntax.graph_rename w h n (old 2)) (HornBinderRules.under_body 2 hg G)
  have hi1 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n)) := of_eq (OriginalFormulaInductionSyntax.prefixIH_rename w mode depth parameter R S a b c d n (old 2)) (HornBinderRules.under_body 2 hi G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hRun := OriginalFormulaInductionSyntax.prefixIH_at (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (slot 2 0) (slot 2 1) hi1 (.conjL hG) (.conjR hG)
  have hRead := OriginalHistoryRead.read_iff_executed hZ1 (old 2 w) (old 2 h) (old 2 n) (slot 2 0) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (slot 2 1) hw1 hn1 (.conjL hG) hg1
  exact SyntaxTypeLocalTransfer.iff_trans hRun (.conjI (.conjR hRead) (.conjL hRead))

theorem exists_agreed_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S a b c d n : Fin m) (hw : Derives Γ (omega w))
    (hF : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hi : Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n)) :
    Derives Γ (OriginalFormulaInductionSyntax.agreedHistory w mode depth parameter R S a b c d n) := by
  have hn := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hF))
  let B := FormulaTransformRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (FormulaTransformRecursionCorrectness.graph_exists hZ w n hw hn)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (OrdinalSyntax.ordinal n.castSucc) := of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under hn B)
  have hi1 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := of_eq (OriginalFormulaInductionSyntax.prefixIH_rename w mode depth parameter R S a b c d n Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := from_graph (ZFContext.under hZ B) w.castSucc mode.castSucc depth.castSucc parameter.castSucc (Fin.last m) R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc hw1 hn1 hB hi1
  have he := OriginalFormulaInductionSyntax.intro_agreedHistory w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hB ha
  exact of_eq (OriginalFormulaInductionSyntax.agreedHistory_rename w mode depth parameter R S a b c d n Fin.castSucc).symm he

end PPAC.Migration.Internal.OriginalHistoryFromInduction
