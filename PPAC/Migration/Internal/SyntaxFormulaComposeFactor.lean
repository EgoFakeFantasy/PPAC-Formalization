import PPAC.Migration.Internal.SyntaxFormulaComposeInduction

/-! 所有内部候选上的公式复合精确等价于存在实际中间公式码的两阶段判断。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeFactor
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaComposeSyntax
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def sequential {m} (w R S T U a b c d e f n v : Fin m) : Formula m := .ex
  ((renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (renamed w.castSucc T.castSucc U.castSucc c.castSucc d.castSucc e.castSucc f.castSucc (Fin.last m) v.castSucc))

theorem sequential_rename {m k} (w R S T U a b c d e f n v : Fin m) (ρ : Fin m → Fin k) :
    (sequential w R S T U a b c d e f n v).rename ρ = sequential (ρ w) (ρ R) (ρ S) (ρ T) (ρ U) (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) (ρ f) (ρ n) (ρ v) := by
  simp only [sequential, Formula.rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_sequential {m} {Γ : Context m} (w R S T U a b c d e f n v q : Fin m)
    (h1 : Derives Γ (renamed w R S a b c d n q)) (h2 : Derives Γ (renamed w T U c d e f q v)) : Derives Γ (sequential w R S T U a b c d e f n v) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI h1 h2)

theorem factor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L a b c d e f n v : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxComposeCodeSyntax.coded w a c e R T K)) (hf : Derives Γ (SyntaxComposeCodeSyntax.coded w b d f S U L))
    (hc : Derives Γ (result w K L a b e f n v)) : Derives Γ (sequential w R S T U a b c d e f n v) := by
  have ht := Derives.conjL (SyntaxRenameOutput.input_of_renamed hZ w K L a b e f n v hw hc)
  have hi := Derives.conjI ht (Derives.conjI (SyntaxComposeCodeReadback.first_code _ _ _ _ _ _ _ hb) (SyntaxComposeCodeReadback.first_code _ _ _ _ _ _ _ hf))
  let Q := renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxRenameOutputInduction.actual_exists hZ w R S a b c d n hw hi)
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw Q)
  have hb1 : Derives Ξ (SyntaxComposeCodeSyntax.coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc K.castSucc) := of_eq (SyntaxComposeCodeSyntax.coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hb Q)
  have hf1 : Derives Ξ (SyntaxComposeCodeSyntax.coded w.castSucc b.castSucc d.castSucc f.castSucc S.castSucc U.castSucc L.castSucc) := of_eq (SyntaxComposeCodeSyntax.coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hf Q)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have ht1 := SyntaxRenameJudgment.target_type _ _ _ _ _ _ _ _ _ hQ
  have hi1 := Derives.conjI ht1 (Derives.conjI (SyntaxComposeCodeReadback.second_code _ _ _ _ _ _ _ hb1) (SyntaxComposeCodeReadback.second_code _ _ _ _ _ _ _ hf1))
  let V := renamed w.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add V (Context.image Formula.raise Ξ)
  apply Derives.exE (p := V) (SyntaxRenameOutputInduction.actual_exists hZ1 w.castSucc T.castSucc U.castSucc c.castSucc d.castSucc e.castSucc f.castSucc (Fin.last m) hw1 hi1)
  have hZ2 := ZFContext.under hZ1 V
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 V)
  have hb2 : Derives Δ (SyntaxComposeCodeSyntax.coded w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc T.castSucc.castSucc K.castSucc.castSucc) := of_eq (SyntaxComposeCodeSyntax.coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hb1 V)
  have hf2 : Derives Δ (SyntaxComposeCodeSyntax.coded w.castSucc.castSucc b.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc S.castSucc.castSucc U.castSucc.castSucc L.castSucc.castSucc) := of_eq (SyntaxComposeCodeSyntax.coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hf1 V)
  have hc2 : Derives Δ (result w.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, result_rename]) (under (under hc Q) V)
  have hq2 : Derives Δ (renamed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [Q, Formula.raise, renamed_rename]) (under hQ V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hcomp := SyntaxFormulaComposeInduction.forward hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hb2 hf2 hq2 hV
  have heq := SyntaxRenameOutputInduction.unique hZ2 w.castSucc.castSucc K.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc hw2 hcomp hc2
  have hs := SyntaxRenameJudgmentSubst.subst_q w.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) v.castSucc.castSucc heq hV
  have ho := intro_sequential w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc T.castSucc.castSucc U.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc hq2 hs
  exact of_eq (by simp only [Formula.raise, sequential_rename]) ho

theorem collapse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L a b c d e f n v : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxComposeCodeSyntax.coded w a c e R T K)) (hf : Derives Γ (SyntaxComposeCodeSyntax.coded w b d f S U L))
    (hc : Derives Γ (sequential w R S T U a b c d e f n v)) : Derives Γ (result w K L a b e f n v) := by
  let Q := (renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj (renamed w.castSucc T.castSucc U.castSucc c.castSucc d.castSucc e.castSucc f.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw Q)
  have hb1 : Derives Δ (SyntaxComposeCodeSyntax.coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc K.castSucc) := of_eq (SyntaxComposeCodeSyntax.coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hb Q)
  have hf1 : Derives Δ (SyntaxComposeCodeSyntax.coded w.castSucc b.castSucc d.castSucc f.castSucc S.castSucc U.castSucc L.castSucc) := of_eq (SyntaxComposeCodeSyntax.coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under hf Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxFormulaComposeInduction.forward (ZFContext.under hZ Q) w.castSucc R.castSucc S.castSucc T.castSucc U.castSucc K.castSucc L.castSucc a.castSucc b.castSucc c.castSucc d.castSucc e.castSucc f.castSucc n.castSucc (Fin.last m) v.castSucc hw1 hb1 hf1 (.conjL hQ) (.conjR hQ)
  exact of_eq (result_rename w K L a b e f n v Fin.castSucc).symm ho

theorem compose_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L a b c d e f n v : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxComposeCodeSyntax.coded w a c e R T K)) (hf : Derives Γ (SyntaxComposeCodeSyntax.coded w b d f S U L)) :
    Derives Γ ((result w K L a b e f n v).iff (sequential w R S T U a b c d e f n v)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact factor (ZFContext.add hZ _) w R S T U K L a b c d e f n v (add hw _) (add hb _) (add hf _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact collapse (ZFContext.add hZ _) w R S T U K L a b c d e f n v (add hw _) (add hb _) (add hf _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxFormulaComposeFactor
