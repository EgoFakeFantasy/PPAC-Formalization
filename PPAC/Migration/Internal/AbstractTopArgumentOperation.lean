import PPAC.Migration.Internal.AbstractTopArgumentSyntax

/-! 原mode1零深度完整参数列运行与实际受检抽象映射等价；所有列表IH、Promise和码表见证均消去。 -/
namespace PPAC.Migration.Internal.AbstractTopArgumentOperation
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractTopArgumentSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q k : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode z P n q).iff (abstracted w a b A B n q k)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTransformRowSyntax.run 2 w mode z P n q
    have hmap := Derives.impE (.conjL (AbstractTopArgumentFields.run_iff (ZFContext.add hZ E) w mode z P a b A B R S n q k
      (add hw E) (add hm E) (add hd E) (add hz E) (add he E) (add hL E))) (.hyp (Or.inl rfl))
    exact intro_abstracted w a b A B n q k R S (add hL E) (add he E) hmap
  · apply Derives.impI
    let E := abstracted w a b A B n q k
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    let D := body w a b A B n q k
    let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    apply SyntaxRenameBinders.eliminate_2 D _ (.conjR hE)
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ E) D
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (add hw E) D)
    have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 (add hm E) D)
    have hd2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (SyntaxRenameBinders.under_2 (add hd E) D)
    have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 (add hz E) D)
    have hL2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (SyntaxRenameBinders.under_2 (add hL E) D)
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have hiff := AbstractTopArgumentFields.run_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc
      a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc k.castSucc.castSucc
      hw2 hm2 hd2 hz2 (.conjL hD) hL2
    exact of_eq (by simp only [Formula.raise, OriginalTransformRowSyntax.run_rename]) (.impE (.conjR hiff) (.conjR hD))

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B n q k : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode z P n q).iff (abstracted w a b A B n q k)) := by
  let D := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 D _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ D
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw D)
  have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hm D)
  have hd2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (SyntaxRenameBinders.under_2 hd D)
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz D)
  have hL2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (SyntaxRenameBinders.under_2 hL D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := at_codes_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc
    a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc k.castSucc.castSucc
    hw2 hm2 hd2 hz2 hD hL2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, abstracted_rename]) ho

theorem guarded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B n q k : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) :
    Derives Γ (((SyntaxMixedImageCodeSyntax.termList w k a B n).conj (OriginalTransformRowSyntax.run 2 w mode z P n q)).iff (abstracted w a b A B n q k)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (SyntaxMixedImageCodeSyntax.termList w k a B n).conj (OriginalTransformRowSyntax.run 2 w mode z P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := run_iff (ZFContext.add hZ E) w mode z P a b A B n q k (add hw E) (add hm E) (add hd E) (add hz E) (add hi E) (.conjL hE)
    exact .impE (.conjL he) (.conjR hE)
  · apply Derives.impI
    let E := abstracted w a b A B n q k
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hL := Derives.conjL hE
    have he := run_iff (ZFContext.add hZ E) w mode z P a b A B n q k (add hw E) (add hm E) (add hd E) (add hz E) (add hi E) hL
    exact .conjI hL (.impE (.conjR he) hE)

end PPAC.Migration.Internal.AbstractTopArgumentOperation
