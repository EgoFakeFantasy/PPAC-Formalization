import PPAC.Migration.Internal.AbstractTopTermSyntax

/-! 实际首槽纯项抽象与原mode1零深度运行等价；两码表实际取得并消去。 -/
namespace PPAC.Migration.Internal.AbstractTopTermOperation
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractTopTermSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (abstracted w a b A B n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTransformRowSyntax.run 1 w mode z P n q
    have hq := Derives.impE (.conjL (AbstractTopTerm.coded_iff (ZFContext.add hZ E) w mode z P a b A B R S n q
      (add hw E) (add hm E) (add hd E) (add hz E) (add he E) (add ht E))) (.hyp (Or.inl rfl))
    exact intro_abstracted w a b A B n q R S (add he E) hq
  · apply Derives.impI
    let E := abstracted w a b A B n q
    let D := body w a b A B n q
    let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise (Context.add E Γ)))
    apply SyntaxRenameBinders.eliminate_2 D _ (.hyp (Or.inl rfl))
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ E) D
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (add hw E) D)
    have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 (add hm E) D)
    have hd2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (SyntaxRenameBinders.under_2 (add hd E) D)
    have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 (add hz E) D)
    have ht2 : Derives Δ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (SyntaxRenameBinders.under_2 (add ht E) D)
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have hiff := AbstractTopTerm.coded_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc
      a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc
      hw2 hm2 hd2 hz2 (.conjL hD) ht2
    have ho := Derives.impE (.conjR hiff) (.conjR hD)
    exact of_eq (by simp only [Formula.raise, OriginalTransformRowSyntax.run_rename]) ho

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B))
    (ht : Derives Γ (SyntaxTermSyntax.term w a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff (abstracted w a b A B n q)) := by
  let D := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 D _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ D
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw D)
  have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hm D)
  have hd2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (SyntaxRenameBinders.under_2 hd D)
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz D)
  have ht2 : Derives Δ (SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) (SyntaxRenameBinders.under_2 ht D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := at_codes_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc
    a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc hw2 hm2 hd2 hz2 hD ht2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, abstracted_rename]) ho

theorem source_type {m} {Γ : Context m} (w a b A B n q : Fin m)
    (hq : Derives Γ (abstracted w a b A B n q)) : Derives Γ (SyntaxTermSyntax.term w a B n) := by
  let D := body w a b A B n q
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 D _ hq
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := SyntaxCodedMixedTermTyping.source_type w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (.conjR hD)
  exact of_eq (by simp only [Formula.raise, SyntaxTermSyntax.term_rename]) ho

theorem guarded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) :
    Derives Γ (((SyntaxTermSyntax.term w a B n).conj (OriginalTransformRowSyntax.run 1 w mode z P n q)).iff (abstracted w a b A B n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (SyntaxTermSyntax.term w a B n).conj (OriginalTransformRowSyntax.run 1 w mode z P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := run_iff (ZFContext.add hZ E) w mode z P a b A B n q (add hw E) (add hm E) (add hd E) (add hz E) (add hi E) (.conjL hE)
    exact .impE (.conjL he) (.conjR hE)
  · apply Derives.impI
    let E := abstracted w a b A B n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have ht := source_type w a b A B n q hE
    have he := run_iff (ZFContext.add hZ E) w mode z P a b A B n q (add hw E) (add hm E) (add hd E) (add hz E) (add hi E) ht
    exact .conjI ht (.impE (.conjR he) hE)

end PPAC.Migration.Internal.AbstractTopTermOperation
