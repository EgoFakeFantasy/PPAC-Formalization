import PPAC.Migration.Internal.OriginalFormulaApplicationRecover
import PPAC.Migration.Internal.SyntaxZeroScalar

/-! 纯成员原子与原App的固定编号0及实际两参数森林双向连接。 -/
namespace PPAC.Migration.Internal.OriginalFormulaMemberApplication
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxNodeSyntax SyntaxForestSyntax SyntaxAtomSyntax

theorem scalar_at_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w zero s : Fin m) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 zero))
    (hs : Derives Γ (zeroScalar w s)) : Derives Γ (scalar w zero s) := by
  let B := constructorBody 0 0 w Fin.elim0 s
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_constructor 0 0 w Fin.elim0 s _ hs
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hz1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 zero.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 zero Fin.castSucc) (under hz B)
  have he := SyntaxNumerals.unique (ZFContext.under hZ B) 0 (Fin.last m) zero.castSucc (.conjL hB) hz1
  have ho := tag_subst 0 w.castSucc (Fin.last m) zero.castSucc Fin.elim0 s.castSucc he (.conjR hB)
  exact of_eq (scalar_rename w zero s Fin.castSucc).symm ho

theorem member_at_forest_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w zero s x y args n : Fin m) (hw : Derives Γ (omega w))
    (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 zero)) (hs : Derives Γ (zeroScalar w s))
    (hf : Derives Γ (forest 2 w (two x y) args)) :
    Derives Γ ((OriginalFormulaApplicationSyntax.application w zero args n).iff (memberCode w s x y n)) :=
  OriginalFormulaApplicationNodes.application_iff_constructor hZ 2 w zero s args n (two x y) hw (scalar_at_zero hZ w zero s hz hs) hf

theorem recover_at_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w symbol s x y args n : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (zeroScalar w s)) (hn : Derives Γ (memberCode w s x y n))
    (hargs : Derives Γ (.mem args w)) (ha : Derives Γ (OriginalFormulaApplicationSyntax.application w symbol args n)) :
    Derives Γ ((SyntaxNumeralSyntax.numeral 0 symbol).conj (forest 2 w (two x y) args)) := by
  have he := OriginalFormulaApplicationRecover.recover_application hZ 2 w symbol s args n (two x y) hw hargs hn ha
  have hIndex := Derives.impE (.conjL (SyntaxZeroScalar.index_iff hZ w symbol s hw (.conjL he))) hs
  exact .conjI hIndex (.conjR he)

theorem application_at_member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w symbol s x y args n : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (zeroScalar w s)) (hn : Derives Γ (memberCode w s x y n))
    (hargs : Derives Γ (.mem args w)) :
    Derives Γ ((OriginalFormulaApplicationSyntax.application w symbol args n).iff
      ((SyntaxNumeralSyntax.numeral 0 symbol).conj (forest 2 w (two x y) args))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact recover_at_member (ZFContext.add hZ _) w symbol s x y args n (add hw _) (add hs _) (add hn _) (add hargs _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := (SyntaxNumeralSyntax.numeral 0 symbol).conj (forest 2 w (two x y) args)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact .impE (.conjR (member_at_forest_iff (ZFContext.add hZ E) w symbol s x y args n (add hw E) (.conjL hE) (add hs E) (.conjR hE))) (add hn E)

theorem checked_at_member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w symbol s x y args n : Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (zeroScalar w s)) (hn : Derives Γ (memberCode w s x y n)) :
    Derives Γ (((Formula.mem args w).conj (OriginalFormulaApplicationSyntax.application w symbol args n)).iff
      ((SyntaxNumeralSyntax.numeral 0 symbol).conj (forest 2 w (two x y) args))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (Formula.mem args w).conj (OriginalFormulaApplicationSyntax.application w symbol args n)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact recover_at_member (ZFContext.add hZ E) w symbol s x y args n (add hw E) (add hs E) (add hn E) (.conjL hE) (.conjR hE)
  · apply Derives.impI
    let E := (SyntaxNumeralSyntax.numeral 0 symbol).conj (forest 2 w (two x y) args)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hNat := SyntaxForests.range (ZFContext.add hZ E) 2 w (two x y) args (add hw E) (.conjR hE)
    exact .conjI hNat (.impE (.conjR (application_at_member_iff (ZFContext.add hZ E) w symbol s x y args n (add hw E) (add hs E) (add hn E) hNat)) hE)

end PPAC.Migration.Internal.OriginalFormulaMemberApplication
