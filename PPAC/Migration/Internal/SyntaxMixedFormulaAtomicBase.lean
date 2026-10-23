import PPAC.Migration.Internal.SyntaxMixedFormulaNullary

/-! 四类原子共同的六内部参数归纳基础情形；实际原字段由原存在消去取得。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaAtomicBase
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem equality_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.equality w a b n)) : Derives Γ (property w n) := by
  let B := SyntaxAtomSyntax.equalBody w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxAtomLogic.eliminate_equality w a b n _ ha
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedFormulaAtomOutput.equality_property_all_parameters (zf_under_2 hZ B) w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjR hB)
  exact of_eq (by simp only [Formula.raise, property_rename]) ho

theorem membership_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.membership w a b n)) : Derives Γ (property w n) := by
  let B := SyntaxAtomSyntax.memberBody w a b n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply SyntaxAtomLogic.eliminate_member w a b n _ ha
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedFormulaAtomOutput.membership_property_all_parameters (SyntaxAtomLogic.zf_under_three hZ B) w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 (.conjR hB)
  exact of_eq (by simp only [Formula.raise, property_rename]) ho

theorem property_of_atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) : Derives Γ (property w n) := by
  apply Derives.disjE ha
  · let C := (SyntaxAtomSyntax.nullary false w a b n).disj (SyntaxAtomSyntax.nullary true w a b n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact SyntaxMixedFormulaNullary.property_all_parameters (ZFContext.add (ZFContext.add hZ C) _) false w n (add (add hw C) _) (.conjR (.hyp (Or.inl rfl)))
    · exact SyntaxMixedFormulaNullary.property_all_parameters (ZFContext.add (ZFContext.add hZ C) _) true w n (add (add hw C) _) (.conjR (.hyp (Or.inl rfl)))
  · let C := (SyntaxAtomSyntax.membership w a b n).disj (SyntaxAtomSyntax.equality w a b n)
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add C Γ) C)
    · exact membership_property (ZFContext.add (ZFContext.add hZ C) _) w a b n (add (add hw C) _) (.hyp (Or.inl rfl))
    · exact equality_property (ZFContext.add (ZFContext.add hZ C) _) w a b n (add (add hw C) _) (.hyp (Or.inl rfl))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (ha : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) : Derives Γ (fiber w R S a b c d n) :=
  .impE (property_at w n R S a b c d (property_of_atomic hZ w a b n hw ha)) hi

theorem actual_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w R S a b c d n))
    (ha : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) : Derives Γ (existsOutput w R S a b c d n) :=
  SyntaxMixedFormulaOutput.exists_of_fiber w R S a b c d n (actual_fiber hZ w R S a b c d n hw hi ha)
end PPAC.Migration.Internal.SyntaxMixedFormulaAtomicBase
