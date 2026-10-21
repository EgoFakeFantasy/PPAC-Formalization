import PPAC.Migration.Internal.FormulaCodeCongruence

/-! 固定真实载体下，将所有Typed查询替换为FormulaCode；覆盖全部内部子码及后继见证。 -/
namespace PPAC.Migration.Internal.FormulaCodeCriterionTransfer
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax SyntaxLogicalSyntax SyntaxAtomSyntax
open SyntaxTypeJudgmentSyntax FormulaCodeSyntax FormulaCodeCongruence
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem typed_iff_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hc : Derives Γ (carrier w a c)) : Derives Γ ((typed w c n b f).iff (formulaCode w n b f)) := by
  have hh := FormulaCodeCarrier.code_iff_typed hZ w a c n b f hc
  exact .conjI (.conjR hh) (.conjL hh)

theorem advanced_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c x b f : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.advancedTyped w c x b f).iff (FormulaCodeRecursiveSyntax.advancedCode w x b f)) := by
  apply ex_congr
  have hc1 : Derives (Context.image Formula.raise Γ) (carrier w.castSucc a.castSucc c.castSucc) := by
    simpa only [carrier_rename] using Derives.rename Fin.castSucc hc
  exact conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (typed_iff_code (ZFContext.rename hZ Fin.castSucc) w.castSucc a.castSucc c.castSucc x.castSucc (Fin.last m) f.castSucc hc1)

theorem check_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w a c x b f : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.stepCheck advance w c x b f).iff (FormulaCodeRecursiveSyntax.stepCheck advance w x b f)) := by
  cases advance
  · exact typed_iff_code hZ w a c x b f hc
  · exact advanced_iff hZ w a c x b f hc

theorem single_fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w a c b f x n : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.singleFields tag advance w c b f x n).iff (FormulaCodeRecursiveSyntax.singleFields tag advance w b f x n)) :=
  conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (check_iff hZ advance w a c x b f hc))

theorem binary_fields_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a c b f x y n : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.binaryFields kind w c b f x y n).iff (FormulaCodeRecursiveSyntax.binaryFields kind w b f x y n)) :=
  conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
        (conj_congr (typed_iff_code hZ w a c x b f hc) (typed_iff_code hZ w a c y b f hc))))

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w a c b f n : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.singleCase tag advance w c b f n).iff (FormulaCodeRecursiveSyntax.singleCase tag advance w b f n)) := by
  apply conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply ex_congr
  have hc1 : Derives (Context.image Formula.raise Γ) (carrier w.castSucc a.castSucc c.castSucc) := by
    simpa only [carrier_rename] using Derives.rename Fin.castSucc hc
  exact single_fields_iff (ZFContext.rename hZ Fin.castSucc) tag advance
    w.castSucc a.castSucc c.castSucc b.castSucc f.castSucc (Fin.last m) n.castSucc hc1

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a c b f n : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.binaryCase kind w c b f n).iff (FormulaCodeRecursiveSyntax.binaryCase kind w b f n)) := by
  apply conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply ex_congr
  apply ex_congr
  have hc2 : Derives (Context.image Formula.raise (Context.image Formula.raise Γ))
      (carrier w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [carrier_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  exact binary_fields_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) kind
    w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hc2

theorem all_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.allCases w c n b f).iff (FormulaCodeRecursiveSyntax.allCases w n b f)) := by
  open SyntaxTypeLocalTransfer in
  exact disj_congr (iff_refl (atomic w b f n))
    (disj_congr (single_iff hZ 4 false w a c b f n hc)
      (disj_congr (binary_iff hZ 0 w a c b f n hc)
        (disj_congr (binary_iff hZ 1 w a c b f n hc)
          (disj_congr (binary_iff hZ 2 w a c b f n hc)
            (disj_congr (binary_iff hZ 3 w a c b f n hc)
              (disj_congr (single_iff hZ 9 true w a c b f n hc)
                (single_iff hZ 10 true w a c b f n hc)))))))

theorem criterion_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((SyntaxTypeRecursiveSyntax.criterion w c n b f).iff (FormulaCodeRecursiveSyntax.criterion w n b f)) :=
  conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (all_iff hZ w a c n b f hc)
end PPAC.Migration.Internal.FormulaCodeCriterionTransfer
