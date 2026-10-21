import PPAC.Migration.OrdinalRecursionExtensionAlgebra

/-! 原完整图扩展保留全部递归方程；结论不是仅新边正确。 -/
namespace PPAC.Migration.OrdinalRecursionExtension
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

theorem equations_preserved {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g s c f d y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d))
    (hw : Derives Γ (GraphInsertSyntax.witness g s c f d d y))
    (hy : Derives Γ (operator p ρ d f y)) : Derives Γ (equations p ρ g s) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hd' : Derives Δ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc hd
  have hf' : Derives Δ (recursor p (paramsUp ρ) f.castSucc d.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc hf
  have hw' : Derives Δ (GraphInsertSyntax.witness g.castSucc s.castSucc c.castSucc f.castSucc d.castSucc d.castSucc y.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.witness_rename] using Derives.rename Fin.castSucc hw
  have hy' : Derives Δ (operator p (paramsUp ρ) d.castSucc f.castSucc y.castSucc) := by
    simpa only [Formula.raise, operator_rename] using Derives.rename Fin.castSucc hy
  apply Derives.impI
  let X := Formula.mem (Fin.last m) s.castSucc
  let Γx := Context.add X Δ
  have hx : Derives Γx X := .hyp (Or.inl rfl)
  apply Derives.allI
  let Γy := Context.image Formula.raise Γx
  have heY : Derives Γy (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (add he' X)
  have hdY : Derives Γy (ordinal d.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc (add hd' X)
  have hfY : Derives Γy (recursor p (paramsUp (paramsUp ρ)) f.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc (add hf' X)
  have hwY : Derives Γy (GraphInsertSyntax.witness g.castSucc.castSucc s.castSucc.castSucc c.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.witness_rename] using Derives.rename Fin.castSucc (add hw' X)
  have hyY : Derives Γy (operator p (paramsUp (paramsUp ρ)) d.castSucc.castSucc f.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, operator_rename] using Derives.rename Fin.castSucc (add hy' X)
  have hxY : Derives Γy (.mem (Fin.last m).castSucc s.castSucc.castSucc) := Derives.rename Fin.castSucc hx
  apply Derives.impI
  exact OrdinalRecursionExtensionAlgebra.point_history p (paramsUp (paramsUp ρ)) g.castSucc.castSucc
    s.castSucc.castSucc c.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add heY _) (add hdY _) (add hfY _) (add hwY _) (add hyY _)
    (add hxY _) (.hyp (Or.inl rfl))

theorem recursor_preserved {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g s c f d y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d))
    (hw : Derives Γ (GraphInsertSyntax.witness g s c f d d y))
    (hy : Derives Γ (operator p ρ d f y)) : Derives Γ (recursor p ρ g s) :=
  .conjI (.conjL (.conjR (.conjR (.conjR hw)))) (equations_preserved p ρ g s c f d y he hd hf hw hy)
end PPAC.Migration.OrdinalRecursionExtension
