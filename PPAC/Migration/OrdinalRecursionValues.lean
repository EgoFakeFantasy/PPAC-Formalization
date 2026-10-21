import PPAC.Migration.OrdinalRecursionHistory

/-! 两个实际历史图的相等与算子单值性推出当前递归输出相等。 -/
namespace PPAC.Migration.OrdinalRecursionValues
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism OrdinalRecursionHistory
open ReplacementPredicates (paramsUp)

theorem history_outputs {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d e x u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (ho : Derives Γ (ordinal x))
    (hd : Derives Γ (subset x d)) (hc : Derives Γ (subset x e))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hb : Derives Γ (belowAgreement f g d e x))
    (hu : Derives Γ (history p ρ f x u)) (hv : Derives Γ (history p ρ g x v)) : Derives Γ (.equal u v) := by
  let H := (restrict (Fin.last m) f.castSucc x.castSucc).conj
    (operator p (paramsUp ρ) x.castSucc (Fin.last m) u.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hu
  apply Derives.exE (p := H) hu
  have he1 : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he H
  have hdet1 : Derives Ξ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet H
  have ho1 : Derives Ξ (ordinal x.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ho H
  have hd1 : Derives Ξ (subset x.castSucc d.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hd H
  have hc1 : Derives Ξ (subset x.castSucc e.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hc H
  have hf1 : Derives Ξ (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf H
  have hg1 : Derives Ξ (functionOn g.castSucc e.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hg H
  have hb1 : Derives Ξ (belowAgreement f.castSucc g.castSucc d.castSucc e.castSucc x.castSucc) := by
    simpa only [Formula.raise, belowAgreement_rename] using under hb H
  have hv1 : Derives Ξ (history p (paramsUp ρ) g.castSucc x.castSucc v.castSucc) := by
    simpa only [Formula.raise, history_rename] using under hv H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  let K := (restrict (Fin.last (m+1)) g.castSucc.castSucc x.castSucc.castSucc).conj
    (operator p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc)
  let Ψ := Context.add K (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex K) at hv1
  apply Derives.exE (p := K) hv1
  have he2 : Derives Ψ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he1 K
  have hdet2 : Derives Ψ (deterministic p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet1 K
  have ho2 : Derives Ψ (ordinal x.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ho1 K
  have hd2 : Derives Ψ (subset x.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hd1 K
  have hc2 : Derives Ψ (subset x.castSucc.castSucc e.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hc1 K
  have hf2 : Derives Ψ (functionOn f.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf1 K
  have hg2 : Derives Ψ (functionOn g.castSucc.castSucc e.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hg1 K
  have hb2 : Derives Ψ (belowAgreement f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, belowAgreement_rename] using under hb1 K
  have hH2 : Derives Ψ ((restrict (Fin.last m).castSucc f.castSucc.castSucc x.castSucc.castSucc).conj
      (operator p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc u.castSucc.castSucc)) := by
    simpa only [Formula.raise, H, Formula.rename, restrict_rename, operator_rename] using under hH K
  have hK : Derives Ψ K := .hyp (Or.inl rfl)
  have heq := histories_equal (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc g.castSucc.castSucc
    d.castSucc.castSucc e.castSucc.castSucc x.castSucc.castSucc he2 hf2 hg2 (.conjL hH2) (.conjL hK) hd2 hc2 hb2
  have hfunc := RestrictionFunction.function_restrict (Fin.last m).castSucc f.castSucc.castSucc d.castSucc.castSucc
    x.castSucc.castSucc hf2 hd2 (.conjL hH2)
  have hsingle := Derives.impE (deterministic_at p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc hdet2)
    (Derives.conjI ho2 hfunc)
  have hv' := operator_subst_history p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    v.castSucc.castSucc (eq_symm heq) (.conjR hK)
  exact .impE (.impE (functional_at p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc
    u.castSucc.castSucc v.castSucc.castSucc hsingle) (.conjR hH2)) hv'

theorem point_values {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d e x u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d)) (hc : Derives Γ (ordinal e))
    (hf : Derives Γ (recursor p ρ f d)) (hg : Derives Γ (recursor p ρ g e))
    (hb : Derives Γ (belowAgreement f g d e x)) (hxd : Derives Γ (.mem x d)) (hxe : Derives Γ (.mem x e))
    (hu : Derives Γ (edge f x u)) (hv : Derives Γ (edge g x v)) : Derives Γ (.equal u v) :=
  history_outputs p ρ f g d e x u v he hdet (OrdinalRestriction.member d x hd hxd)
    (OrdinalTransitivity.subset_of_member d x (.conjL hd) hxd)
    (OrdinalTransitivity.subset_of_member e x (.conjL hc) hxe) (.conjL hf) (.conjL hg) hb
    (.impE (.impE (equations_at p ρ f d x u (.conjR hf)) hxd) hu)
    (.impE (.impE (equations_at p ρ g e x v (.conjR hg)) hxe) hv)
end PPAC.Migration.OrdinalRecursionValues
