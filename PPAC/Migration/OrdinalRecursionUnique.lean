import PPAC.Migration.OrdinalRecursionExistence

/-! 全部内部序数上的实际递归图存在与已证同域唯一结合，得到真实唯一纤维。 -/
namespace PPAC.Migration.OrdinalRecursionUnique
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism OrdinalRecursionExistenceSyntax
open ReplacementPredicates (paramsUp)

theorem unique_formula {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a f : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hf : Derives Γ (recursor p ρ f a)) : Derives Γ (uniqueAt p ρ a f) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have hdet' : Derives Δ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc hdet
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hf' : Derives Δ (recursor p (paramsUp ρ) f.castSucc a.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  let M := recursor p (paramsUp ρ) (Fin.last m) a.castSucc
  have hAx := OrdinalRecursionContext.add hA' M
  exact OrdinalRecursionCompatibility.unique_same_domain p (paramsUp ρ) (Fin.last m) f.castSucc a.castSucc
    hAx.extensionality hAx.foundation hAx.agreementSeparation (add hdet' M) (add ha' M) (.hyp (Or.inl rfl)) (add hf' M)

theorem fiber_of_exists {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (ha : Derives Γ (ordinal a))
    (hx : Derives Γ (recursorExists p ρ a)) : Derives Γ (fiber p ρ a) := by
  let F := recursor p (paramsUp ρ) (Fin.last m) a.castSucc
  let Ξ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hx
  apply Derives.exE (p := F) hx
  have hAF := OrdinalRecursionContext.under hA F
  have hdetF : Derives Ξ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using under hdet F
  have haF : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha F
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have huniq := unique_formula hAF p (paramsUp ρ) a.castSucc (Fin.last m) hdetF haF hF
  have hout : Derives Ξ (fiber p (paramsUp ρ) a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, recursor_rename, uniqueAt_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hF huniq
  simpa only [Formula.raise, fiber_rename] using hout

theorem all_unique {n m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (p : Formula (n+3)) (ρ : Fin n → Fin m)
    (hdet : Derives Γ (deterministic p ρ)) (hx : Derives Γ (holds p ρ)) : Derives Γ (allUnique p ρ) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have hdet' : Derives Δ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc hdet
  have hx' : Derives Δ (holds p (paramsUp ρ)) := by
    simpa only [Formula.raise, holds_rename] using Derives.rename Fin.castSucc hx
  apply Derives.impI
  let M := ordinal (Fin.last m)
  have hOrd : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  exact fiber_of_exists (OrdinalRecursionContext.add hA' M) p (paramsUp ρ) (Fin.last m) (add hdet' M) hOrd
    (.impE (add (holds_at p (paramsUp ρ) (Fin.last m) hx') M) hOrd)
end PPAC.Migration.OrdinalRecursionUnique
