import PPAC.Migration.OrdinalSyntax

/-! 原Foundation推出全部内部子集的成员极小元条件，不作外部良基断言。 -/
namespace PPAC.Migration.OrdinalFoundation
open Source SourceAlgebra SourceLogic OrdinalSyntax

theorem opposite_minimal {m} {Γ : Context m} (c x : Fin m)
    (h : Derives Γ (MinimalPredicates.setMinimal c x)) : Derives Γ (setMinimal c x) := by
  apply Derives.conjI (.conjL h)
  apply Derives.allI
  have h' : Derives (Context.image Formula.raise Γ) (MinimalPredicates.setMinimal c.castSucc x.castSucc) := by
    simpa only [Formula.raise, MinimalPredicates.setMinimal_rename] using Derives.rename Fin.castSucc h
  apply Derives.impI
  apply Derives.impI
  exact .impE (.impE (add (add (MinimalPredicates.specialize_setMinimal c.castSucc x.castSucc (Fin.last m) h') _) _)
    (.hyp (Or.inl rfl))) (.hyp (Or.inr (Or.inl rfl)))

theorem regular_to_minimal {m} {Γ : Context m} (c : Fin m) (h : Derives Γ (MinimalPredicates.regular c)) :
    Derives Γ (minimalExists c) := by
  let X := MinimalPredicates.setMinimal c.castSucc (Fin.last m)
  let Γx := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at h
  apply Derives.exE (p := X) h
  have hx : Derives Γx X := .hyp (Or.inl rfl)
  have hm := opposite_minimal c.castSucc (Fin.last m) hx
  have hr : Derives Γx (minimalExists c.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, setMinimal_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hm
  simpa only [Formula.raise, minimalExists_rename] using hr

theorem wellFounded {m} {Γ : Context m} (a : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0)) : Derives Γ (OrdinalSyntax.wellFounded a) := by
  apply Derives.allI
  have hf' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  exact regular_to_minimal (Fin.last m) (.impE (add (MinimalInstances.foundation_instance (Fin.last m) hf') _)
    (.conjR (.hyp (Or.inl rfl))))
end PPAC.Migration.OrdinalFoundation
