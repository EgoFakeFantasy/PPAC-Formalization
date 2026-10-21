import PPAC.Migration.OrdinalRestriction

/-! 空集满足原序数定义；原线性条件也推出序数本身不自属。 -/
namespace PPAC.Migration.OrdinalEmpty
open Source SourceAlgebra SourceLogic OrdinalSyntax

theorem no_self {m} {Γ : Context m} (a : Fin m) (hl : Derives Γ (linear a)) : Derives Γ (Formula.mem a a).neg := by
  apply Derives.impI
  exact .impE (.impE (add (irreflexive_at a a (.conjL hl)) _) (.hyp (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem no_self_of_eq {m} {Γ : Context m} (x a : Fin m)
    (he : Derives Γ (.equal x a)) (hn : Derives Γ (Formula.mem a a).neg) : Derives Γ (Formula.mem x x).neg := by
  apply Derives.impI
  have he' := add he (.mem x x)
  have hax := mem_subst he' (Derives.hyp (Or.inl rfl))
  have haa := UnorderedPairLogic.mem_container_subst x a a he' hax
  exact .impE (add hn _) haa

theorem irreflexive_empty {m} {Γ : Context m} (z : Fin m) (hz : Derives Γ (OmegaSyntax.empty z)) : Derives Γ (irreflexive z) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (OmegaSyntax.empty z.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact .botE (.impE (add (OmegaSyntax.empty_at z.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))

theorem chain_empty {m} {Γ : Context m} (z : Fin m) (hz : Derives Γ (OmegaSyntax.empty z)) : Derives Γ (membershipTransitive z) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
      (OmegaSyntax.empty z.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using OrdinalRestriction.raise_three hz
  apply Derives.impI
  exact .botE (.impE (add (OmegaSyntax.empty_at z.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc hz') _) (.hyp (Or.inl rfl)))

theorem comparable_empty {m} {Γ : Context m} (z : Fin m) (hz : Derives Γ (OmegaSyntax.empty z)) : Derives Γ (comparable z) := by
  apply Derives.allI
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (OmegaSyntax.empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hz)
  apply Derives.impI
  exact .botE (.impE (add (OmegaSyntax.empty_at z.castSucc.castSucc (Fin.last m).castSucc hz') _) (.hyp (Or.inl rfl)))

theorem ordinal {m} {Γ : Context m} (z : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0)) (hz : Derives Γ (OmegaSyntax.empty z)) :
    Derives Γ (OrdinalSyntax.ordinal z) :=
  .conjI (OrdinalTransitivity.from_canonical z (OmegaElementary.empty_transitive z hz))
    (.conjI (.conjI (irreflexive_empty z hz) (.conjI (chain_empty z hz) (comparable_empty z hz))) (OrdinalFoundation.wellFounded z hf))
end PPAC.Migration.OrdinalEmpty
