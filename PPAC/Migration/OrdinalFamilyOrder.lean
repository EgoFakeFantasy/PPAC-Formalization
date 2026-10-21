import PPAC.Migration.OrdinalFamilySyntax

/-! 任意内部序数集合的成员关系严格线性；加上传递性得到原序数。 -/
namespace PPAC.Migration.OrdinalFamilyOrder
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalFamilySyntax

theorem irreflexive {m} {Γ : Context m} (c : Fin m) (hc : Derives Γ (ordinals c)) :
    Derives Γ (OrdinalSyntax.irreflexive c) := by
  apply Derives.allI
  have hc' : Derives (Context.image Formula.raise Γ) (ordinals c.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  have hx : Derives (Context.add (.mem (Fin.last m) c.castSucc) (Context.image Formula.raise Γ)) (ordinal (Fin.last m)) :=
    .impE (add (ordinals_at c.castSucc (Fin.last m) hc') _) (.hyp (Or.inl rfl))
  exact OrdinalEmpty.no_self (Fin.last m) (.conjL (.conjR hx))

theorem chain {m} {Γ : Context m} (c : Fin m) (hc : Derives Γ (ordinals c)) :
    Derives Γ (membershipTransitive c) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hc' : Derives Δ (ordinals c.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using OrdinalRestriction.raise_three hc
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let K := (Formula.mem (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
    (.mem (Fin.last (m+1)).castSucc (Fin.last (m+2)))
  let Ξ := Context.add K (Context.add (.mem (Fin.last (m+2)) c.castSucc.castSucc.castSucc)
    (Context.add (.mem (Fin.last (m+1)).castSucc c.castSucc.castSucc.castSucc)
      (Context.add (.mem (Fin.last m).castSucc.castSucc c.castSucc.castSucc.castSucc) Δ)))
  have hz : Derives Ξ (ordinal (Fin.last (m+2))) := .impE
    (add (add (add (add (ordinals_at c.castSucc.castSucc.castSucc (Fin.last (m+2)) hc') _) _) _) _)
    (.hyp (Or.inr (Or.inl rfl)))
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  exact .impE (.impE (transitiveSet_at (Fin.last (m+2)) (Fin.last (m+1)).castSucc
    (Fin.last m).castSucc.castSucc (.conjL hz)) (.conjR hK)) (.conjL hK)

theorem comparable {m} {Γ : Context m} (c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hc : Derives Γ (ordinals c)) : Derives Γ (OrdinalSyntax.comparable c) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hf' : Derives Δ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hs' : Derives Δ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hs)
  have hc' : Derives Δ (ordinals c.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinals_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  apply Derives.impI
  apply Derives.impI
  let Ξ := Context.add (.mem (Fin.last (m+1)) c.castSucc.castSucc)
    (Context.add (.mem (Fin.last m).castSucc c.castSucc.castSucc) Δ)
  have hx : Derives Ξ (ordinal (Fin.last m).castSucc) :=
    .impE (add (add (ordinals_at c.castSucc.castSucc (Fin.last m).castSucc hc') _) _) (.hyp (Or.inr (Or.inl rfl)))
  have hy : Derives Ξ (ordinal (Fin.last (m+1))) :=
    .impE (add (add (ordinals_at c.castSucc.castSucc (Fin.last (m+1)) hc') _) _) (.hyp (Or.inl rfl))
  exact OrdinalComparison.compare (Fin.last m).castSucc (Fin.last (m+1))
    (add (add he' _) _) (add (add hf' _) _) (add (add hs' _) _) hx hy

theorem ordinal_of_transitive {m} {Γ : Context m} (c : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (ht : Derives Γ (transitiveSet c)) (hc : Derives Γ (ordinals c)) : Derives Γ (ordinal c) :=
  .conjI ht (.conjI (.conjI (irreflexive c hc) (.conjI (chain c hc) (comparable c he hf hs hc)))
    (OrdinalFoundation.wellFounded c hf))
end PPAC.Migration.OrdinalFamilyOrder
