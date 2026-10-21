import PPAC.Migration.OrdinalFoundation

/-! 原序数传递公式与已证传递覆盖谓词的双向推导，及序数成员的传递性。 -/
namespace PPAC.Migration.OrdinalTransitivity
open Source SourceAlgebra SourceLogic OrdinalSyntax RestrictionSyntax

theorem subset_of_member {m} {Γ : Context m} (a x : Fin m)
    (ht : Derives Γ (transitiveSet a)) (hx : Derives Γ (.mem x a)) : Derives Γ (subset x a) := by
  apply Derives.allI
  have ht' : Derives (Context.image Formula.raise Γ) (transitiveSet a.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using Derives.rename Fin.castSucc ht
  have hx' := Derives.rename Fin.castSucc hx
  apply Derives.impI
  exact .impE (.impE (add (transitiveSet_at a.castSucc x.castSucc (Fin.last m) ht') _) (add hx' _)) (.hyp (Or.inl rfl))

theorem to_canonical {m} {Γ : Context m} (a : Fin m) (ht : Derives Γ (transitiveSet a)) :
    Derives Γ (OmegaStructureSyntax.transitive a) := by
  apply Derives.allI
  have ht' : Derives (Context.image Formula.raise Γ) (transitiveSet a.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using Derives.rename Fin.castSucc ht
  apply Derives.impI
  exact subset_of_member a.castSucc (Fin.last m) (add ht' _) (.hyp (Or.inl rfl))

theorem from_canonical {m} {Γ : Context m} (a : Fin m) (ht : Derives Γ (OmegaStructureSyntax.transitive a)) :
    Derives Γ (transitiveSet a) := by
  apply Derives.allI
  apply Derives.allI
  have ht' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ))
      (OmegaStructureSyntax.transitive a.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaStructureSyntax.transitive_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ht)
  apply Derives.impI
  apply Derives.impI
  exact .impE (subset_at (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1))
    (.impE (add (add (OmegaStructureSyntax.transitive_at a.castSucc.castSucc (Fin.last m).castSucc ht') _) _)
      (.hyp (Or.inr (Or.inl rfl))))) (.hyp (Or.inl rfl))

theorem subset_trans {m} {Γ : Context m} (c b a : Fin m)
    (hc : Derives Γ (subset c b)) (hb : Derives Γ (subset b a)) : Derives Γ (subset c a) := by
  apply Derives.allI
  have hc' : Derives (Context.image Formula.raise Γ) (subset c.castSucc b.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hc
  have hb' : Derives (Context.image Formula.raise Γ) (subset b.castSucc a.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hb
  apply Derives.impI
  exact .impE (add (subset_at b.castSucc a.castSucc (Fin.last m) hb') _)
    (.impE (add (subset_at c.castSucc b.castSucc (Fin.last m) hc') _) (.hyp (Or.inl rfl)))

theorem member_transitive {m} {Γ : Context m} (a b : Fin m)
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (.mem b a)) : Derives Γ (transitiveSet b) := by
  have ht := Derives.conjL ha
  have hchain := Derives.conjL (Derives.conjR (Derives.conjL (Derives.conjR ha)))
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have ht' : Derives Δ (transitiveSet a.castSucc.castSucc) := by
    simpa only [Formula.raise, transitiveSet_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ht)
  have hchain' : Derives Δ (membershipTransitive a.castSucc.castSucc) := by
    simpa only [Formula.raise, membershipTransitive_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hchain)
  have hb' := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb)
  apply Derives.impI
  apply Derives.impI
  let Γq := Context.add (.mem (Fin.last (m+1)) (Fin.last m).castSucc)
    (Context.add (.mem (Fin.last m).castSucc b.castSucc.castSucc) Δ)
  have hxa : Derives Γq (.mem (Fin.last m).castSucc a.castSucc.castSucc) :=
    .impE (.impE (add (add (transitiveSet_at a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc ht') _) _)
      (add (add hb' _) _)) (.hyp (Or.inr (Or.inl rfl)))
  have hya : Derives Γq (.mem (Fin.last (m+1)) a.castSucc.castSucc) :=
    .impE (.impE (add (add (transitiveSet_at a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) ht') _) _) hxa)
      (.hyp (Or.inl rfl))
  exact .impE (.impE (.impE (.impE (add (add (chain_at a.castSucc.castSucc (Fin.last (m+1))
      (Fin.last m).castSucc b.castSucc.castSucc hchain') _) _) hya) hxa) (add (add hb' _) _))
    (.conjI (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl))))
end PPAC.Migration.OrdinalTransitivity
