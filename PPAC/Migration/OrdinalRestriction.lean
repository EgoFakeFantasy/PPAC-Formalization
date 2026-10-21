import PPAC.Migration.OrdinalTransitivity

/-! 线性与内部子集极小元条件沿子集传输，证明原序数的成员仍为原序数。 -/
namespace PPAC.Migration.OrdinalRestriction
open Source SourceAlgebra SourceLogic OrdinalSyntax RestrictionSyntax

theorem raise_three {m} {Γ : Context m} {p : Formula m} (h : Derives Γ p) :
    Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))) p.raise.raise.raise :=
  .rename Fin.castSucc (.rename Fin.castSucc (.rename Fin.castSucc h))

theorem irreflexive_subset {m} {Γ : Context m} (a b : Fin m)
    (hs : Derives Γ (subset b a)) (hi : Derives Γ (irreflexive a)) : Derives Γ (irreflexive b) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (subset b.castSucc a.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hi' : Derives (Context.image Formula.raise Γ) (irreflexive a.castSucc) := by
    simpa only [Formula.raise, irreflexive_rename] using Derives.rename Fin.castSucc hi
  apply Derives.impI
  exact .impE (add (irreflexive_at a.castSucc (Fin.last m) hi') _)
    (.impE (add (subset_at b.castSucc a.castSucc (Fin.last m) hs') _) (.hyp (Or.inl rfl)))

theorem chain_subset {m} {Γ : Context m} (a b : Fin m)
    (hs : Derives Γ (subset b a)) (ht : Derives Γ (membershipTransitive a)) : Derives Γ (membershipTransitive b) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hs' : Derives Δ (subset b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using raise_three hs
  have ht' : Derives Δ (membershipTransitive a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, membershipTransitive_rename] using raise_three ht
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Γq := Context.add ((Formula.mem (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      (.mem (Fin.last (m+1)).castSucc (Fin.last (m+2))))
    (Context.add (.mem (Fin.last (m+2)) b.castSucc.castSucc.castSucc)
      (Context.add (.mem (Fin.last (m+1)).castSucc b.castSucc.castSucc.castSucc)
        (Context.add (.mem (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc) Δ)))
  have hx : Derives Γq (.mem (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc) :=
    .impE (add (add (add (add (subset_at b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc hs') _) _) _) _)
      (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hy : Derives Γq (.mem (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc) :=
    .impE (add (add (add (add (subset_at b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc hs') _) _) _) _)
      (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  have hz : Derives Γq (.mem (Fin.last (m+2)) a.castSucc.castSucc.castSucc) :=
    .impE (add (add (add (add (subset_at b.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last (m+2)) hs') _) _) _) _)
      (.hyp (Or.inr (Or.inl rfl)))
  exact .impE (.impE (.impE (.impE (add (add (add (add (chain_at a.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) ht') _) _) _) _) hx) hy) hz) (.hyp (Or.inl rfl))

theorem comparable_subset {m} {Γ : Context m} (a b : Fin m)
    (hs : Derives Γ (subset b a)) (hc : Derives Γ (comparable a)) : Derives Γ (comparable b) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hs' : Derives Δ (subset b.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hs)
  have hc' : Derives Δ (comparable a.castSucc.castSucc) := by
    simpa only [Formula.raise, comparable_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  apply Derives.impI
  apply Derives.impI
  let Γq := Context.add (.mem (Fin.last (m+1)) b.castSucc.castSucc)
    (Context.add (.mem (Fin.last m).castSucc b.castSucc.castSucc) Δ)
  have hx : Derives Γq (.mem (Fin.last m).castSucc a.castSucc.castSucc) :=
    .impE (add (add (subset_at b.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc hs') _) _)
      (.hyp (Or.inr (Or.inl rfl)))
  have hy : Derives Γq (.mem (Fin.last (m+1)) a.castSucc.castSucc) :=
    .impE (add (add (subset_at b.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1)) hs') _) _) (.hyp (Or.inl rfl))
  exact .impE (.impE (add (add (comparable_at a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hc') _) _) hx) hy

theorem linear_subset {m} {Γ : Context m} (a b : Fin m)
    (hs : Derives Γ (subset b a)) (hl : Derives Γ (linear a)) : Derives Γ (linear b) :=
  .conjI (irreflexive_subset a b hs (.conjL hl))
    (.conjI (chain_subset a b hs (.conjL (.conjR hl))) (comparable_subset a b hs (.conjR (.conjR hl))))

theorem wellFounded_subset {m} {Γ : Context m} (a b : Fin m)
    (hs : Derives Γ (subset b a)) (hw : Derives Γ (wellFounded a)) : Derives Γ (wellFounded b) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (subset b.castSucc a.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hw' : Derives (Context.image Formula.raise Γ) (wellFounded a.castSucc) := by
    simpa only [Formula.raise, wellFounded_rename] using Derives.rename Fin.castSucc hw
  apply Derives.impI
  exact .impE (add (wellFounded_at a.castSucc (Fin.last m) hw') _)
    (.conjI (OrdinalTransitivity.subset_trans (Fin.last m) b.castSucc a.castSucc (.conjL (.hyp (Or.inl rfl))) (add hs' _))
      (.conjR (.hyp (Or.inl rfl))))

theorem member {m} {Γ : Context m} (a b : Fin m)
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (.mem b a)) : Derives Γ (ordinal b) := by
  have hs := OrdinalTransitivity.subset_of_member a b (.conjL ha) hb
  exact .conjI (OrdinalTransitivity.member_transitive a b ha hb)
    (.conjI (linear_subset a b hs (.conjL (.conjR ha))) (wellFounded_subset a b hs (.conjR (.conjR ha))))
end PPAC.Migration.OrdinalRestriction
