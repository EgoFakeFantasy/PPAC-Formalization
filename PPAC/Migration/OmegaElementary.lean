import PPAC.Migration.OmegaStructureSyntax

/-! 空集与后继的对象传递性质；这里只用原等词及成员规则。 -/
namespace PPAC.Migration.OmegaElementary
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax RestrictionSyntax InsertLogic

theorem empty_subset {m} {Γ : Context m} (z w : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (subset z w) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact .botE (.impE (add (empty_at z.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))

theorem successor_subset {m} {Γ : Context m} (s x w : Fin m)
    (hs : Derives Γ (successor s x)) (hx : Derives Γ (.mem x w)) (hb : Derives Γ (subset x w)) :
    Derives Γ (subset s w) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (successor s.castSucc x.castSucc) := by
    simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hs
  have hb' : Derives (Context.image Formula.raise Γ) (subset x.castSucc w.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hb
  have hx' := Derives.rename Fin.castSucc hx
  apply Derives.impI
  have hc := InsertLogic.member_cases s.castSucc x.castSucc x.castSucc (Fin.last m) (add hs' _) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact .impE (add (add (subset_at x.castSucc w.castSucc (Fin.last m) hb') _) _) (.hyp (Or.inl rfl))
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add (add hx' _) _)

theorem empty_transitive {m} {Γ : Context m} (z : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (transitive z) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact .botE (.impE (add (empty_at z.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))

theorem successor_transitive {m} {Γ : Context m} (s x : Fin m)
    (hs : Derives Γ (successor s x)) (hx : Derives Γ (transitive x)) : Derives Γ (transitive s) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (successor s.castSucc x.castSucc) := by
    simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hs
  have hx' : Derives (Context.image Formula.raise Γ) (transitive x.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using Derives.rename Fin.castSucc hx
  apply Derives.impI
  have hc := InsertLogic.member_cases s.castSucc x.castSucc x.castSucc (Fin.last m) (add hs' _) (.hyp (Or.inl rfl))
  apply Derives.allI
  have hsY : Derives (Context.image Formula.raise (Context.add (.mem (Fin.last m) s.castSucc)
      (Context.image Formula.raise Γ))) (successor s.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc (add hs' _)
  have hcY := Derives.rename Fin.castSucc hc
  have hxY : Derives (Context.image Formula.raise (Context.add (.mem (Fin.last m) s.castSucc)
      (Context.image Formula.raise Γ))) (transitive x.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using Derives.rename Fin.castSucc (add hx' _)
  let Δ := Context.image Formula.raise (Context.add (.mem (Fin.last m) s.castSucc) (Context.image Formula.raise Γ))
  let Γt := Context.add (.mem (Fin.last (m+1)) (Fin.last m).castSucc) Δ
  apply Derives.impI
  apply Derives.disjE (add hcY _)
  · have hb : Derives (Context.add (.mem (Fin.last m).castSucc x.castSucc.castSucc) Γt)
        (subset (Fin.last m).castSucc x.castSucc.castSucc) := Derives.impE (add (add (transitive_at x.castSucc.castSucc (Fin.last m).castSucc hxY) _) _)
        (.hyp (Or.inl rfl))
    have htx : Derives (Context.add (.mem (Fin.last m).castSucc x.castSucc.castSucc) Γt)
        (.mem (Fin.last (m+1)) x.castSucc.castSucc) := Derives.impE (subset_at (Fin.last m).castSucc x.castSucc.castSucc (Fin.last (m+1)) hb)
      (.hyp (Or.inr (Or.inl rfl)))
    exact old_member s.castSucc.castSucc x.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))
      (add (add hsY _) _) htx
  · have htx : Derives (Context.add (.equal (Fin.last m).castSucc x.castSucc.castSucc) Γt)
        (.mem (Fin.last (m+1)) x.castSucc.castSucc) := UnorderedPairLogic.mem_container_subst (Fin.last m).castSucc x.castSucc.castSucc (Fin.last (m+1))
      (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))
    exact old_member s.castSucc.castSucc x.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))
      (add (add hsY _) _) htx
end PPAC.Migration.OmegaElementary
