import PPAC.Migration.PowerSetSyntax

/-! 实际幂集的外延唯一性、等词传输及包含单调性；全部原规则推导。 -/
namespace PPAC.Migration.PowerSetLogic
open Source SourceAlgebra SourceLogic PairSyntax RestrictionSyntax PowerSetSyntax

theorem unique {m} {Γ : Context m} (w u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (powerOf w v)) (hu : Derives Γ (powerOf u v)) : Derives Γ (.equal w u) := by
  apply Derives.impE (extensionality_instance w u he)
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (powerOf w.castSucc v.castSucc) := by
    simpa only [Formula.raise, powerOf_rename] using Derives.rename Fin.castSucc hw
  have hu' : Derives (Context.image Formula.raise Γ) (powerOf u.castSucc v.castSucc) := by
    simpa only [Formula.raise, powerOf_rename] using Derives.rename Fin.castSucc hu
  have hwz := power_at w.castSucc v.castSucc (Fin.last m) hw'
  have huz := power_at u.castSucc v.castSucc (Fin.last m) hu'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add huz _)) (.impE (.conjL (add hwz _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hwz _)) (.impE (.conjL (add huz _)) (.hyp (Or.inl rfl)))

theorem subst_base {m} {Γ : Context m} (w v u : Fin m)
    (he : Derives Γ (.equal v u)) (hw : Derives Γ (powerOf w v)) : Derives Γ (powerOf w u) := by
  have hi : Derives Γ ((powerOf w.castSucc (Fin.last m)).instantiate v) := by
    simpa only [Formula.instantiate, powerOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw
  have hr := Derives.eqSubst (powerOf w.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, powerOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr

theorem subst_power {m} {Γ : Context m} (w u v : Fin m)
    (he : Derives Γ (.equal w u)) (hw : Derives Γ (powerOf w v)) : Derives Γ (powerOf u v) := by
  have hi : Derives Γ ((powerOf (Fin.last m) v.castSucc).instantiate w) := by
    simpa only [Formula.instantiate, powerOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw
  have hr := Derives.eqSubst (powerOf (Fin.last m) v.castSucc) he hi
  simpa only [Formula.instantiate, powerOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr

theorem base_member {m} {Γ : Context m} (w v : Fin m) (hw : Derives Γ (powerOf w v)) : Derives Γ (.mem v w) :=
  .impE (.conjR (power_at w v v hw)) (.allI (.impI (.hyp (Or.inl rfl))))

theorem monotone {m} {Γ : Context m} (w u v t : Fin m)
    (hw : Derives Γ (powerOf w v)) (hu : Derives Γ (powerOf u t)) (hs : Derives Γ (subset v t)) :
    Derives Γ (subset w u) := by
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (powerOf w.castSucc v.castSucc) := by
    simpa only [Formula.raise, powerOf_rename] using Derives.rename Fin.castSucc hw
  have hu' : Derives (Context.image Formula.raise Γ) (powerOf u.castSucc t.castSucc) := by
    simpa only [Formula.raise, powerOf_rename] using Derives.rename Fin.castSucc hu
  have hs' : Derives (Context.image Formula.raise Γ) (subset v.castSucc t.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  apply Derives.impI
  have hz := Derives.impE (.conjL (add (power_at w.castSucc v.castSucc (Fin.last m) hw') _)) (.hyp (Or.inl rfl))
  exact .impE (.conjR (add (power_at u.castSucc t.castSucc (Fin.last m) hu') _))
    (OrdinalTransitivity.subset_trans (Fin.last m) v.castSucc t.castSucc hz (add hs' _))
end PPAC.Migration.PowerSetLogic
