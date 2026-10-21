import PPAC.Migration.OmegaExistence

/-! 最小归纳集在对象理论内唯一。 -/
namespace PPAC.Migration.OmegaAlgebra
open Source SourceAlgebra SourceLogic PairSyntax OmegaSyntax RestrictionSyntax

theorem subset_antisymm {m} {Γ : Context m} (w v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (subset w v)) (hv : Derives Γ (subset v w)) : Derives Γ (.equal w v) := by
  apply Derives.impE (extensionality_instance w v he)
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (subset w.castSucc v.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hw
  have hv' : Derives (Context.image Formula.raise Γ) (subset v.castSucc w.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hv
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (subset_at w.castSucc v.castSucc (Fin.last m) (add hw' _)) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .impE (subset_at v.castSucc w.castSucc (Fin.last m) (add hv' _)) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (w v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hv : Derives Γ (omega v)) : Derives Γ (.equal w v) :=
  subset_antisymm w v he (.impE (omega_at w v hw) (.conjL hv)) (.impE (omega_at v w hv) (.conjL hw))

theorem member_universal {m} {Γ : Context m} (w x : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) : Derives Γ (universal x) := by
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hx' : Derives (Context.image Formula.raise Γ) (.mem x.castSucc w.castSucc) := Derives.rename Fin.castSucc hx
  apply Derives.impI
  let I := isInductive (Fin.last m)
  have hs := Derives.impE (omega_at w.castSucc (Fin.last m) (add hw' I)) (.hyp (Or.inl rfl))
  exact .impE (subset_at w.castSucc (Fin.last m) x.castSucc hs) (add hx' I)

theorem membership_iff {m} {Γ : Context m} (w x : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((Formula.mem x w).iff (universal x)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact member_universal w x (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact .impE (universal_at x w (.hyp (Or.inl rfl))) (.conjL (add hw _))
end PPAC.Migration.OmegaAlgebra
