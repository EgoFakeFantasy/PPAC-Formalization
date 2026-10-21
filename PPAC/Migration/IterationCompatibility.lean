import PPAC.Migration.IterationInduction

/-! 对象ω内的传递域轨迹相容；同域轨迹通过完整图外延性相等。 -/
namespace PPAC.Migration.IterationCompatibility
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax IterationSyntax RestrictionSyntax

theorem values_at {m} {Γ : Context m} (f g d e w x u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hb : Derives Γ (subset d w)) (hh : Derives Γ (allCommon f g d e w))
    (hu : Derives Γ (edge f x u)) (hv : Derives Γ (edge g x v)) : Derives Γ (.equal u v) := by
  have hxd := GraphProperties.domain_of_edge f d x u he hf hu
  have hxe := GraphProperties.domain_of_edge g e x v he hg hv
  have hxw := Derives.impE (subset_at d w x hb) hxd
  have ha : Derives Γ (agreesAt f g x) :=
    .impE (.impE (IterationInduction.common_at f g d e w x hh hxw) hxd) hxe
  exact .impE (.impE (agreesAt_at f g x u v ha) hu) hv

theorem from_common {m} {Γ : Context m} (f g d e w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hb : Derives Γ (subset d w)) (hh : Derives Γ (allCommon f g d e w)) : Derives Γ (GraphFamilySyntax.agrees f g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using
      Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he))
  have hf' : Derives Δ (functionOn f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using
      Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf))
  have hg' : Derives Δ (functionOn g.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using
      Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg))
  have hb' : Derives Δ (subset d.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using
      Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb))
  have hh' : Derives Δ (allCommon f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc
      d.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, allCommon_rename] using
      Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hh))
  apply Derives.impI
  apply Derives.impI
  exact values_at f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc
    e.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
    (Fin.last (m+1)).castSucc (Fin.last (m+2)) (add (add he' _) _) (add (add hf' _) _) (add (add hg' _) _)
    (add (add hb' _) _) (add (add hh' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem compatible {m} {Γ : Context m} (f g d e z a w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a))
    (hd : Derives Γ (transitive d)) (hc : Derives Γ (transitive e)) (hb : Derives Γ (subset d w)) :
    Derives Γ (GraphFamilySyntax.agrees f g) := from_common f g d e w he (.conjL hf) (.conjL hg) hb
      (IterationInduction.all_common f g d e z a w he hs hw hz hf hg hd hc)

theorem unique_same_domain {m} {Γ : Context m} (f g d z a w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g d z a))
    (hd : Derives Γ (transitive d)) (hb : Derives Γ (subset d w)) : Derives Γ (.equal f g) :=
  GraphPointwise.equal_of_agrees f g d he (.conjL hf) (.conjL hg)
    (compatible f g d d z a w he hs hw hz hf hg hd hd hb)
end PPAC.Migration.IterationCompatibility
