import PPAC.Migration.OrdinalRecursionValues
import PPAC.Migration.IterationCompatibility

/-! 在全部内部原序数初段上，以对象有界成员归纳证明给定递归图相容及唯一。 -/
namespace PPAC.Migration.OrdinalRecursionCompatibility
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open OrdinalRecursionDeterminism OrdinalRecursionHistory IterationSyntax
open ReplacementPredicates (paramsUp)

theorem point_agrees {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d e x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d)) (hc : Derives Γ (ordinal e))
    (hf : Derives Γ (recursor p ρ f d)) (hg : Derives Γ (recursor p ρ g e))
    (hb : Derives Γ (belowAgreement f g d e x)) (hxd : Derives Γ (.mem x d)) (hxe : Derives Γ (.mem x e)) :
    Derives Γ (agreesAt f g x) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hdet' : Derives Δ (deterministic p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hdet)
  have hd' : Derives Δ (ordinal d.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hd)
  have hc' : Derives Δ (ordinal e.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  have hf' : Derives Δ (recursor p (paramsUp (paramsUp ρ)) f.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hg' : Derives Δ (recursor p (paramsUp (paramsUp ρ)) g.castSucc.castSucc e.castSucc.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hb' : Derives Δ (belowAgreement f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, belowAgreement_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb)
  have hxd' : Derives Δ (Formula.mem x.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, Formula.rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hxd)
  have hxe' : Derives Δ (Formula.mem x.castSucc.castSucc e.castSucc.castSucc) := by
    simpa only [Formula.raise, Formula.rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hxe)
  apply Derives.impI
  apply Derives.impI
  exact OrdinalRecursionValues.point_values p (paramsUp (paramsUp ρ)) f.castSucc.castSucc g.castSucc.castSucc
    d.castSucc.castSucc e.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add he' _) _) (add (add hdet' _) _) (add (add hd' _) _) (add (add hc' _) _)
    (add (add hf' _) _) (add (add hg' _) _) (add (add hb' _) _) (add (add hxd' _) _) (add (add hxe' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

set_option maxHeartbeats 800000 in
theorem progressive {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d)) (hc : Derives Γ (ordinal e))
    (hf : Derives Γ (recursor p ρ f d)) (hg : Derives Γ (recursor p ρ g e)) :
    Derives Γ (BoundedInduction.progressive agreementMatrix (args4 f g d e) d) := by
  simp only [BoundedInduction.progressive, BoundedInduction.below, agreement_pred, paramsUp, args4_0, args4_1, args4_2, args4_3]
  change Derives Γ (.all ((Formula.mem (Fin.last m) d.castSucc).imp
    ((belowAgreement f.castSucc g.castSucc d.castSucc e.castSucc (Fin.last m)).imp
      (commonAt f.castSucc g.castSucc d.castSucc e.castSucc (Fin.last m)))))
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hdet' : Derives Δ (deterministic p (paramsUp ρ)) := by
    simpa only [Formula.raise, deterministic_rename] using Derives.rename Fin.castSucc hdet
  have hd' : Derives Δ (ordinal d.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc hd
  have hc' : Derives Δ (ordinal e.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc hc
  have hf' : Derives Δ (recursor p (paramsUp ρ) f.castSucc d.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc hf
  have hg' : Derives Δ (recursor p (paramsUp ρ) g.castSucc e.castSucc) := by
    simpa only [Formula.raise, recursor_rename] using Derives.rename Fin.castSucc hg
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact point_agrees p (paramsUp ρ) f.castSucc g.castSucc d.castSucc e.castSucc (Fin.last m)
    (add (add (add (add he' _) _) _) _) (add (add (add (add hdet' _) _) _) _)
    (add (add (add (add hd' _) _) _) _) (add (add (add (add hc' _) _) _) _)
    (add (add (add (add hf' _) _) _) _) (add (add (add (add hg' _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_common {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation agreementMatrix.neg).rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d)) (hc : Derives Γ (ordinal e))
    (hf : Derives Γ (recursor p ρ f d)) (hg : Derives Γ (recursor p ρ g e)) : Derives Γ (allCommon f g d e d) := by
  have hi := BoundedInduction.induction_on_set agreementMatrix (args4 f g d e) d hsep hfoundation
    (progressive p ρ f g d e he hdet hd hc hf hg)
  simpa only [BoundedInduction.holds, allCommon, agreement_pred, paramsUp, args4_0, args4_1, args4_2, args4_3] using hi

theorem compatible {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation agreementMatrix.neg).rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d)) (hc : Derives Γ (ordinal e))
    (hf : Derives Γ (recursor p ρ f d)) (hg : Derives Γ (recursor p ρ g e)) : Derives Γ (GraphFamilySyntax.agrees f g) :=
  IterationCompatibility.from_common f g d e d he (.conjL hf) (.conjL hg)
    (.allI (.impI (.hyp (Or.inl rfl)))) (all_common p ρ f g d e he hfoundation hsep hdet hd hc hf hg)

theorem unique_same_domain {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f g d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hfoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation agreementMatrix.neg).rename Fin.elim0))
    (hdet : Derives Γ (deterministic p ρ)) (hd : Derives Γ (ordinal d))
    (hf : Derives Γ (recursor p ρ f d)) (hg : Derives Γ (recursor p ρ g d)) : Derives Γ (.equal f g) :=
  GraphPointwise.equal_of_agrees f g d he (.conjL hf) (.conjL hg)
    (compatible p ρ f g d d he hfoundation hsep hdet hd hd hf hg)
end PPAC.Migration.OrdinalRecursionCompatibility
