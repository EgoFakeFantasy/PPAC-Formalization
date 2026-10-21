import PPAC.Migration.OrdinalRecursionDeterminism
import PPAC.Migration.GraphPointwise

/-! 若所有较小成员处输出相容，则实际前段限制图相等；完整entriesOn不可省略。 -/
namespace PPAC.Migration.OrdinalRecursionHistory
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax OrdinalRecursionSyntax
open IterationSyntax GraphFamilySyntax

def belowAgreement {m} (f g d e x : Fin m) : Formula m :=
  BoundedInduction.below agreementMatrix (args4 f g d e) d x

theorem belowAgreement_rename {m k} (f g d e x : Fin m) (r : Fin m → Fin k) :
    (belowAgreement f g d e x).rename r = belowAgreement (r f) (r g) (r d) (r e) (r x) := by
  simp only [belowAgreement, BoundedInduction.below, agreement_pred, ReplacementPredicates.paramsUp,
    args4_0, args4_1, args4_2, args4_3, Formula.rename, commonAt_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem below_at {m} {Γ : Context m} (f g d e x y : Fin m) (hh : Derives Γ (belowAgreement f g d e x)) :
    Derives Γ ((Formula.mem y d).imp ((Formula.mem y x).imp (commonAt f g d e y))) := by
  have hi := SetInductionLogic.bounded_below_at agreementMatrix (args4 f g d e) d x y hh
  simpa only [agreement_pred, args4_0, args4_1, args4_2, args4_3] using hi

theorem history_values {m} {Γ : Context m} (h k f g d e x y u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hh : Derives Γ (restrict h f x)) (hk : Derives Γ (restrict k g x))
    (hb : Derives Γ (belowAgreement f g d e x))
    (hu : Derives Γ (edge h y u)) (hv : Derives Γ (edge k y v)) : Derives Γ (.equal u v) := by
  have hfu := RestrictionEdges.old_edge h f x y u hh hu
  have hgv := RestrictionEdges.old_edge k g x y v hk hv
  have hyd := GraphProperties.domain_of_edge f d y u he hf hfu
  have hye := GraphProperties.domain_of_edge g e y v he hg hgv
  have hyx := RestrictionEdges.input_in_subset h f x y u he hh hu
  have hcommon := Derives.impE (Derives.impE (below_at f g d e x y hb) hyd) hyx
  have ha := Derives.impE (Derives.impE hcommon hyd) hye
  exact .impE (.impE (agreesAt_at f g y u v ha) hfu) hgv

theorem histories_agree {m} {Γ : Context m} (h k f g d e x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hh : Derives Γ (restrict h f x)) (hk : Derives Γ (restrict k g x))
    (hb : Derives Γ (belowAgreement f g d e x)) : Derives Γ (agrees h k) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrdinalRestriction.raise_three he
  have hf' : Derives Δ (functionOn f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using OrdinalRestriction.raise_three hf
  have hg' : Derives Δ (functionOn g.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using OrdinalRestriction.raise_three hg
  have hh' : Derives Δ (restrict h.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using OrdinalRestriction.raise_three hh
  have hk' : Derives Δ (restrict k.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using OrdinalRestriction.raise_three hk
  have hb' : Derives Δ (belowAgreement f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, belowAgreement_rename] using OrdinalRestriction.raise_three hb
  apply Derives.impI
  apply Derives.impI
  exact history_values h.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc
    g.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
    (add (add he' _) _) (add (add hf' _) _) (add (add hg' _) _) (add (add hh' _) _)
    (add (add hk' _) _) (add (add hb' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem histories_equal {m} {Γ : Context m} (h k f g d e x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hh : Derives Γ (restrict h f x)) (hk : Derives Γ (restrict k g x))
    (hd : Derives Γ (subset x d)) (hc : Derives Γ (subset x e))
    (hb : Derives Γ (belowAgreement f g d e x)) : Derives Γ (.equal h k) :=
  GraphPointwise.equal_of_agrees h k x he
    (RestrictionFunction.function_restrict h f d x hf hd hh)
    (RestrictionFunction.function_restrict k g e x hg hc hk)
    (histories_agree h k f g d e x he hf hg hh hk hb)
end PPAC.Migration.OrdinalRecursionHistory
