import PPAC.Migration.Internal.NaturalEvaluationUniqueness

/-! 每个内部自然索引的真实唯一末值纤维。 -/
namespace PPAC.Migration.Internal.NaturalEvaluationFiber
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_natural {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a r : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w))
    (hord : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (ordinal (Fin.last m)))))
    (hall : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend ρ w a))) :
    Derives Γ (uniqueValue p ρ w a r) := by
  have hy := NaturalEvaluationExistence.at_natural p ρ w a r hw hr hord hall
  let Y := evaluation p (paramsUp ρ) w.castSucc a.castSucc r.castSucc (Fin.last m)
  let Γy := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have heY : Derives Γy (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Y
  have hwY : Derives Γy (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw Y
  have hrY : Derives Γy (.mem r.castSucc w.castSucc) := under hr Y
  have hordY : Derives Γy (.all ((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).imp (ordinal (Fin.last (m+1))))) := by
    simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using under hord Y
  have hallY : Derives Γy (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp ρ) w.castSucc a.castSucc)) := by
    simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using under hall Y
  have hY : Derives Γy Y := .hyp (Or.inl rfl)
  have hu : Derives Γy (.all ((evaluation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    let Δ := Context.image Formula.raise Γy
    have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc heY
    have hw' : Derives Δ (omega w.castSucc.castSucc) := by
      simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hwY
    have hr' : Derives Δ (.mem r.castSucc.castSucc w.castSucc.castSucc) := Derives.rename Fin.castSucc hrY
    have hord' : Derives Δ (.all ((Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).imp (ordinal (Fin.last (m+2))))) := by
      simpa only [Formula.raise, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using Derives.rename Fin.castSucc hordY
    have hall' : Derives Δ (OrdinalRecursionExistenceSyntax.allUnique (matrix p) (extend (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc)) := by
      simpa only [Formula.raise, OrdinalRecursionExistenceSyntax.allUnique_rename, extend_rename, paramsUp] using Derives.rename Fin.castSucc hallY
    have hy' : Derives Δ (evaluation p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, Y, evaluation_rename, paramsUp] using Derives.rename Fin.castSucc hY
    apply Derives.impI
    exact NaturalEvaluationUniqueness.evaluation_unique p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc
      (Fin.last (m+1)) (Fin.last m).castSucc (add he' _) (add hw' _) (add hr' _) (add hord' _) (add hall' _) (.hyp (Or.inl rfl)) (add hy' _)
  have hout : Derives Γy (uniqueValue p (paramsUp ρ) w.castSucc a.castSucc r.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, evaluation_rename, paramsUp, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hu
  simpa only [Formula.raise, uniqueValue_rename, paramsUp] using hout
end PPAC.Migration.Internal.NaturalEvaluationFiber
