import PPAC.Migration.Internal.ProjectCompilerRecursivePoint

/-! Full actual compiler recursive equation on all internal candidates, with all witnesses discharged. -/
namespace PPAC.Migration.Internal.ProjectCompilerRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_carrier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b q : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c)) :
    Derives Γ ((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)) := by
  apply SourcePropositional.by_cases (Formula.mem n w)
  · let N := Formula.mem n w
    let Ξ := Context.add N Γ
    have hn : Derives Ξ N := .hyp (Or.inl rfl)
    let V := ProjectCompilerEvaluationSyntax.evaluation w.castSucc c.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply Derives.exE (p := V) (ProjectCompilerEvaluationExistence.at_natural (ZFContext.add hZ N) w c n (add hw N) hn)
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw N) V)
    have hc1 := of_eq (ProjectCompilerCodeSyntax.carrier_rename w a c Fin.castSucc) (under (add hc N) V)
    have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn V
    have hr := ProjectCompilerRecursivePoint.at_value (ZFContext.under (ZFContext.add hZ N) V)
      w.castSucc a.castSucc c.castSucc n.castSucc (Fin.last m) b.castSucc q.castSucc hw1 hn1 hc1 hV
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
      ProjectCompilerRecursiveSyntax.criterion_rename]) hr
  · apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl)))
        (.conjL (ProjectCompilerCodeProperties.guards w n b q (.hyp (Or.inl rfl)))))
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)) := by
  let B := ProjectCompilerCodeSyntax.carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (ProjectCompilerCodeCarrier.exists_carrier hZ w)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hr := at_carrier (HornBinderRules.zf_body 2 hZ B) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    n.castSucc.castSucc b.castSucc.castSucc q.castSucc.castSucc hw2 hB
  exact of_eq (by simp only [Formula.iff, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
    ProjectCompilerRecursiveSyntax.criterion_rename, HornBinderSyntax.old]) hr

def universalLaw {m} (w : Fin m) : Formula m := .all (.all (.all
  ((ProjectCompilerCodeSyntax.compiled w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
    (ProjectCompilerRecursiveSyntax.criterion w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))))))

theorem universalLaw_rename {m l} (w : Fin m) (ρ : Fin m → Fin l) :
    (universalLaw w).rename ρ = universalLaw (ρ w) := by
  simp only [universalLaw, Formula.iff, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
    ProjectCompilerRecursiveSyntax.criterion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (universalLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hZ3 := HornBinderRules.zf_many 3 hZ
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  exact recursive_iff hZ3 (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) hw3

end PPAC.Migration.Internal.ProjectCompilerRecursive
