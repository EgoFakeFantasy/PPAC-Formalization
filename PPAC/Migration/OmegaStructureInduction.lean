import PPAC.Migration.OmegaElementary

/-! 对象ω归纳的三个实际实例，覆盖所有内部ω成员。 -/
namespace PPAC.Migration.OmegaStructureInduction
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax OmegaInductionSyntax
open RestrictionSyntax
open ReplacementPredicates (paramsUp)

theorem split_base {m} {Γ : Context m} (w : Fin m) : Derives Γ (base splitMatrix (fun _ => w)) := by
  simp only [base, split_pred, paramsUp]
  exact .allI (.impI (.disjL (.hyp (Or.inl rfl))))

theorem split_step {m} {Γ : Context m} (w : Fin m) : Derives Γ (step splitMatrix (fun _ => w) w) := by
  simp only [step, split_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact .disjR (predecessor_intro w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)))

theorem decomposition {m} {Γ : Context m} (w : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation splitMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (split w.castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega splitMatrix (fun _ => w) w hs hw (split_base w) (split_step w)
  simpa only [holds, split_pred, paramsUp] using hi

theorem subset_base {m} {Γ : Context m} (w : Fin m) : Derives Γ (base subsetMatrix (fun _ => w)) := by
  simp only [base, subset_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  exact OmegaElementary.empty_subset (Fin.last m) w.castSucc (.hyp (Or.inl rfl))

theorem subset_step {m} {Γ : Context m} (w : Fin m) : Derives Γ (step subsetMatrix (fun _ => w) w) := by
  simp only [step, subset_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OmegaElementary.successor_subset (Fin.last (m+1)) (Fin.last m).castSucc w.castSucc.castSucc
    (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl)))

theorem omega_transitive {m} {Γ : Context m} (w : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation subsetMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) : Derives Γ (transitive w) := by
  have hi := OmegaInduction.induction_on_omega subsetMatrix (fun _ => w) w hs hw (subset_base w) (subset_step w)
  simpa only [holds, subset_pred, paramsUp, transitive] using hi

theorem transitive_base {m} {Γ : Context m} : Derives Γ (base transitiveMatrix (Fin.elim0 : Fin 0 → Fin m)) := by
  simp only [base, transitive_pred]
  apply Derives.allI
  apply Derives.impI
  exact OmegaElementary.empty_transitive (Fin.last m) (.hyp (Or.inl rfl))

theorem transitive_step {m} {Γ : Context m} (w : Fin m) :
    Derives Γ (step transitiveMatrix (Fin.elim0 : Fin 0 → Fin m) w) := by
  simp only [step, transitive_pred]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OmegaElementary.successor_transitive (Fin.last (m+1)) (Fin.last m).castSucc
    (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem elements_transitive {m} {Γ : Context m} (w : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (transitive (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega transitiveMatrix (Fin.elim0 : Fin 0 → Fin m) w hs hw transitive_base (transitive_step w)
  simpa only [holds, transitive_pred] using hi
end PPAC.Migration.OmegaStructureInduction
