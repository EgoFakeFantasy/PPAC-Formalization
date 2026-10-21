import PPAC.Migration.Internal.StructuralListShiftStep

/-! 两条真实轨迹的同索引步关系覆盖全部内部ω；原Separation归纳实例实际消去。 -/
namespace PPAC.Migration.Internal.StructuralListShiftInduction
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StructuralListShiftSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem base {m} {Γ : Context m} (head : Bool) (ρ : Fin 3 → Fin m)
    (hab : Derives Γ (step head (ρ 0) (ρ 1) (ρ 2))) :
    Derives Γ (OmegaInductionSyntax.base (StructuralListShiftSyntax.matrix head) ρ) := by
  simp only [OmegaInductionSyntax.base, StructuralListShiftSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let E := empty (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hab1 : Derives Δ (step head (ρ 0).castSucc (ρ 1).castSucc (ρ 2).castSucc) := by
    simpa only [Formula.raise, step_rename] using under hab E
  exact StructuralListShiftStep.coupled_empty head _ _ _ _ (.hyp (Or.inl rfl)) hab1

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.step (StructuralListShiftSyntax.matrix head) ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, StructuralListShiftSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let C := coupled head (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (ρ 2).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add C (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add
    (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) C) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)) M) C) S
  exact StructuralListShiftStep.coupled_successor hZ2 head _ _ _ _ _ hw2
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_coupled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (ρ : Fin 3 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hab : Derives Γ (StructuralListProjectionSyntax.step head (ρ 0) (ρ 1) (ρ 2))) :
    Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp
      (coupled head (ρ 0).castSucc (ρ 1).castSucc (ρ 2).castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega (StructuralListShiftSyntax.matrix head) ρ (ρ 0)
    (ZFContext.separation hZ (StructuralListShiftSyntax.matrix head)) hw (base head ρ hab) (step hZ head ρ hw)
  simpa only [OmegaInductionSyntax.holds, StructuralListShiftSyntax.matrix_pred, paramsUp] using hi

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hab : Derives Γ (StructuralListProjectionSyntax.step head w a b)) :
    Derives Γ (coupled head w a b r) := by
  have h0 : Source.SetLanguage.args3 w a b (0 : Fin 3) = w := rfl
  have h1 : Source.SetLanguage.args3 w a b (1 : Fin 3) = a := by
    change Fin.cases w (Source.SetLanguage.args2 a b) (Fin.succ (0 : Fin 2)) = a
    rw [Fin.cases_succ]
    rfl
  have h2 : Source.SetLanguage.args3 w a b (2 : Fin 3) = b := by
    change Fin.cases w (Source.SetLanguage.args2 a b) (Fin.succ (1 : Fin 2)) = b
    rw [Fin.cases_succ]
    change Fin.cases a (fun _ : Fin 1 => b) (Fin.succ (0 : Fin 1)) = b
    rw [Fin.cases_succ]
  have hw' : Derives Γ (omega (Source.SetLanguage.args3 w a b 0)) := by simpa only [h0] using hw
  have hab' : Derives Γ (StructuralListProjectionSyntax.step head (Source.SetLanguage.args3 w a b 0) (Source.SetLanguage.args3 w a b 1) (Source.SetLanguage.args3 w a b 2)) := by simpa only [h0, h1, h2] using hab
  have hall := all_coupled hZ head (Source.SetLanguage.args3 w a b) hw' hab'
  have h : Derives Γ ((Formula.mem r w).imp (coupled head w a b r)) := by
    simpa only [Formula.instantiate, Formula.rename, coupled_rename, Fin.lastCases_last, Fin.lastCases_castSucc,
      h0, h1, h2, id_eq] using Derives.allE r hall
  exact .impE h hr
end PPAC.Migration.Internal.StructuralListShiftInduction
