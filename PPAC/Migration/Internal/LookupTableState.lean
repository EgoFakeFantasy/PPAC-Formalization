import PPAC.Migration.Internal.LookupTableOperatorExistence

/-! 实际二字段状态的原配数存在、同码单射及运行时参数等词传输。 -/
namespace PPAC.Migration.Internal.LookupTableState
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem same_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i y j z p : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (state w i y p)) (hj : Derives Γ (state w j z p)) :
    Derives Γ ((Formula.equal i j).conj (.equal y z)) :=
  GodelPairInjective.injective hZ w i y j z p hw (.conjL (.conjL hi)) (.conjR (.conjL hi))
    (.conjL (.conjL hj)) (.conjR (.conjL hj)) (.conjR (.conjR hi)) (.conjR (.conjR hj))

theorem exists_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (legal w i y)) : Derives Γ (.ex (state w.castSucc i.castSucc y.castSucc (Fin.last m))) := by
  have he := GodelPairCore.exists_code hZ w i y hw (.conjL hl) (.conjR hl)
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (GodelPairSyntax.code w.castSucc i.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hl1 : Derives Δ (legal w.castSucc i.castSucc y.castSucc) := of_eq (legal_rename w i y Fin.castSucc) (under hl P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hState : Derives Δ (state w.castSucc i.castSucc y.castSucc (Fin.last m)) := .conjI hl1 hP
  have ho : Derives Δ (.ex (state w.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)))) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, state_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hState
  exact of_eq (by simp only [Formula.raise, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem contains_legal {m} {Γ : Context m} (w v i y : Fin m) (hc : Derives Γ (contains w v i y)) :
    Derives Γ (legal w i y) := by
  let P := (Formula.mem (Fin.last m) v.castSucc).conj (state w.castSucc i.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hc
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (legal_rename w i y Fin.castSucc).symm (.conjL (.conjR hP))

theorem run_subst_index {m} {Γ : Context m} (w h n i y j : Fin m) (he : Derives Γ (.equal i j))
    (hr : Derives Γ (run w h n i y)) : Derives Γ (run w h n j y) := by
  let P := run w.castSucc h.castSucc n.castSucc (Fin.last m) y.castSucc
  have e0 : P.instantiate i = run w h n i y := by simp only [P, Formula.instantiate, run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate j = run w h n j y := by simp only [P, Formula.instantiate, run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

theorem run_subst_output {m} {Γ : Context m} (w h n i y z : Fin m) (he : Derives Γ (.equal y z))
    (hr : Derives Γ (run w h n i y)) : Derives Γ (run w h n i z) := by
  let P := run w.castSucc h.castSucc n.castSucc i.castSucc (Fin.last m)
  have e0 : P.instantiate y = run w h n i y := by simp only [P, Formula.instantiate, run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z = run w h n i z := by simp only [P, Formula.instantiate, run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hr))

end PPAC.Migration.Internal.LookupTableState
