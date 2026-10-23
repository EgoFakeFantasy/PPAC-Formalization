import PPAC.Migration.Internal.HornExprUnique

/-! 每个上游固定表达式的实际唯一内部纤维和全部候选相等刻画。 -/
namespace PPAC.Migration.Internal.HornExprValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem at_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w y z : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) (hy : Derives Γ (graph e w env y)) :
    Derives Γ ((graph e w env z).iff (.equal z y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact HornExprUnique.unique (ZFContext.add hZ _) e w z y env (add hw _) (add hn _) (.hyp (Or.inl rfl)) (add hy _)
  · apply Derives.impI
    exact output_subst e w y z env (eq_symm (.hyp (Or.inl rfl))) (add hy _)

theorem unique_value {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w y : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) (hy : Derives Γ (graph e w env y)) :
    Derives Γ (uniqueValue e w env y) := by
  apply Derives.allI
  apply Derives.impI
  let U := graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn U)
  have hy1 : Derives Δ (graph e w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq (graph_rename e w y env Fin.castSucc) (under hy U)
  exact HornExprUnique.unique (ZFContext.under hZ U) e w.castSucc (Fin.last m) y.castSucc (fun i => (env i).castSucc) hw1 hn1 (.hyp (Or.inl rfl)) hy1

theorem actual_fiber {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (e : Expr n) (w : Fin m) (env : Fin n → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env)) : Derives Γ (fiber e w env) := by
  have he := HornExprExistence.exists_value hZ e w env hw hn
  let V := (Formula.mem (Fin.last m) w.castSucc).conj (graph e w.castSucc (fun i => (env i).castSucc) (Fin.last m))
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hu := unique_value (ZFContext.under hZ V) e w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 (.conjR hV)
  have ho : Derives Δ (fiber e w.castSucc (fun i => (env i).castSucc)) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, uniqueValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hV) (.conjI (.conjL hV) hu))
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

end PPAC.Migration.Internal.HornExprValue
