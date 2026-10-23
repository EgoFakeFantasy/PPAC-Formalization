import PPAC.Migration.Internal.HornExprForest

/-! 实际上游node表达式与原精确字段构造器对任意内部候选双向对应。 -/
namespace PPAC.Migration.Internal.HornExprConstructor
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem output_subst {m} {Γ : Context m} (k tag : Nat) (w y z : Fin m) (xs : Fin k → Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs y)) :
    Derives Γ (SyntaxNodeSyntax.constructor k tag w xs z) := by
  let P := SyntaxNodeSyntax.constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)
  have h0 : P.instantiate y = SyntaxNodeSyntax.constructor k tag w xs y := by simp only [P, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = SyntaxNodeSyntax.constructor k tag w xs z := by simp only [P, Formula.instantiate, SyntaxNodeSyntax.constructor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

theorem constructor_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (exprs : Fin k → Expr n)
    (w y : Fin m) (env : Fin n → Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat n w env))
    (hs : ∀ i, Derives Γ (graph (exprs i) w env (xs i))) :
    Derives Γ ((graph (Expr.node (.literal tag) (List.ofFn exprs)) w env y).iff (SyntaxNodeSyntax.constructor k tag w xs y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (Expr.node (.literal tag) (List.ofFn exprs)) w env y
    have hi := SyntaxForestSyntax.intro_inputs k w xs (fun i => HornExprRange.range hZ (exprs i) w (xs i) env hw hn (hs i))
    have he := SyntaxConstructors.exists_constructor (ZFContext.add hZ E) k tag w xs (add hw E) (add hi E)
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.constructor k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := R) he
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp E) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hn1 := of_eq (environmentNat_rename n w env Fin.castSucc) (lift hn)
    have hs1 (i : Fin k) := of_eq (graph_rename (exprs i) w (xs i) env Fin.castSucc) (lift (hs i))
    have hy1 : Derives Δ (graph (Expr.node (.literal tag) (List.ofFn exprs)) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq
      (graph_rename _ w y env Fin.castSucc) (under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) R)
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have heq := HornExprUnique.unique (ZFContext.under (ZFContext.add hZ E) R) _ w.castSucc y.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1 hy1
      (HornExprForest.constructor_graph k tag exprs _ _ _ _ hs1 (.conjR hR))
    exact of_eq (SyntaxNodeSyntax.constructor_rename k tag w xs y Fin.castSucc).symm (output_subst k tag _ _ _ _ (eq_symm heq) (.conjR hR))
  · apply Derives.impI
    exact HornExprForest.constructor_graph k tag exprs _ _ _ _ (fun i => add (hs i) _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.HornExprConstructor
