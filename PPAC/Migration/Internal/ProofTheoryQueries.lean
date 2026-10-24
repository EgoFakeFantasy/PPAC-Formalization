import PPAC.Migration.Internal.ProofTheorySyntax

/-! theoryShape的准确语法与对象公理测试接口；未引入公理测试正确性假设。 -/
namespace PPAC.Migration.Internal.ProofTheoryQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax ProofTheorySyntax
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem head_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((graph ObjectProofNode.theoryShape.head w env row).iff (SyntaxNodeSyntax.constructor 3 1 w env row)) :=
  HornExprConstructor.constructor_iff hZ 3 1 (fun i : Fin 3 => Expr.var i) w row env env hw hn
    (fun i => .conjI (environmentNat_at w env hn i) (.eqRefl _))

theorem formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxExprQuery.query formulaExpr w env).iff (FormulaCodeSyntax.formulaCode w (env 1) z (env 0))) :=
  LogicalStaticQueries.query_iff hZ false (0 : Fin 3) 1 w z env hw hn hz

theorem axiom_constructor_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((OriginalAxiomExprQuery.query test axiomExpr w env).iff (OriginalAxiomExprQuery.rowQuery test 2 0 w (axiomFields env))) := by
  let es : Fin 2 → Expr 3 := Fin.cases (.var 2) (Fin.cases (.var 1) Fin.elim0)
  have he : axiomExpr = Expr.node (.literal 0) (List.ofFn es) := rfl
  rw [he]
  apply OriginalAxiomExprQuery.constructor_query_iff test hZ 2 0 es w env (axiomFields env) hw hn
  intro i
  refine Fin.cases (.conjI (environmentNat_at w env hn 2) (.eqRefl _)) (fun j => ?_) i
  exact Fin.cases (.conjI (environmentNat_at w env hn 1) (.eqRefl _)) (fun q => Fin.elim0 q) j

theorem bundle_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w z : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((bundle test w env).iff (specification test w z env)) :=
  FormulaCodeCongruence.conj_congr (formula_iff hZ w z env hw hn hz) (axiom_constructor_iff test hZ w env hw hn)

theorem all_assignment_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph ObjectProofNode.theoryShape.head w env row)) : Derives Γ (HornExprBounds.environmentBound 3 row env) := by
  have hVars : ∀ i, i ∈ ObjectProofNode.theoryShape.head.variables := by decide
  exact HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ ObjectProofNode.theoryShape.head i (hVars i) w row env hw hn hh)

end PPAC.Migration.Internal.ProofTheoryQueries
