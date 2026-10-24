import PPAC.Migration.Internal.ProofTreeNodeTag

/-! 原各child位置的递归前提精确化为实际Node入口；全部内部候选与原顺序保留。 -/
namespace PPAC.Migration.Internal.ProofTreeChildren
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)

def children {m a} (test : Formula 1) : List (Fin a) → Fin m → (Fin a → Fin m) → Formula m
  | .nil, _, _ => HornRuleSyntax.truth
  | .cons i is, w, env => (ProofTreeEntrySyntax.node test w (env i)).conj (children test is w env)

theorem children_rename {m a l} (test : Formula 1) (is : List (Fin a)) (w : Fin m) (env : Fin a → Fin m) (ρ : Fin m → Fin l) :
    (children test is w env).rename ρ = children test is (ρ w) (fun i => ρ (env i)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [children, Formula.rename, ProofTreeEntryFacts.node_rename, ih]

theorem variable_premise_iff {m a} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ)
    (i : Fin a) (w : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((ProofTreeTracedStep.premise test (.node (.literal 0) [.var i]) w env).iff (ProofTreeEntrySyntax.node test w (env i))) :=
  ProofTreeTraceQuery.constructor_query_iff test hZ 1 0 (fun _ => .var i) w env (fun _ => env i) hw hn
    (fun _ => .conjI (environmentNat_at w env hn i) (.eqRefl _))

theorem children_iff {m a} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ)
    (is : List (Fin a)) (w : Fin m) (env : Fin a → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((ProofTreeTracedStep.premises test (is.map (fun i => .node (.literal 0) [.var i])) w env).iff (children test is w env)) := by
  induction is with
  | nil => exact SyntaxTypeLocalTransfer.iff_refl _
  | cons i is ih => exact FormulaCodeCongruence.conj_congr (variable_premise_iff test hZ i w env hw hn) ih

theorem child_at {m a} {Γ : Context m} (test : Formula 1) (is : List (Fin a)) (i : Fin a) (hi : i ∈ is)
    (w : Fin m) (env : Fin a → Fin m) (hc : Derives Γ (children test is w env)) :
    Derives Γ (ProofTreeEntrySyntax.node test w (env i)) := by
  induction is with
  | nil => simp only [List.not_mem_nil] at hi
  | cons j is ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact .conjL hc
    · exact ih hi (.conjR hc)

end PPAC.Migration.Internal.ProofTreeChildren
