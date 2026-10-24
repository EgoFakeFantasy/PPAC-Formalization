import PPAC.Migration.Internal.LogicalStaticNodeSyntax

/-! 每个实际数值头证书实例化的完整静态逻辑节点双条件；对象前提仅Ω与empty。 -/
namespace PPAC.Migration.Internal.LogicalStaticNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax LogicalStaticNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

theorem head_bounds {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Expr (n+1))
    (hVars : ∀ i, i ∈ head.variables) (w row : Fin m) (env : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat (n+1) w env))
    (hh : Derives Γ (graph head w env row)) : Derives Γ (HornExprBounds.environmentBound (n+1) row env) :=
  HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ head i (hVars i) w row env hw hn hh)

theorem matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (n : Nat) (isTerm : Bool)
    (head : Expr (n+1)) (numeric : NumericHead n) (hVars : ∀ i, i ∈ head.variables)
    (hHead : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w row : Fin l) (env : Fin (n+1) → Fin l),
      Derives Δ (omega w) → Derives Δ (environmentNat (n+1) w env) → Derives Δ ((graph head w env row).iff (numeric w row env)))
    (w z row : Fin m) (env : Fin (n+1) → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix n isTerm head w row env).iff (normalizedMatrix n isTerm numeric w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix n isTerm head w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR (.conjR hE))
    have ht := Derives.impE (.conjL (LogicalStaticQueries.bundle_iff (ZFContext.add hZ E) n isTerm w z env (add hw E) hn (add hz E))) (.conjR (.conjR (.conjR hE)))
    have hc := Derives.impE (.conjL (hHead (ZFContext.add hZ E) w row env (add hw E) hn)) hh
    exact .conjI hn (.conjI hc ht)
  · apply Derives.impI
    let E := normalizedMatrix n isTerm numeric w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (hHead (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    have hb := head_bounds (ZFContext.add hZ E) head hVars w row env (add hw E) hn hh
    have hq := Derives.impE (.conjR (LogicalStaticQueries.bundle_iff (ZFContext.add hZ E) n isTerm w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    exact .conjI hn (.conjI hb (.conjI hh hq))

theorem normalized_node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (n : Nat) (isTerm : Bool)
    (head : Expr (n+1)) (numeric : NumericHead n) (hVars : ∀ i, i ∈ head.variables)
    (hHead : ∀ {l} {Δ : Context l}, ZFContext.Evidence Δ → ∀ (w row : Fin l) (env : Fin (n+1) → Fin l),
      Derives Δ (omega w) → Derives Δ (environmentNat (n+1) w env) → Derives Δ ((graph head w env row).iff (numeric w row env)))
    (w z row : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node n isTerm head w row).iff (normalized n isTerm numeric w z row)) := by
  apply HornApplicationBounds.existsMany_congr (n+1)
  have hwN := of_eq (omega_rename w (old (n+1))) (HornBinderRules.under_many (n+1) hw)
  have hzN := of_eq (empty_rename z (old (n+1))) (HornBinderRules.under_many (n+1) hz)
  exact matrix_iff (HornBinderRules.zf_many (n+1) hZ) n isTerm head numeric hVars hHead
    (old (n+1) w) (old (n+1) z) (old (n+1) row) (slot (n+1)) hwN hzN

end PPAC.Migration.Internal.LogicalStaticNode
