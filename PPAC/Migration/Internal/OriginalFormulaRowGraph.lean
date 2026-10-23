import PPAC.Migration.Internal.OriginalFormulaDispatch

/-! 任意原kind五字段行在真实候选行上消去头图；元数据、输入、输出均内部对象。 -/
namespace PPAC.Migration.Internal.OriginalFormulaRowGraph
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def fields {a} (j0 j1 j2 : Fin a) (e f : Expr a) : Fin 5 → Expr a :=
  HornRowFields.five (.var j0) (.var j1) (.var j2) e f

theorem graph_at_row {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (j0 j1 j2 : Fin a) (e f : Expr a) (w n q r : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row kind w (env j0) (env j1) (env j2) n q r)) :
    Derives Γ ((graph (Expr.node (.literal kind) (List.ofFn (fields j0 j1 j2 e f))) w env r).iff
      ((graph e w env n).conj (graph f w env q))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (Expr.node (.literal kind) (List.ofFn (fields j0 j1 j2 e f))) w env r
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have h3 := HornRowFields.field_graph (ZFContext.add hZ E) kind (fields j0 j1 j2 e f) w r env (HornRowFields.five (env j0) (env j1) (env j2) n q) 3 (add hw E) (add hn E) hE (add hc E)
    have h4 := HornRowFields.field_graph (ZFContext.add hZ E) kind (fields j0 j1 j2 e f) w r env (HornRowFields.five (env j0) (env j1) (env j2) n q) 4 (add hw E) (add hn E) hE (add hc E)
    exact .conjI h3 h4
  · apply Derives.impI
    let E := (graph e w env n).conj (graph f w env q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hv (i : Fin a) : Derives (Context.add E Γ) (graph (.var i) w env (env i)) := .conjI (add (environmentNat_at w env hn i) E) (.eqRefl _)
    have hs : ∀ i, Derives (Context.add E Γ) (graph ((fields j0 j1 j2 e f) i) w env (HornRowFields.five (env j0) (env j1) (env j2) n q i)) :=
      fun i => Fin.cases (hv j0) (fun a => Fin.cases (hv j1) (fun b => Fin.cases (hv j2) (fun c => Fin.cases (.conjL hE) (fun _ => .conjR hE) c) b) a) i
    exact .impE (.conjR (HornExprConstructor.constructor_iff (ZFContext.add hZ E) 5 kind (fields j0 j1 j2 e f) w r env _ (add hw E) (add hn E) hs)) (add hc E)

theorem metadata_eq {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (j0 j1 j2 : Fin a) (e f : Expr a) (w mode depth parameter n q r : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env))
    (hh : Derives Γ (graph (Expr.node (.literal kind) (List.ofFn (fields j0 j1 j2 e f))) w env r))
    (hc : Derives Γ (OriginalTransformRowSyntax.row kind w mode depth parameter n q r)) :
    Derives Γ ((Formula.equal mode (env j0)).conj ((Formula.equal depth (env j1)).conj (.equal parameter (env j2)))) := by
  have h0 := HornRowFields.field_graph hZ kind (fields j0 j1 j2 e f) w r env (HornRowFields.five mode depth parameter n q) 0 hw hn hh hc
  have h1 := HornRowFields.field_graph hZ kind (fields j0 j1 j2 e f) w r env (HornRowFields.five mode depth parameter n q) 1 hw hn hh hc
  have h2 := HornRowFields.field_graph hZ kind (fields j0 j1 j2 e f) w r env (HornRowFields.five mode depth parameter n q) 2 hw hn hh hc
  exact .conjI (.conjR h0) (.conjI (.conjR h1) (.conjR h2))

theorem variable_child_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (js : Fin 5 → Fin a) (w : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((HornUniversalTraceRules.tracedPremise (Expr.node (.literal kind) (List.ofFn (fun i => Expr.var (js i)))) w env).iff
      (OriginalTransformRowSyntax.run kind w (env (js 0)) (env (js 1)) (env (js 2)) (env (js 3)) (env (js 4)))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename a w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr
    (OriginalArgumentsExpr.variable_row_iff (ZFContext.rename hZ Fin.castSucc) kind js w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1)
    (SyntaxTypeLocalTransfer.iff_refl _)

end PPAC.Migration.Internal.OriginalFormulaRowGraph
