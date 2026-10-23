import PPAC.Migration.Internal.HornNodeFields
import PPAC.Migration.Internal.OriginalFormulaScalarExpr
import PPAC.Migration.Internal.PureSyntaxTraceRules

/-! 原纯变量检查规则的实际输入表达式与原变量码双条件；不预给字段或编码值。 -/
namespace PPAC.Migration.Internal.PureSyntaxVariableExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def variableExpr {n} (bound : Bool) (i : Fin n) : Expr n :=
  Expr.node (.literal (SyntaxVariableSyntax.tag bound)) [Expr.node (.var i) []]

def fields (bound : Bool) : Fin 3 → Expr 3 :=
  Fin.cases (.var 0) (Fin.cases (.var 1) (Fin.cases (variableExpr bound 2) Fin.elim0))

theorem actual_head (bound : Bool) :
    (YesMetaZFC.Automation.ObjectTermSyntax.variableRule (!bound)).head =
      Expr.node (.literal 0) (List.ofFn (fields bound)) := by cases bound <;> rfl

theorem actual_guards (bound : Bool) :
    (YesMetaZFC.Automation.ObjectTermSyntax.variableRule (!bound)).guards =
      [(.var (2 : Fin 3), .var (if bound then (0 : Fin 3) else (1 : Fin 3)))] := by cases bound <;> rfl

theorem variable_iff {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (i : Fin n)
    (w y : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat n w env)) :
    Derives Γ ((graph (variableExpr bound i) w env y).iff (SyntaxVariableSyntax.code bound w (env i) y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := graph (variableExpr bound i) w env y
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.scalar w.castSucc (env i).castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (SyntaxNodes.exists_node (ZFContext.add hZ E) 0 w (env i) Fin.elim0 (add hw E) (add (environmentNat_at w env hn i) E) (.eqRefl _))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun j => (env j).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under (add hn E) B)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hg1 : Derives Δ (graph (variableExpr bound i) w.castSucc (fun j => (env j).castSucc) y.castSucc) := of_eq (graph_rename _ w y env Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := OriginalFormulaScalarExpr.scalar_graph i w.castSucc (Fin.last m) (fun j => (env j).castSucc) hn1 (.conjR hB)
    have hc := Derives.impE (.conjL (HornExprConstructor.constructor_iff hZ1 1 (SyntaxVariableSyntax.tag bound) (fun _ : Fin 1 => Expr.node (.var i) []) w.castSucc y.castSucc (fun j => (env j).castSucc) (fun _ => Fin.last m) hw1 hn1 (fun _ => hs))) hg1
    have ht := SyntaxVariableSyntax.intro_code bound w.castSucc (env i).castSucc y.castSucc (Fin.last m) (.conjR hB) hc
    exact of_eq (SyntaxVariableSyntax.code_rename bound w (env i) y Fin.castSucc).symm ht
  · apply Derives.impI
    let E := SyntaxVariableSyntax.code bound w (env i) y
    let B := SyntaxVariableSyntax.codeBody bound w (env i) y
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxVariableSyntax.eliminate_code bound w (env i) y _ (.hyp (Or.inl rfl))
    have hn1 : Derives Δ (environmentNat n w.castSucc (fun j => (env j).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under (add hn E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := OriginalFormulaScalarExpr.scalar_graph i w.castSucc (Fin.last m) (fun j => (env j).castSucc) hn1 (.conjL hB)
    have ht : Derives Δ (graph (variableExpr bound i) w.castSucc (fun j => (env j).castSucc) y.castSucc) :=
      HornExprForest.constructor_graph 1 (SyntaxVariableSyntax.tag bound) (fun _ : Fin 1 => Expr.node (.var i) []) w.castSucc y.castSucc (fun j => (env j).castSucc) (fun _ => Fin.last m) (fun _ => hs) (.conjR hB)
    exact of_eq (by simp only [Formula.raise, graph_rename]) ht

end PPAC.Migration.Internal.PureSyntaxVariableExpr
