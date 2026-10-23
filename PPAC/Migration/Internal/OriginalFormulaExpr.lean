import PPAC.Migration.Internal.OriginalFormulaApplicationExpr

/-! 原十一公式族head与全部内部输入／输出候选的精确数值构造关系。 -/
namespace PPAC.Migration.Internal.OriginalFormulaExpr
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (constant binary unary row)

def constantFields (tag : Nat) : Fin 5 → Expr 3 := OriginalFormulaRowGraph.fields 0 1 2 (Expr.node (.literal tag) []) (Expr.node (.literal tag) [])

def binaryFields (tag : Nat) : Fin 5 → Expr 7 := OriginalFormulaRowGraph.fields 0 1 2 (Expr.node (.literal tag) [.var 3,.var 4]) (Expr.node (.literal tag) [.var 5,.var 6])

def unaryFields (tag : Nat) : Fin 5 → Expr 5 := OriginalFormulaRowGraph.fields 0 1 2 (Expr.node (.literal tag) [.var 3]) (Expr.node (.literal tag) [.var 4])

def applicationFields : Fin 5 → Expr 6 := OriginalFormulaRowGraph.fields 0 1 2 (OriginalFormulaApplicationSyntax.expr 3 4) (OriginalFormulaApplicationSyntax.expr 3 5)

def binaryLeft (kind : Nat) : Expr 7 := row kind (.var 0) (.var 1) (.var 2) (.var 3) (.var 5)
def binaryRight (kind : Nat) : Expr 7 := row kind (.var 0) (.var 1) (.var 2) (.var 4) (.var 6)
def unaryChild (binder : Bool) : Expr 5 := row 3 (.var 0) (if binder then .succ (.var 1) else .var 1) (.var 2) (.var 3) (.var 4)
def applicationChild : Expr 6 := row 2 (.var 0) (.var 1) (.var 2) (.var 4) (.var 5)

theorem actual_constant_head (tag : Nat) : (constant tag).head = Expr.node (.literal 3) (List.ofFn (constantFields tag)) := rfl
theorem actual_binary_head (tag kind : Nat) : (binary tag kind).head = Expr.node (.literal 3) (List.ofFn (binaryFields tag)) := rfl
theorem actual_unary_head (tag : Nat) (binder : Bool) : (unary tag binder).head = Expr.node (.literal 3) (List.ofFn (unaryFields tag)) := rfl
theorem actual_application_head : (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3).head = Expr.node (.literal 3) (List.ofFn applicationFields) := rfl

theorem actual_binary_premises (tag kind : Nat) : (binary tag kind).premises = [binaryLeft kind,binaryRight kind] := rfl
theorem actual_unary_premises (tag : Nat) (binder : Bool) : (unary tag binder).premises = [unaryChild binder] := rfl
theorem actual_application_premises : (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3).premises = [applicationChild] := rfl

theorem empty_node_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w n : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (Expr.node (.literal tag) []) w env n).iff (SyntaxNodeSyntax.constructor 0 tag w Fin.elim0 n)) := by
  simpa only [List.ofFn_zero] using HornExprConstructor.constructor_iff hZ 0 tag Fin.elim0 w n env Fin.elim0 hw hn (fun i => Fin.elim0 i)

theorem one_node_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (i : Fin a) (w n : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (Expr.node (.literal tag) [.var i]) w env n).iff (SyntaxNodeSyntax.constructor 1 tag w (fun _ => env i) n)) := by
  have hv : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  simpa only [List.ofFn_succ, List.ofFn_zero] using HornExprConstructor.constructor_iff hZ 1 tag (fun _ => Expr.var i) w n env (fun _ => env i) hw hn (fun _ => hv)

def twoExpr {a} (i j : Fin a) : Fin 2 → Expr a := Fin.cases (.var i) (Fin.cases (.var j) Fin.elim0)

theorem two_node_iff {m a} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (i j : Fin a) (w n : Fin m) (env : Fin a → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat a w env)) :
    Derives Γ ((graph (Expr.node (.literal tag) [.var i,.var j]) w env n).iff (SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two (env i) (env j)) n)) := by
  have hv (k : Fin a) : Derives Γ (graph (.var k) w env (env k)) := .conjI (environmentNat_at w env hn k) (.eqRefl _)
  have hs : ∀ k : Fin 2, Derives Γ (graph ((twoExpr i j) k) w env (SyntaxAtomSyntax.two (env i) (env j) k)) := fun k => Fin.cases (hv i) (Fin.cases (hv j) (fun z => Fin.elim0 z)) k
  simpa only [List.ofFn_succ, List.ofFn_zero, twoExpr, SyntaxAtomSyntax.two, Fin.cases_zero, Fin.cases_succ] using HornExprConstructor.constructor_iff hZ 2 tag ((twoExpr i j)) w n env (SyntaxAtomSyntax.two (env i) (env j)) hw hn hs

theorem constant_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((graph (constant tag).head w env r).iff ((SyntaxNodeSyntax.constructor 0 tag w Fin.elim0 n).conj (SyntaxNodeSyntax.constructor 0 tag w Fin.elim0 q))) := by
  rw [actual_constant_head tag]
  exact SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRowGraph.graph_at_row hZ 3 0 1 2 (Expr.node (.literal tag) []) (Expr.node (.literal tag) []) w n q r env hw hn hc)
    (FormulaCodeCongruence.conj_congr (empty_node_iff hZ tag w n env hw hn) (empty_node_iff hZ tag w q env hw hn))

theorem binary_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind : Nat) (w n q r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((graph (binary tag kind).head w env r).iff ((SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two (env 3) (env 4)) n).conj (SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two (env 5) (env 6)) q))) := by
  rw [actual_binary_head tag kind]
  exact SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRowGraph.graph_at_row hZ 3 0 1 2 (Expr.node (.literal tag) [.var 3,.var 4]) (Expr.node (.literal tag) [.var 5,.var 6]) w n q r env hw hn hc)
    (FormulaCodeCongruence.conj_congr (two_node_iff hZ tag 3 4 w n env hw hn) (two_node_iff hZ tag 5 6 w q env hw hn))

theorem unary_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (binder : Bool) (w n q r : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((graph (unary tag binder).head w env r).iff ((SyntaxNodeSyntax.constructor 1 tag w (fun _ => env 3) n).conj (SyntaxNodeSyntax.constructor 1 tag w (fun _ => env 4) q))) := by
  rw [actual_unary_head tag binder]
  exact SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRowGraph.graph_at_row hZ 3 0 1 2 (Expr.node (.literal tag) [.var 3]) (Expr.node (.literal tag) [.var 4]) w n q r env hw hn hc)
    (FormulaCodeCongruence.conj_congr (one_node_iff hZ tag 3 w n env hw hn) (one_node_iff hZ tag 4 w q env hw hn))

theorem application_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)  (w n q r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((graph (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3).head w env r).iff ((OriginalFormulaApplicationSyntax.application w (env 3) (env 4) n).conj (OriginalFormulaApplicationSyntax.application w (env 3) (env 5) q))) := by
  rw [actual_application_head ]
  exact SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaRowGraph.graph_at_row hZ 3 0 1 2 (OriginalFormulaApplicationSyntax.expr 3 4) (OriginalFormulaApplicationSyntax.expr 3 5) w n q r env hw hn hc)
    (FormulaCodeCongruence.conj_congr (OriginalFormulaApplicationExpr.application_iff hZ 3 4 w n env hw hn) (OriginalFormulaApplicationExpr.application_iff hZ 3 5 w q env hw hn))

end PPAC.Migration.Internal.OriginalFormulaExpr
