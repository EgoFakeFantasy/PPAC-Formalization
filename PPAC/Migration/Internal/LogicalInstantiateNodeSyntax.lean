import PPAC.Migration.Internal.LogicalRule20Head
import PPAC.Migration.Internal.LogicalRule23Head
import PPAC.Migration.Internal.LogicalRule25Head

/-! 原逻辑20／23／25的准确有界纯关系节点与独立数值头规格；接受式不含类型或操作规格。 -/
namespace PPAC.Migration.Internal.LogicalInstantiateNodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Expr)

def head4 (universal : Bool) : Expr 4 := if universal then ObjectLogicalAxiom.rule20.head else ObjectLogicalAxiom.rule23.head

def head6 : Expr 6 := ObjectLogicalAxiom.rule25.head

def normalizedHead4 {m} (universal : Bool) (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  if universal then LogicalRule20Head.normalized w row env else LogicalRule23Head.normalized w row env

def normalizedHead6 {m} (w row : Fin m) (env : Fin 6 → Fin m) : Formula m := LogicalRule25Head.normalized w row env

theorem actual_rule20_arity : ObjectLogicalAxiom.rule20.arity = 4 := rfl

theorem actual_rule23_arity : ObjectLogicalAxiom.rule23.arity = 4 := rfl

theorem actual_rule25_arity : ObjectLogicalAxiom.rule25.arity = 6 := rfl

theorem actual_rule20_queries : ObjectLogicalAxiom.rule20.queries =
    [(false, LogicalInstantiateSyntax.formula4), (false, LogicalInstantiateSyntax.term4), (true, LogicalInstantiateSyntax.transform4)] := rfl

theorem actual_rule23_queries : ObjectLogicalAxiom.rule23.queries = ObjectLogicalAxiom.rule20.queries := rfl

theorem actual_rule25_queries : ObjectLogicalAxiom.rule25.queries =
    [(false, LogicalInstantiateSyntax.leftTerm6), (false, LogicalInstantiateSyntax.rightTerm6), (false, LogicalInstantiateSyntax.formula6),
     (true, LogicalInstantiateSyntax.leftTransform6), (true, LogicalInstantiateSyntax.rightTransform6)] := rfl

theorem actual_head20 : head4 true = ObjectLogicalAxiom.rule20.head := rfl

theorem actual_head23 : head4 false = ObjectLogicalAxiom.rule23.head := rfl

theorem actual_head25 : head6 = ObjectLogicalAxiom.rule25.head := rfl

def queryMatrix4 {m} (universal : Bool) (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (graph (head4 universal) w env row).conj (LogicalInstantiateSyntax.bundle4 w env)

def boundedMatrix4 {m} (universal : Bool) (w row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((HornExprBounds.environmentBound 4 row env).conj (queryMatrix4 universal w row env))

def specificationMatrix4 {m} (universal : Bool) (w z row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((graph (head4 universal) w env row).conj (LogicalInstantiateSyntax.specification4 w z env))

def normalizedMatrix4 {m} (universal : Bool) (w z row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((normalizedHead4 universal w row env).conj (LogicalInstantiateSyntax.specification4 w z env))

def body4 {m} (universal : Bool) (w row : Fin m) : Formula (m+4) := boundedMatrix4 universal (old 4 w) (old 4 row) (slot 4)

def specificationBody4 {m} (universal : Bool) (w z row : Fin m) : Formula (m+4) := specificationMatrix4 universal (old 4 w) (old 4 z) (old 4 row) (slot 4)

def normalizedBody4 {m} (universal : Bool) (w z row : Fin m) : Formula (m+4) := normalizedMatrix4 universal (old 4 w) (old 4 z) (old 4 row) (slot 4)

def node4 {m} (universal : Bool) (w row : Fin m) : Formula m := existsMany 4 (body4 universal w row)

def specification4 {m} (universal : Bool) (w z row : Fin m) : Formula m := existsMany 4 (specificationBody4 universal w z row)

def normalized4 {m} (universal : Bool) (w z row : Fin m) : Formula m := existsMany 4 (normalizedBody4 universal w z row)

theorem head4_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hh : Derives Γ (graph (head4 universal) w env row)) : Derives Γ (HornExprBounds.environmentBound 4 row env) := by
  have hVars : ∀ i : Fin 4, i ∈ (head4 universal).variables := by cases universal <;> decide
  exact HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ (head4 universal) i (hVars i) w row env hw hn hh)

theorem head4_normalized_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((graph (head4 universal) w env row).iff (normalizedHead4 universal w row env)) := by
  cases universal with
  | false => exact LogicalRule23Head.head_iff hZ w row env hw hn
  | true => exact LogicalRule20Head.head_iff hZ w row env hw hn

def queryMatrix6 {m} (w row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (graph (head6) w env row).conj (LogicalInstantiateSyntax.bundle6 w env)

def boundedMatrix6 {m} (w row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (environmentNat 6 w env).conj ((HornExprBounds.environmentBound 6 row env).conj (queryMatrix6 w row env))

def specificationMatrix6 {m} (w z row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (environmentNat 6 w env).conj ((graph (head6) w env row).conj (LogicalInstantiateSyntax.specification6 w z env))

def normalizedMatrix6 {m} (w z row : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (environmentNat 6 w env).conj ((normalizedHead6 w row env).conj (LogicalInstantiateSyntax.specification6 w z env))

def body6 {m} (w row : Fin m) : Formula (m+6) := boundedMatrix6 (old 6 w) (old 6 row) (slot 6)

def specificationBody6 {m} (w z row : Fin m) : Formula (m+6) := specificationMatrix6 (old 6 w) (old 6 z) (old 6 row) (slot 6)

def normalizedBody6 {m} (w z row : Fin m) : Formula (m+6) := normalizedMatrix6 (old 6 w) (old 6 z) (old 6 row) (slot 6)

def node6 {m} (w row : Fin m) : Formula m := existsMany 6 (body6 w row)

def specification6 {m} (w z row : Fin m) : Formula m := existsMany 6 (specificationBody6 w z row)

def normalized6 {m} (w z row : Fin m) : Formula m := existsMany 6 (normalizedBody6 w z row)

theorem head6_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hh : Derives Γ (graph (head6) w env row)) : Derives Γ (HornExprBounds.environmentBound 6 row env) := by
  have hVars : ∀ i : Fin 6, i ∈ (head6).variables := by decide
  exact HornExprBounds.intro_environmentBound row env (fun i => HornExprBounds.variable_bound hZ (head6) i (hVars i) w row env hw hn hh)

theorem head6_normalized_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w row : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env)) :
    Derives Γ ((graph (head6) w env row).iff (normalizedHead6 w row env)) := by
  exact LogicalRule25Head.head_iff hZ w row env hw hn

end PPAC.Migration.Internal.LogicalInstantiateNodeSyntax
