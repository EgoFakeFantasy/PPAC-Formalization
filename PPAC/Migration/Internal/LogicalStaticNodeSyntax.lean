import PPAC.Migration.Internal.LogicalStaticQueries

/-! 不含变换查询的原逻辑模式：独立接受式与数值头／类型规格。 -/
namespace PPAC.Migration.Internal.LogicalStaticNodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)

def NumericHead (n : Nat) : Type := ∀ {m : Nat}, Fin m → Fin m → (Fin (n+1) → Fin m) → Formula m

def queryMatrix {m} (n : Nat) (isTerm : Bool) (head : Expr (n+1)) (w row : Fin m) (env : Fin (n+1) → Fin m) : Formula m :=
  (graph head w env row).conj (LogicalStaticQueries.bundle n isTerm w env)

def boundedMatrix {m} (n : Nat) (isTerm : Bool) (head : Expr (n+1)) (w row : Fin m) (env : Fin (n+1) → Fin m) : Formula m :=
  (environmentNat (n+1) w env).conj ((HornExprBounds.environmentBound (n+1) row env).conj (queryMatrix n isTerm head w row env))

def normalizedMatrix {m} (n : Nat) (isTerm : Bool) (numeric : NumericHead n) (w z row : Fin m) (env : Fin (n+1) → Fin m) : Formula m :=
  (environmentNat (n+1) w env).conj ((numeric w row env).conj (LogicalStaticQueries.types n isTerm w z env))

def body {m} (n : Nat) (isTerm : Bool) (head : Expr (n+1)) (w row : Fin m) : Formula (m+(n+1)) :=
  boundedMatrix n isTerm head (old (n+1) w) (old (n+1) row) (slot (n+1))

def normalizedBody {m} (n : Nat) (isTerm : Bool) (numeric : NumericHead n) (w z row : Fin m) : Formula (m+(n+1)) :=
  normalizedMatrix n isTerm numeric (old (n+1) w) (old (n+1) z) (old (n+1) row) (slot (n+1))

def node {m} (n : Nat) (isTerm : Bool) (head : Expr (n+1)) (w row : Fin m) : Formula m :=
  existsMany (n+1) (body n isTerm head w row)

def normalized {m} (n : Nat) (isTerm : Bool) (numeric : NumericHead n) (w z row : Fin m) : Formula m :=
  existsMany (n+1) (normalizedBody n isTerm numeric w z row)

end PPAC.Migration.Internal.LogicalStaticNodeSyntax
