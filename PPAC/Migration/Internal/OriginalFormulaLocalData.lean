import PPAC.Migration.Internal.OriginalFormulaChildren

/-! 原十一公式族的纯数值局部数据；所有实际子运行保留原完整轨迹定义。 -/
namespace PPAC.Migration.Internal.OriginalFormulaLocalData
open Source SourceAlgebra SourceLogic

def constant {m} (tag : Nat) (w n q : Fin m) : Formula m :=
  (SyntaxNodeSyntax.constructor 0 tag w Fin.elim0 n).conj (SyntaxNodeSyntax.constructor 0 tag w Fin.elim0 q)

def binary {m} (tag kind : Nat) (w mode depth parameter n q x y X Y : Fin m) : Formula m :=
  ((SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two x y) n).conj
    (SyntaxNodeSyntax.constructor 2 tag w (SyntaxAtomSyntax.two X Y) q)).conj
      ((OriginalTransformRowSyntax.run kind w mode depth parameter x X).conj (OriginalTransformRowSyntax.run kind w mode depth parameter y Y))

def unary {m} (tag : Nat) (w mode childDepth parameter n q x X : Fin m) : Formula m :=
  ((SyntaxNodeSyntax.constructor 1 tag w (fun _ => x) n).conj (SyntaxNodeSyntax.constructor 1 tag w (fun _ => X) q)).conj
    (OriginalTransformRowSyntax.run 3 w mode childDepth parameter x X)

def application {m} (w mode depth parameter n q symbol args newArgs : Fin m) : Formula m :=
  ((OriginalFormulaApplicationSyntax.application w symbol args n).conj (OriginalFormulaApplicationSyntax.application w symbol newArgs q)).conj
    (OriginalTransformRowSyntax.run 2 w mode depth parameter args newArgs)

theorem constant_rename {m j} (tag : Nat) (w n q : Fin m) (ρ : Fin m → Fin j) :
    (constant tag w n q).rename ρ = constant tag (ρ w) (ρ n) (ρ q) := by
  simp only [constant, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map]

theorem binary_rename {m j} (tag kind : Nat) (w mode depth parameter n q x y X Y : Fin m) (ρ : Fin m → Fin j) :
    (binary tag kind w mode depth parameter n q x y X Y).rename ρ = binary tag kind (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [binary, Formula.rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map, OriginalTransformRowSyntax.run_rename]

theorem unary_rename {m j} (tag : Nat) (w mode childDepth parameter n q x X : Fin m) (ρ : Fin m → Fin j) :
    (unary tag w mode childDepth parameter n q x X).rename ρ = unary tag (ρ w) (ρ mode) (ρ childDepth) (ρ parameter) (ρ n) (ρ q) (ρ x) (ρ X) := by
  simp only [unary, Formula.rename, SyntaxNodeSyntax.constructor_rename, OriginalTransformRowSyntax.run_rename]

theorem application_rename {m j} (w mode depth parameter n q symbol args newArgs : Fin m) (ρ : Fin m → Fin j) :
    (application w mode depth parameter n q symbol args newArgs).rename ρ = application (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) (ρ symbol) (ρ args) (ρ newArgs) := by
  simp only [application, Formula.rename, OriginalFormulaApplicationSyntax.application_rename, OriginalTransformRowSyntax.run_rename]

end PPAC.Migration.Internal.OriginalFormulaLocalData
