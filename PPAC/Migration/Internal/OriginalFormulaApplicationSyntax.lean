import PPAC.Migration.Internal.OriginalFormulaScalarExpr

/-! 原关系应用的纯数值结构：符号零字段码、实际Cons载荷及实际标签2节点。 -/
namespace PPAC.Migration.Internal.OriginalFormulaApplicationSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)

def expr {a} (i j : Fin a) : Expr a := YesMetaZFC.Automation.ObjectSyntaxTransform.rawNode 2
  (YesMetaZFC.Automation.ObjectSyntaxTransform.cons (Expr.node (.var i) []) (.var j))

def body {m} (w symbol args n : Fin m) : Formula (m+3) :=
  (SyntaxNodeSyntax.scalar (old 3 w) (old 3 symbol) (slot 3 0)).conj
    ((StructuralListSyntax.consCode (old 3 w) (slot 3 0) (old 3 args) (slot 3 1)).conj
      ((SyntaxNumeralSyntax.numeral 2 (slot 3 2)).conj (StructuralNodeSyntax.raw (old 3 w) (slot 3 2) (slot 3 1) (old 3 n))))

def application {m} (w symbol args n : Fin m) : Formula m := existsMany 3 (body w symbol args n)

theorem body_lift {m j} (w symbol args n : Fin m) (ρ : Fin m → Fin j) :
    (body w symbol args n).rename (lift 3 ρ) = body (ρ w) (ρ symbol) (ρ args) (ρ n) := by
  simp only [body, Formula.rename, SyntaxNodeSyntax.scalar_rename, StructuralListSyntax.consCode_rename, SyntaxNumeralSyntax.numeral_rename, StructuralNodeSyntax.raw_rename, lift_old, lift_slot]

theorem application_rename {m j} (w symbol args n : Fin m) (ρ : Fin m → Fin j) :
    (application w symbol args n).rename ρ = application (ρ w) (ρ symbol) (ρ args) (ρ n) := by
  simp only [application, existsMany_rename, body_lift]

theorem intro_application {m} {Γ : Context m} (w symbol args n s p two : Fin m)
    (hs : Derives Γ (SyntaxNodeSyntax.scalar w symbol s))
    (hp : Derives Γ (StructuralListSyntax.consCode w s args p))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 two))
    (hn : Derives Γ (StructuralNodeSyntax.raw w two p n)) : Derives Γ (application w symbol args n) := by
  let env : Fin 3 → Fin m := OriginalLookupExpr.rowFields s p two
  apply HornBinderRules.intro_many 3 (body w symbol args n) env
  exact of_eq (by simp only [body, Formula.rename, SyntaxNodeSyntax.scalar_rename, StructuralListSyntax.consCode_rename, SyntaxNumeralSyntax.numeral_rename, StructuralNodeSyntax.raw_rename, assign_old, assign_slot]; rfl) (.conjI hs (.conjI hp (.conjI ht hn)))

end PPAC.Migration.Internal.OriginalFormulaApplicationSyntax
