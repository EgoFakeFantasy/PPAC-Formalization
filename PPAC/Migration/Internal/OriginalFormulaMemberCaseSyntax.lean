import PPAC.Migration.Internal.OriginalFormulaMemberApplication

/-! 纯成员原子的实际应用分支：内部编号0、两参数森林与真实原列表子运行。 -/
namespace PPAC.Migration.Internal.OriginalFormulaMemberCaseSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {m} (w mode depth parameter x y q : Fin m) : Formula (m+3) :=
  (SyntaxNumeralSyntax.numeral 0 (slot 3 0)).conj
    ((SyntaxForestSyntax.forest 2 (old 3 w) (SyntaxAtomSyntax.two (old 3 x) (old 3 y)) (slot 3 1)).conj
      ((OriginalFormulaApplicationSyntax.application (old 3 w) (slot 3 0) (slot 3 2) (old 3 q)).conj
        (OriginalTransformRowSyntax.run 2 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (slot 3 1) (slot 3 2))))

def membershipCase {m} (w mode depth parameter x y q : Fin m) : Formula m := existsMany 3 (body w mode depth parameter x y q)

theorem body_lift {m j} (w mode depth parameter x y q : Fin m) (ρ : Fin m → Fin j) :
    (body w mode depth parameter x y q).rename (lift 3 ρ) = body (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ x) (ρ y) (ρ q) := by
  simp only [body, Formula.rename, SyntaxNumeralSyntax.numeral_rename, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map, OriginalFormulaApplicationSyntax.application_rename, OriginalTransformRowSyntax.run_rename, lift_old, lift_slot]

theorem membershipCase_rename {m j} (w mode depth parameter x y q : Fin m) (ρ : Fin m → Fin j) :
    (membershipCase w mode depth parameter x y q).rename ρ = membershipCase (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ x) (ρ y) (ρ q) := by
  simp only [membershipCase, existsMany_rename, body_lift]

theorem intro_case {m} {Γ : Context m} (w mode depth parameter x y q zero args newArgs : Fin m)
    (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 zero))
    (hf : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) args))
    (ha : Derives Γ (OriginalFormulaApplicationSyntax.application w zero newArgs q))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter args newArgs)) :
    Derives Γ (membershipCase w mode depth parameter x y q) := by
  apply HornBinderRules.intro_many 3 (body w mode depth parameter x y q) (OriginalLookupExpr.rowFields zero args newArgs)
  exact of_eq (by simp only [body, Formula.rename, SyntaxNumeralSyntax.numeral_rename, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map, OriginalFormulaApplicationSyntax.application_rename, OriginalTransformRowSyntax.run_rename, assign_old, assign_slot]; rfl) (.conjI hz (.conjI hf (.conjI ha hr)))

end PPAC.Migration.Internal.OriginalFormulaMemberCaseSyntax
