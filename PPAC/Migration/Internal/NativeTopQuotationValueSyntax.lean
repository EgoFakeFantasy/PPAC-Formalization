import PPAC.Migration.Internal.NativeTopQuotationOriginal

/-! 首槽操作、准确原生quotation及原目标FormulaCode在同一对象输出码上的联合唯一纤维。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationValueSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def instantiateValue {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q : Fin m) : Formula m := (SyntaxTopFormulaSyntax.instantiated w a b A t n q).conj
  ((PureQuotationSyntax.formula (input.instantiateTop replacement) w q).conj (FormulaCodeSyntax.formulaCode w q a b))

def instantiateFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n : Fin m) : Formula m := .ex
  ((instantiateValue input replacement w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)).conj (SyntaxTopFormulaSyntax.instantiateUnique w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)))

theorem instantiateValue_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q : Fin m) (ρ : Fin m → Fin k) :
    (instantiateValue input replacement w a b A t n q).rename ρ = instantiateValue input replacement (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) (ρ q) := by
  simp only [instantiateValue, Formula.rename, SyntaxTopFormulaSyntax.instantiated_rename, PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename]

theorem instantiateFiber_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n : Fin m) (ρ : Fin m → Fin k) :
    (instantiateFiber input replacement w a b A t n).rename ρ = instantiateFiber input replacement (ρ w) (ρ a) (ρ b) (ρ A) (ρ t) (ρ n) := by
  simp only [instantiateFiber, Formula.rename, instantiateValue_rename, SyntaxTopFormulaSyntax.instantiateUnique_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_instantiate_fiber {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q : Fin m) (hv : Derives Γ (instantiateValue input replacement w a b A t n q))
    (hu : Derives Γ (SyntaxTopFormulaSyntax.instantiateUnique w a b A t n q)) : Derives Γ (instantiateFiber input replacement w a b A t n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, instantiateValue_rename, SyntaxTopFormulaSyntax.instantiateUnique_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hv hu)

def abstractValue {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q : Fin m) : Formula m := (SyntaxTopFormulaSyntax.abstracted w a b A B n q).conj
  ((PureQuotationSyntax.formula (input.abstractFreeTop) w q).conj (FormulaCodeSyntax.formulaCode w q A b))

def abstractFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n : Fin m) : Formula m := .ex
  ((abstractValue input w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)).conj (SyntaxTopFormulaSyntax.abstractUnique w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)))

theorem abstractValue_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q : Fin m) (ρ : Fin m → Fin k) :
    (abstractValue input w a b A B n q).rename ρ = abstractValue input (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) := by
  simp only [abstractValue, Formula.rename, SyntaxTopFormulaSyntax.abstracted_rename, PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename]

theorem abstractFiber_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n : Fin m) (ρ : Fin m → Fin k) :
    (abstractFiber input w a b A B n).rename ρ = abstractFiber input (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) := by
  simp only [abstractFiber, Formula.rename, abstractValue_rename, SyntaxTopFormulaSyntax.abstractUnique_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_abstract_fiber {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q : Fin m) (hv : Derives Γ (abstractValue input w a b A B n q))
    (hu : Derives Γ (SyntaxTopFormulaSyntax.abstractUnique w a b A B n q)) : Derives Γ (abstractFiber input w a b A B n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, abstractValue_rename, SyntaxTopFormulaSyntax.abstractUnique_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hv hu)

end PPAC.Migration.Internal.NativeTopQuotationValueSyntax
