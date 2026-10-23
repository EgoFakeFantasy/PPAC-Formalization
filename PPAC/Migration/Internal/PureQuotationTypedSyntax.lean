import PPAC.Migration.Internal.PureQuotationTermTyping

/-! 原quotation与精确内部作用域类型的实际值公式。 -/
namespace PPAC.Migration.Internal.PureQuotationTypedSyntax
open Source SourceAlgebra SourceLogic

def termValue {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : Formula m :=
  (PureQuotationSyntax.term input w n).conj (SyntaxTermSyntax.term w b f n)

def formulaValue {m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : Formula m :=
  (PureQuotationSyntax.formula input w n).conj (FormulaCodeSyntax.formulaCode w n b f)

def termExists {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : Formula m := .ex
  (termValue input w.castSucc b.castSucc f.castSucc (Fin.last m))

def formulaExists {m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : Formula m := .ex
  (formulaValue input w.castSucc b.castSucc f.castSucc (Fin.last m))

def termUnique {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) : Formula m := .all
  ((termValue input w.castSucc b.castSucc f.castSucc (Fin.last m)).imp (.equal (Fin.last m) n.castSucc))

def formulaUnique {m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) : Formula m := .all
  ((formulaValue input w.castSucc b.castSucc f.castSucc (Fin.last m)).imp (.equal (Fin.last m) n.castSucc))

def termFiber {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) : Formula m := .ex
  ((termValue input w.castSucc b.castSucc f.castSucc (Fin.last m)).conj (termUnique input w.castSucc b.castSucc f.castSucc (Fin.last m)))

def formulaFiber {m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) : Formula m := .ex
  ((formulaValue input w.castSucc b.castSucc f.castSucc (Fin.last m)).conj (formulaUnique input w.castSucc b.castSucc f.castSucc (Fin.last m)))

theorem termValue_rename {m k} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) (ρ : Fin m → Fin k) :
    (termValue input w b f n).rename ρ = termValue input (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [termValue, PureQuotationSyntax.term_rename, SyntaxTermSyntax.term_rename, Formula.rename]

theorem termExists_rename {m k} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) (ρ : Fin m → Fin k) :
    (termExists input w b f).rename ρ = termExists input (ρ w) (ρ b) (ρ f) := by
  simp only [termExists, termValue_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem termUnique_rename {m k} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m) (ρ : Fin m → Fin k) :
    (termUnique input w b f n).rename ρ = termUnique input (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [termUnique, termValue_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem termFiber_rename {m k} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f : Fin m) (ρ : Fin m → Fin k) :
    (termFiber input w b f).rename ρ = termFiber input (ρ w) (ρ b) (ρ f) := by
  simp only [termFiber, termValue_rename, termUnique_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_term_exists {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m)
    (hn : Derives Γ (termValue input w b f n)) : Derives Γ (termExists input w b f) := by
  apply Derives.exI n
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, termValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn

theorem intro_term_fiber {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w b f n : Fin m)
    (hn : Derives Γ (termValue input w b f n)) (hu : Derives Γ (termUnique input w b f n)) : Derives Γ (termFiber input w b f) := by
  apply Derives.exI n
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, termValue_rename, termUnique_rename, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hu)

theorem formulaValue_rename {m k} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) (ρ : Fin m → Fin k) :
    (formulaValue input w b f n).rename ρ = formulaValue input (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [formulaValue, PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename, Formula.rename]

theorem formulaExists_rename {m k} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) (ρ : Fin m → Fin k) :
    (formulaExists input w b f).rename ρ = formulaExists input (ρ w) (ρ b) (ρ f) := by
  simp only [formulaExists, formulaValue_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem formulaUnique_rename {m k} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m) (ρ : Fin m → Fin k) :
    (formulaUnique input w b f n).rename ρ = formulaUnique input (ρ w) (ρ b) (ρ f) (ρ n) := by
  simp only [formulaUnique, formulaValue_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem formulaFiber_rename {m k} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f : Fin m) (ρ : Fin m → Fin k) :
    (formulaFiber input w b f).rename ρ = formulaFiber input (ρ w) (ρ b) (ρ f) := by
  simp only [formulaFiber, formulaValue_rename, formulaUnique_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_formula_exists {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m)
    (hn : Derives Γ (formulaValue input w b f n)) : Derives Γ (formulaExists input w b f) := by
  apply Derives.exI n
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, formulaValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn

theorem intro_formula_fiber {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m)
    (hn : Derives Γ (formulaValue input w b f n)) (hu : Derives Γ (formulaUnique input w b f n)) : Derives Γ (formulaFiber input w b f) := by
  apply Derives.exI n
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, formulaValue_rename, formulaUnique_rename, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hu)

end PPAC.Migration.Internal.PureQuotationTypedSyntax
