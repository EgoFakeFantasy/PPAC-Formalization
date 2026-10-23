import PPAC.Migration.Internal.TermImageQuotationTyping

/-! 两份原项像quotation码及准确TermLists的纯对象环境合同；全部码对见证内部绑定。 -/
namespace PPAC.Migration.Internal.TermQuotationEnvironmentSyntax
open Source SourceAlgebra SourceLogic

def environment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d R S : Fin m) : Formula m :=
  ((TermImageQuotationSyntax.images bs w R).conj (TermImageQuotationSyntax.images fs w S)).conj
    (SyntaxMixedImageCodeSyntax.termLists w a b c d R S)

def body {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d : Fin m) : Formula (m+2) :=
  environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def existsEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d : Fin m) : Formula m := .ex (.ex (body bs fs w a b c d))

def uniqueEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d R S : Fin m) : Formula m := .all (.all
      ((environment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
        ((Formula.equal (Fin.last m).castSucc R.castSucc.castSucc).conj (.equal (Fin.last (m+1)) S.castSucc.castSucc))))

def fiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d : Fin m) : Formula m := .ex (.ex
      ((body bs fs w a b c d).conj
        (uniqueEnvironment bs fs w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem environment_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d R S : Fin m) (ρ : Fin m → Fin k) : (environment bs fs w a b c d R S).rename ρ = environment bs fs (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [environment, TermImageQuotationSyntax.images_rename, SyntaxMixedImageCodeSyntax.termLists_rename, Formula.rename]

theorem existsEnvironment_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d : Fin m) (ρ : Fin m → Fin k) : (existsEnvironment bs fs w a b c d).rename ρ = existsEnvironment bs fs (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [existsEnvironment, body, environment_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueEnvironment_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d R S : Fin m) (ρ : Fin m → Fin k) : (uniqueEnvironment bs fs w a b c d R S).rename ρ = uniqueEnvironment bs fs (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [uniqueEnvironment, environment_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d : Fin m) (ρ : Fin m → Fin k) : (fiber bs fs w a b c d).rename ρ = fiber bs fs (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [fiber, body, environment_rename, uniqueEnvironment_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_exists {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d R S : Fin m) (he : Derives Γ (environment bs fs w a b c d R S)) : Derives Γ (existsEnvironment bs fs w a b c d) := by
  apply Derives.exI R
  apply Derives.exI S
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [body, Formula.instantiate, environment_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

theorem intro_fiber {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w a b c d R S : Fin m) (he : Derives Γ (environment bs fs w a b c d R S)) (hu : Derives Γ (uniqueEnvironment bs fs w a b c d R S)) : Derives Γ (fiber bs fs w a b c d) := by
  apply Derives.exI R
  apply Derives.exI S
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [body, Formula.instantiate, environment_rename, uniqueEnvironment_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he hu)

end PPAC.Migration.Internal.TermQuotationEnvironmentSyntax
