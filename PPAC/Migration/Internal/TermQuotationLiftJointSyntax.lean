import PPAC.Migration.Internal.TermQuotationLiftCorrespondence

/-! 原coded binder与提升quotation环境的实际联合纤维；唯一性比较全部原lifted候选。 -/
namespace PPAC.Migration.Internal.TermQuotationLiftJointSyntax
open Source SourceAlgebra SourceLogic TermQuotationLiftSyntax
open SyntaxRenameQuerySyntax (of_eq)

def state {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w R S a b c d A C K H : Fin m) : Formula m :=
  (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).conj
    (TermQuotationEnvironmentSyntax.environment (newBound bs) (shifted fs) w A b C d K H)

def body {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w R S a b c d A C : Fin m) : Formula (m+2) :=
  (state bs fs w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (SyntaxCodedMixedBinderFiber.uniquePair w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))

def fiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w R S a b c d A C : Fin m) : Formula m := .ex (.ex (body bs fs w R S a b c d A C))

theorem state_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w R S a b c d A C K H : Fin m) (ρ : Fin m → Fin k) :
    (state bs fs w R S a b c d A C K H).rename ρ = state bs fs (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) (ρ K) (ρ H) := by
  simp only [state, Formula.rename, SyntaxCodedMixedBinderSyntax.lifted_rename, TermQuotationEnvironmentSyntax.environment_rename]

theorem fiber_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w R S a b c d A C : Fin m) (ρ : Fin m → Fin k) :
    (fiber bs fs w R S a b c d A C).rename ρ = fiber bs fs (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ A) (ρ C) := by
  simp only [fiber, body, Formula.rename, state_rename, SyntaxCodedMixedBinderFiber.uniquePair_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free))
    (w R S a b c d A C K H : Fin m) (hs : Derives Γ (state bs fs w R S a b c d A C K H))
    (hu : Derives Γ (SyntaxCodedMixedBinderFiber.uniquePair w R S a b c d A C K H)) :
    Derives Γ (fiber bs fs w R S a b c d A C) := by
  apply Derives.exI K
  apply Derives.exI H
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, state_rename, SyntaxCodedMixedBinderFiber.uniquePair_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs hu)

end PPAC.Migration.Internal.TermQuotationLiftJointSyntax
