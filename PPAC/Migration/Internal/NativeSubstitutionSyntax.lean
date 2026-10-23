import PPAC.Migration.Internal.NativeSubstitutionImages

/-! 原生变量替换的实际项像环境合同；对象码值和上下文长度仍为对象变量。 -/
namespace PPAC.Migration.Internal.NativeSubstitutionSyntax
open Source SourceAlgebra SourceLogic

abbrev Mapping (source bound free : PureSyntaxQuotation.Ctx) :=
  YesMetaZFC.Logic.FirstOrder.VariableSubstitution YesMetaZFC.SetTheory.signature source bound free

def environment {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w a b c d R S : Fin m) : Formula m :=
  TermQuotationEnvironmentSyntax.environment (NativeSubstitutionImages.images sb σ) (NativeSubstitutionImages.images sf τ) w a b c d R S

def existsEnvironment {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w a b c d : Fin m) : Formula m :=
  TermQuotationEnvironmentSyntax.existsEnvironment (NativeSubstitutionImages.images sb σ) (NativeSubstitutionImages.images sf τ) w a b c d

def fiber {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w a b c d : Fin m) : Formula m :=
  TermQuotationEnvironmentSyntax.fiber (NativeSubstitutionImages.images sb σ) (NativeSubstitutionImages.images sf τ) w a b c d

theorem environment_rename {m k} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w a b c d R S : Fin m) (ρ : Fin m → Fin k) :
    (environment σ τ w a b c d R S).rename ρ = environment σ τ (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) :=
  TermQuotationEnvironmentSyntax.environment_rename _ _ w a b c d R S ρ

theorem existsEnvironment_rename {m k} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w a b c d : Fin m) (ρ : Fin m → Fin k) :
    (existsEnvironment σ τ w a b c d).rename ρ = existsEnvironment σ τ (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) :=
  TermQuotationEnvironmentSyntax.existsEnvironment_rename _ _ w a b c d ρ

theorem fiber_rename {m k} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w a b c d : Fin m) (ρ : Fin m → Fin k) :
    (fiber σ τ w a b c d).rename ρ = fiber σ τ (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) :=
  TermQuotationEnvironmentSyntax.fiber_rename _ _ w a b c d ρ

theorem environment_lift {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w A b C d K H : Fin m) :
    environment (YesMetaZFC.Logic.FirstOrder.VariableSubstitution.liftBound YesMetaZFC.SetTheory.SetSort.set σ)
      (YesMetaZFC.Logic.FirstOrder.VariableSubstitution.weakenBound YesMetaZFC.SetTheory.SetSort.set τ) w A b C d K H =
    TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound (NativeSubstitutionImages.images sb σ))
      (TermQuotationLiftSyntax.shifted (NativeSubstitutionImages.images sf τ)) w A b C d K H := by
  simp only [environment, NativeSubstitutionImages.images_lift, NativeSubstitutionImages.images_weaken]

end PPAC.Migration.Internal.NativeSubstitutionSyntax
