import PPAC.Migration.Internal.SuccessorRecursion

/-! 算术推导只包装四个原公理与三个明确分离实例，不包含算术或递推结论。 -/
namespace PPAC.Migration.Internal.ArithmeticContext
open Source SourceAlgebra SourceLogic
structure Evidence {m} (Γ : Context m) : Prop where
  base : SequenceContext.Evidence Γ
  ordinalSeparation : Derives Γ ((Source.SetLanguage.separation OmegaOrdinals.matrix).rename Fin.elim0)
  transitiveSeparation : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0)
  restrictionSeparation : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0)

theorem rename {m k} {Γ : Context m} (hA : Evidence Γ) (r : Fin m → Fin k) : Evidence (Context.image (Formula.rename r) Γ) := by
  constructor
  · exact SequenceContext.rename hA.base r
  · simpa only [closed_rename] using Derives.rename r hA.ordinalSeparation
  · simpa only [closed_rename] using Derives.rename r hA.transitiveSeparation
  · simpa only [closed_rename] using Derives.rename r hA.restrictionSeparation

theorem add {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula m) : Evidence (Context.add p Γ) :=
  ⟨SequenceContext.add hA.base p, SourceLogic.add hA.ordinalSeparation p,
    SourceLogic.add hA.transitiveSeparation p, SourceLogic.add hA.restrictionSeparation p⟩
theorem under {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula (m+1)) : Evidence (Context.add p (Context.image Formula.raise Γ)) :=
  add (rename hA Fin.castSucc) p
theorem under_two {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula (m+2)) :
    Evidence (Context.add p (Context.image Formula.raise (Context.image Formula.raise Γ))) := add (rename (rename hA Fin.castSucc) Fin.castSucc) p

theorem source_ZF (m : Nat) : Evidence (Source.SetLanguage.ZF.at m) :=
  ⟨SequenceContext.source_ZF m,
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaOrdinals.matrix, rfl⟩,
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaStructureSyntax.transitiveMatrix, rfl⟩,
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation RestrictionSyntax.matrix, rfl⟩⟩
end PPAC.Migration.Internal.ArithmeticContext
