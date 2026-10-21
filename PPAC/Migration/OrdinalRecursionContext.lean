import PPAC.Migration.ObjectOrdinalRecursionSuccessor
import PPAC.Migration.ReplacementInstances

/-! 仅包装五个既有原公理的Derives证书；不含递归存在、相容或收集结论。 -/
namespace PPAC.Migration.OrdinalRecursionContext
open Source SourceAlgebra SourceLogic

structure Evidence {m} (Γ : Context m) : Prop where
  extensionality : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)
  foundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0)
  pairing : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0)
  union : Derives Γ (Source.SetLanguage.union.rename Fin.elim0)
  agreementSeparation : Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix.neg).rename Fin.elim0)

theorem rename {m k} {Γ : Context m} (hA : Evidence Γ) (r : Fin m → Fin k) : Evidence (Context.image (Formula.rename r) Γ) := by
  constructor
  · simpa only [closed_rename] using Derives.rename r hA.extensionality
  · simpa only [closed_rename] using Derives.rename r hA.foundation
  · simpa only [closed_rename] using Derives.rename r hA.pairing
  · simpa only [closed_rename] using Derives.rename r hA.union
  · simpa only [closed_rename] using Derives.rename r hA.agreementSeparation

theorem add {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula m) : Evidence (Context.add p Γ) :=
  ⟨SourceLogic.add hA.extensionality p, SourceLogic.add hA.foundation p, SourceLogic.add hA.pairing p,
    SourceLogic.add hA.union p, SourceLogic.add hA.agreementSeparation p⟩

theorem under {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula (m+1)) : Evidence (Context.add p (Context.image Formula.raise Γ)) :=
  add (rename hA Fin.castSucc) p

theorem source_ZF (m : Nat) : Evidence (Source.SetLanguage.ZF.at m) :=
  ⟨.hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation IterationSyntax.agreementMatrix.neg, rfl⟩⟩
theorem under_two {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula (m+2)) :
    Evidence (Context.add p (Context.image Formula.raise (Context.image Formula.raise Γ))) :=
  add (rename (rename hA Fin.castSucc) Fin.castSucc) p

end PPAC.Migration.OrdinalRecursionContext
