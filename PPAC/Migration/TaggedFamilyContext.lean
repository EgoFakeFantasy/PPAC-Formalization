import PPAC.Migration.TaggedFamilySyntax

/-! 仅包装四个既有原公理证书，不含行/族存在、非空或不交结论。 -/
namespace PPAC.Migration.TaggedFamilyContext
open Source SourceAlgebra SourceLogic

structure Evidence {m} (Γ : Context m) : Prop where
  extensionality : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)
  pairing : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0)
  pairReplacement : Derives Γ ((Source.SetLanguage.replacement TaggedRowSyntax.pairMatrix).rename Fin.elim0)
  familyReplacement : Derives Γ ((Source.SetLanguage.replacement TaggedFamilySyntax.matrix).rename Fin.elim0)

theorem rename {m k} {Γ : Context m} (hA : Evidence Γ) (r : Fin m → Fin k) : Evidence (Context.image (Formula.rename r) Γ) := by
  constructor
  · simpa only [closed_rename] using Derives.rename r hA.extensionality
  · simpa only [closed_rename] using Derives.rename r hA.pairing
  · simpa only [closed_rename] using Derives.rename r hA.pairReplacement
  · simpa only [closed_rename] using Derives.rename r hA.familyReplacement

theorem add {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula m) : Evidence (Context.add p Γ) :=
  ⟨SourceLogic.add hA.extensionality p, SourceLogic.add hA.pairing p,
    SourceLogic.add hA.pairReplacement p, SourceLogic.add hA.familyReplacement p⟩

theorem under {m} {Γ : Context m} (hA : Evidence Γ) (p : Formula (m+1)) :
    Evidence (Context.add p (Context.image Formula.raise Γ)) := add (rename hA Fin.castSucc) p

theorem source_ZF (m : Nat) : Evidence (Source.SetLanguage.ZF.at m) :=
  ⟨.hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement TaggedRowSyntax.pairMatrix, rfl⟩,
   .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement TaggedFamilySyntax.matrix, rfl⟩⟩
end PPAC.Migration.TaggedFamilyContext
