import PPAC.Migration.ObjectFiniteIteration

/-! 已公开八句对象公理的推导证书包；不是新公理或新推导规则。 -/
namespace PPAC.Migration.IterationContext
open Source SourceAlgebra SourceLogic

structure Evidence {m} (Γ : Context m) : Prop where
  extensionality : Derives Γ ((Source.SetLanguage.extensionality).rename Fin.elim0)
  pairing : Derives Γ ((Source.SetLanguage.pairing).rename Fin.elim0)
  union : Derives Γ ((Source.SetLanguage.union).rename Fin.elim0)
  foundation : Derives Γ ((Source.SetLanguage.foundation).rename Fin.elim0)
  transitiveSeparation : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0)
  existenceSeparation : Derives Γ ((Source.SetLanguage.separation IterationExistence.existenceMatrix).rename Fin.elim0)
  subsetSeparation : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.subsetMatrix).rename Fin.elim0)
  agreementSeparation : Derives Γ ((Source.SetLanguage.separation IterationSyntax.agreementMatrix).rename Fin.elim0)

theorem add {m} {Γ : Context m} (h : Evidence Γ) (p : Formula m) : Evidence (Context.add p Γ) := by
  constructor
  · exact SourceLogic.add h.extensionality p
  · exact SourceLogic.add h.pairing p
  · exact SourceLogic.add h.union p
  · exact SourceLogic.add h.foundation p
  · exact SourceLogic.add h.transitiveSeparation p
  · exact SourceLogic.add h.existenceSeparation p
  · exact SourceLogic.add h.subsetSeparation p
  · exact SourceLogic.add h.agreementSeparation p

theorem rename {m k} {Γ : Context m} (h : Evidence Γ) (r : Fin m → Fin k) : Evidence (Context.image (Formula.rename r) Γ) := by
  constructor
  · simpa only [closed_rename] using Derives.rename r h.extensionality
  · simpa only [closed_rename] using Derives.rename r h.pairing
  · simpa only [closed_rename] using Derives.rename r h.union
  · simpa only [closed_rename] using Derives.rename r h.foundation
  · simpa only [closed_rename] using Derives.rename r h.transitiveSeparation
  · simpa only [closed_rename] using Derives.rename r h.existenceSeparation
  · simpa only [closed_rename] using Derives.rename r h.subsetSeparation
  · simpa only [closed_rename] using Derives.rename r h.agreementSeparation

theorem under {m} {Γ : Context m} (h : Evidence Γ) (p : Formula (m+1)) :
    Evidence (Context.add p (Context.image Formula.raise Γ)) := add (rename h Fin.castSucc) p

theorem under_two {m} {Γ : Context m} (h : Evidence Γ) (p : Formula (m+2)) :
    Evidence (Context.add p (Context.image Formula.raise (Context.image Formula.raise Γ))) :=
  add (rename (rename h Fin.castSucc) Fin.castSucc) p

theorem source_ZF (m) : Evidence (Source.SetLanguage.ZF.at m) := by
  constructor
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.union, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaStructureSyntax.transitiveMatrix, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation IterationExistence.existenceMatrix, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation OmegaStructureSyntax.subsetMatrix, rfl⟩
  · exact .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation IterationSyntax.agreementMatrix, rfl⟩

theorem all_exists {m} {Γ : Context m} (h : Evidence Γ) (z a w : Fin m)
    (hw : Derives Γ (OmegaSyntax.omega w)) (hz : Derives Γ (OmegaSyntax.empty z)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp
      (FiniteIterationSyntax.existsTrack (Fin.last m) z.castSucc a.castSucc))) :=
  IterationExistence.all_exists z a w h.pairing h.union h.extensionality h.foundation h.transitiveSeparation h.existenceSeparation hw hz

theorem unique {m} {Γ : Context m} (h : Evidence Γ) (f d g e n z a w : Fin m)
    (hw : Derives Γ (OmegaSyntax.omega w)) (hz : Derives Γ (OmegaSyntax.empty z)) (hn : Derives Γ (.mem n w))
    (hf : Derives Γ (FiniteIterationSyntax.witness f d n z a)) (hg : Derives Γ (FiniteIterationSyntax.witness g e n z a)) :
    Derives Γ ((Formula.equal d e).conj (.equal f g)) :=
  FiniteIterationUniqueness.witness_equal f d g e n z a w h.extensionality h.transitiveSeparation h.subsetSeparation h.agreementSeparation hw hz hn hf hg
end PPAC.Migration.IterationContext
