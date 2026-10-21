import PPAC.Migration.IterationExistence

/-! 任意内部n∈ω的后继域有限轨迹，实际域与图都唯一。 -/
namespace PPAC.Migration.FiniteIterationUniqueness
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax IterationSyntax FiniteIterationSyntax

theorem witness_equal {m} {Γ : Context m} (f d g e n z a w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (htrans : Derives Γ ((Source.SetLanguage.separation transitiveMatrix).rename Fin.elim0))
    (hsubset : Derives Γ ((Source.SetLanguage.separation subsetMatrix).rename Fin.elim0))
    (hagree : Derives Γ ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w))
    (hf : Derives Γ (witness f d n z a)) (hg : Derives Γ (witness g e n z a)) :
    Derives Γ ((Formula.equal d e).conj (.equal f g)) := by
  have htn := OmegaStructureAlgebra.element_transitive_at w n (OmegaStructureInduction.elements_transitive w htrans hw) hn
  have htd := OmegaElementary.successor_transitive d n (.conjL hf) htn
  have hdw := OmegaStructureAlgebra.successor_member w d n he hw hn (.conjL hf)
  have htw := OmegaStructureInduction.omega_transitive w hsubset hw
  have hdb := Derives.impE (transitive_at w d htw) hdw
  have hde := OmegaUniversal.successor_unique d e n he (.conjL hf) (.conjL hg)
  have hgd := IterationExistence.subst_domain g e d z a (eq_symm hde) (.conjR hg)
  have hfg := IterationCompatibility.unique_same_domain f g d z a w he hagree hw hz (.conjR hf) hgd htd hdb
  exact .conjI hde hfg
end PPAC.Migration.FiniteIterationUniqueness
