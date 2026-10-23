import PPAC.Migration.Internal.IndexFormulaRenameBridgeSyntax

/-! 原源推导规则中的三重存在消去与提升；只是既有规则组合，不另造推导核。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameBinders
open Source SourceAlgebra SourceLogic

theorem under_three {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+3)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) P.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)))

theorem zf_under_three {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+3)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) :=
  ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) B

theorem eliminate_three {m} {Γ : Context m} (B : Formula (m+3)) (P : Formula m)
    (he : Derives Γ (.ex (.ex (.ex B))))
    (hc : Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) P.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, hs, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr hs, h2⟩, h1⟩

end PPAC.Migration.Internal.IndexFormulaRenameBinders
