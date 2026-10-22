import PPAC.Migration.Internal.SyntaxFormulaComposeDiagrams

/-! 固定3/14个对象变量的原存在消去、全称上下文提升；不构造新的推导规则。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeBinders
open Source SourceAlgebra SourceLogic

theorem eliminate_3 {m} {Γ : Context m} (B : Formula (m+3)) (P : Formula m)
    (he : Derives Γ (.ex (.ex (.ex B))))
    (hc : Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) P.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, hs, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr hs, h2⟩, h1⟩

theorem under_14 {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+14)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))))))))))) P.raise.raise.raise.raise.raise.raise.raise.raise.raise.raise.raise.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hp)))))))))))))))

theorem zf_under_14 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+14)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))))))))))) := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) B
end PPAC.Migration.Internal.SyntaxFormulaComposeBinders
