import PPAC.Migration.Internal.SyntaxRenameOutput

/-! 原源规则的固定多变量存在消去/变量提升；所有见证仍由对象量词取得。 -/
namespace PPAC.Migration.Internal.SyntaxRenameBinders
open Source SourceAlgebra SourceLogic

theorem under_2 {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+2)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))) P.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hp)))

theorem zf_under_2 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+2)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))) := ZFContext.add (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) B

theorem eliminate_2 {m} {Γ : Context m} (B : Formula (m+2)) (P : Formula m)
    (he : Derives Γ (.ex (.ex (B))))
    (hc : Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Γ)))) P.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, hs, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr hs, h1⟩

theorem under_4 {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+4)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))) P.raise.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hp)))))

theorem zf_under_4 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+4)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))) := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) B

theorem eliminate_4 {m} {Γ : Context m} (B : Formula (m+4)) (P : Formula m)
    (he : Derives Γ (.ex (.ex (.ex (.ex (B))))))
    (hc : Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))) P.raise.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, ⟨s3, hs, h3⟩, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr ⟨s3, Or.inr hs, h3⟩, h2⟩, h1⟩

theorem under_5 {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+5)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))) P.raise.raise.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hp))))))

theorem zf_under_5 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+5)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))) := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) B

theorem eliminate_5 {m} {Γ : Context m} (B : Formula (m+5)) (P : Formula m)
    (he : Derives Γ (.ex (.ex (.ex (.ex (.ex (B)))))))
    (hc : Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))) P.raise.raise.raise.raise.raise) : Derives Γ P := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro p (hp | ⟨s1, ⟨s2, ⟨s3, ⟨s4, hs, h4⟩, h3⟩, h2⟩, h1⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨s1, Or.inr ⟨s2, Or.inr ⟨s3, Or.inr ⟨s4, Or.inr hs, h4⟩, h3⟩, h2⟩, h1⟩

theorem under_6 {m} {Γ : Context m} {P : Formula m} (hp : Derives Γ P) (B : Formula (m+6)) :
    Derives (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))) P.raise.raise.raise.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hp)))))))

theorem zf_under_6 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (B : Formula (m+6)) :
    ZFContext.Evidence (Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))) := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) B

end PPAC.Migration.Internal.SyntaxRenameBinders
