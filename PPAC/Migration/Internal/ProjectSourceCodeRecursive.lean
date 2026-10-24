import PPAC.Migration.Internal.ProjectSourceCodeProperties

/-! 无额外载体前提的完整公式码递归双条件；根/上下文候选遍历所有内部集合。 -/
namespace PPAC.Migration.Internal.ProjectSourceCodeRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax PowerSetSyntax ProjectSourceCodeSyntax ProjectSourceCodeRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_carrier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (carrier w a c)) :
    Derives Γ ((sourceCode w n b f).iff (criterion w n b f)) :=
  ProjectSourceTypeLocalTransfer.iff_trans (ProjectSourceCodeCarrier.code_iff_typed hZ w a c n b f hc)
    (ProjectSourceTypeLocalTransfer.iff_trans (ProjectSourceTypeRecursive.recursive_iff hZ w a c n b f hw (.conjL hc) (.conjR hc))
      (ProjectSourceCodeCriterionTransfer.criterion_iff hZ w a c n b f hc))

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((sourceCode w n b f).iff (criterion w n b f)) := by
  have he := ProjectSourceCodeCarrier.exists_carrier hZ w
  let B := carrier w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := at_carrier (ZFContext.under_two hZ B) w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc hw2 hB
  have hh : Derives Δ (((sourceCode w n b f).iff (criterion w n b f)).raise.raise) := by
    simpa only [Formula.raise, Formula.iff, Formula.rename, sourceCode_rename, criterion_rename] using hout
  refine Derives.weaken ?_ hh
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩

def universalLaw {m} (w : Fin m) : Formula m := .all (.all (.all
  ((sourceCode w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
    (criterion w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))))))

theorem universalLaw_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (universalLaw w).rename r = universalLaw (r w) := by
  simp only [universalLaw, Formula.iff, Formula.rename, sourceCode_rename, criterion_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (universalLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
      (omega w.castSucc.castSucc.castSucc) := by
    simpa only [omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  exact recursive_iff (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc)
    w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
    (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3
end PPAC.Migration.Internal.ProjectSourceCodeRecursive
