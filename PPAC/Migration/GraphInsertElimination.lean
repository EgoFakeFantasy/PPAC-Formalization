import PPAC.Migration.GraphInsertRestriction

/-! 原图扩展的三个实际对象见证同步消去；仍只使用原exE/rename/weaken。 -/
namespace PPAC.Migration.GraphInsertElimination
open Source GraphInsertSyntax

abbrev witnesses {m} (f d x y : Fin m) : Formula (m+3) :=
  witness (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc

theorem eliminate {m} {Γ : Context m} (f d x y : Fin m) (q : Formula m)
    (h : Derives Γ (existsExtension f d x y))
    (hc : Derives (Context.add (witnesses f d x y)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) q.raise.raise.raise) :
    Derives Γ q := by
  change Derives Γ (.ex (.ex (.ex (witnesses f d x y)))) at h
  apply Derives.exE h
  apply Derives.exE (p := .ex (witnesses f d x y)) (Derives.hyp (Or.inl rfl))
  apply Derives.exE (p := witnesses f d x y) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  intro r hr
  rcases hr with hr | ⟨s, ⟨t, ht, he₁⟩, he₂⟩
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ht, he₁⟩, he₂⟩

theorem under_three {m} {Γ : Context m} {q : Formula m} (h : Derives Γ q) (b : Formula (m+3)) :
    Derives (Context.add b (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
      q.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (.rename Fin.castSucc (.rename Fin.castSucc (.rename Fin.castSucc h)))
end PPAC.Migration.GraphInsertElimination
