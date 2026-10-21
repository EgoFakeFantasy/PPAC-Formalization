import PPAC.Migration.Internal.FormulaCodeTypedDataReverse

/-! 完整类型识别的实际唯一纤维双条件和正负分类；终点是对象原核Derives。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDecode
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeSyntax FormulaCodeTypedDataSyntax
open FormulaCodeShapeSyntax (uniqueShape uniqueShape_rename)
open StructuralTreeOperatorSyntax (shape)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem eliminate_fiber {m} {Γ : Context m} (w n b f : Fin m) (q : Formula m)
    (he : Derives Γ (typedFiber w n b f))
    (hc : Derives (Context.add
      ((dataBody w n b f).conj (uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
        (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
        (Fin.last (m+2)).castSucc (Fin.last (m+3))))
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
      q.raise.raise.raise.raise) : Derives Γ q := by
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩

theorem code_of_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (typedFiber w n b f)) : Derives Γ (formulaCode w n b f) := by
  let B := (dataBody w n b f).conj (uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_fiber w n b f _ hd
  have hZ4 := StructuralListLengthSyntax.zf_under_four hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using StructuralListLengthSyntax.under_four hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := FormulaCodeTypedDataReverse.code_of_data hZ4
    w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    b.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 (.conjL hB)
  simpa only [Formula.raise, formulaCode_rename] using ho

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((formulaCode w n b f).iff (typedFiber w n b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact FormulaCodeTypedDataForward.actual_fiber (ZFContext.add hZ _) w n b f (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact code_of_fiber (ZFContext.add hZ _) w n b f (add hw _) (.hyp (Or.inl rfl))

theorem reject_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((formulaCode w n b f).neg.iff (typedFiber w n b f).neg) := by
  have hh := fiber_iff hZ w n b f hw
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    exact .impE (.hyp (Or.inr (Or.inl rfl))) (.impE (add (add (.conjR hh) _) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.impI
    exact .impE (.hyp (Or.inr (Or.inl rfl))) (.impE (add (add (.conjL hh) _) _) (.hyp (Or.inl rfl)))

theorem classification {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ (((formulaCode w n b f).conj (typedFiber w n b f)).disj
      ((formulaCode w n b f).neg.conj (typedFiber w n b f).neg)) := by
  have hh := fiber_iff hZ w n b f hw
  apply Derives.classical
  let Q := ((formulaCode w n b f).conj (typedFiber w n b f)).disj
    ((formulaCode w n b f).neg.conj (typedFiber w n b f).neg)
  have hn : Derives (Context.add Q.neg Γ) (formulaCode w n b f).neg := by
    apply Derives.impI
    have hc : Derives (Context.add (formulaCode w n b f) (Context.add Q.neg Γ)) (formulaCode w n b f) := .hyp (Or.inl rfl)
    exact .impE (.hyp (Or.inr (Or.inl rfl))) (.disjL (.conjI hc (.impE (add (add (.conjL hh) _) _) hc)))
  have ht : Derives (Context.add Q.neg Γ) (typedFiber w n b f).neg := by
    apply Derives.impI
    exact .impE (add hn _) (.impE (add (add (.conjR hh) _) _) (.hyp (Or.inl rfl)))
  exact .impE (.hyp (Or.inl rfl)) (.disjR (.conjI hn ht))
end PPAC.Migration.Internal.FormulaCodeTypedDecode
