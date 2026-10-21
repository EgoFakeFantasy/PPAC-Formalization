import PPAC.Migration.Internal.FormulaCodeTypedDataCases

/-! 接受码实际唯一解码为完整类型数据；正向接口不假定原Constructor存在。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDataForward
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeTypedDataSyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem cases_of_shape {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ (cases 11 w t l g b f) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have hh : Derives Γ ((allCases w n b f).imp (cases 11 w t l g b f)) := by
    apply FormulaCodeCaseLogic.all_imp w n b f (cases 11 w t l g b f)
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.atomic (ZFContext.add hZ _) w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.negation (ZFContext.add hZ _) w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.binary (ZFContext.add hZ _) 0 w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.binary (ZFContext.add hZ _) 1 w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.binary (ZFContext.add hZ _) 2 w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.binary (ZFContext.add hZ _) 3 w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.universal (ZFContext.add hZ _) w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTypedDataCases.existential (ZFContext.add hZ _) w n b f t p l g
        (add hw _) (add hc _) (add hs _) (.hyp (Or.inl rfl))
  exact .impE hh (.conjR (.impE (.conjL hr) hc))

theorem data_of_shape {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ (typedData w n b f t p l g) := by
  have hchild := FormulaCodeTreeValidity.children hZ w n b f t p l g hw hc hs
  have hctx := Derives.conjR (FormulaCodeProperties.guards w n b f hc)
  exact .conjI (.conjI hs hchild) (.conjI hctx (cases_of_shape hZ w n b f t p l g hw hc hs))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f)) : Derives Γ (typedFiber w n b f) := by
  have he := FormulaCodeAcceptedShape.accepted hZ w n b f hw hc
  let B := (FormulaCodeShapeSyntax.shapeBody w n).conj
    (FormulaCodeShapeSyntax.uniqueShape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
      (Fin.last (m+2)).castSucc (Fin.last (m+3)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply FormulaCodeShapeSyntax.eliminate_fiber w n _ he
  have hZ4 := StructuralListLengthSyntax.zf_under_four hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using StructuralListLengthSyntax.under_four hw B
  have hc4 : Derives Δ (formulaCode w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      b.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using StructuralListLengthSyntax.under_four hc B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hd := data_of_shape hZ4 w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    b.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc
    (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 hc4 (.conjL hB)
  have hout := intro_fiber _ _ _ _ _ _ _ _ hd (.conjR hB)
  simpa only [Formula.raise, typedFiber_rename] using hout
theorem reject_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g))
    (hb : Derives Γ (cases 11 w t l g b f).neg) : Derives Γ (formulaCode w n b f).neg := by
  apply Derives.impI
  exact .impE (add hb _) (cases_of_shape (ZFContext.add hZ _) w n b f t p l g
    (add hw _) (.hyp (Or.inl rfl)) (add hs _))

theorem reject_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g))
    (hb : Derives Γ (typedData w n b f t p l g).neg) : Derives Γ (formulaCode w n b f).neg := by
  apply Derives.impI
  exact .impE (add hb _) (data_of_shape (ZFContext.add hZ _) w n b f t p l g
    (add hw _) (.hyp (Or.inl rfl)) (add hs _))

theorem data_tree_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (typedData w n b f t p l g)) :
    Derives Γ (StructuralTreeValiditySyntax.valid w n) :=
  StructuralTreeDecode.recursive_to_valid hZ w n hw (StructuralTreeValiditySyntax.intro_recursive w n t p l g (.conjL hd))
end PPAC.Migration.Internal.FormulaCodeTypedDataForward
