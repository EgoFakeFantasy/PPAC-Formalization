import PPAC.Migration.Internal.FormulaCodeRecursive

/-! 已知原构造的完整类型条件；替换只使用对象等词规则。 -/
namespace PPAC.Migration.Internal.FormulaCodeBranchSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax

def singleTypes {m} (advance : Bool) (w b f x : Fin m) : Formula m :=
  (contexts w b f).conj (stepCheck advance w x b f)
def binaryTypes {m} (w b f x y : Fin m) : Formula m :=
  (contexts w b f).conj ((formulaCode w x b f).conj (formulaCode w y b f))

theorem singleTypes_rename {m k} (advance : Bool) (w b f x : Fin m) (r : Fin m → Fin k) :
    (singleTypes advance w b f x).rename r = singleTypes advance (r w) (r b) (r f) (r x) := by
  simp only [singleTypes, Formula.rename, contexts_rename, stepCheck_rename]
theorem binaryTypes_rename {m k} (w b f x y : Fin m) (r : Fin m → Fin k) :
    (binaryTypes w b f x y).rename r = binaryTypes (r w) (r b) (r f) (r x) (r y) := by
  simp only [binaryTypes, Formula.rename, contexts_rename, formulaCode_rename]

theorem check_subst_child {m} {Γ : Context m} (advance : Bool) (w x y b f : Fin m)
    (he : Derives Γ (.equal x y)) (hr : Derives Γ (stepCheck advance w x b f)) :
    Derives Γ (stepCheck advance w y b f) := by
  have hi : Derives Γ ((stepCheck advance w.castSucc (Fin.last m) b.castSucc f.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, stepCheck_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst (stepCheck advance w.castSucc (Fin.last m) b.castSucc f.castSucc) he hi
  simpa only [Formula.instantiate, stepCheck_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x b f k : Fin m)
    (hk : Derives Γ (successor k b)) :
    Derives Γ ((advancedCode w x b f).iff (formulaCode w x k f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let K := (successor (Fin.last m) b.castSucc).conj (formulaCode w.castSucc x.castSucc (Fin.last m) f.castSucc)
    let Ξ := Context.add (advancedCode w x b f) Γ
    let Δ := Context.add K (Context.image Formula.raise Ξ)
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ (advancedCode w x b f)) K
    have hk1 : Derives Δ (successor k.castSucc b.castSucc) := by
      simpa only [Formula.raise, successor_rename] using under (add hk (advancedCode w x b f)) K
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have he := InsertLogic.unique _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality (.conjL hK) hk1
    have hout := FormulaCodeTransport.code_bound _ _ _ _ _ he (.conjR hK)
    simpa only [Formula.raise, formulaCode_rename] using hout
  · apply Derives.impI
    exact intro_advanced _ _ _ _ k (add hk _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.FormulaCodeBranchSyntax
