import PPAC.Migration.Internal.FormulaCodeCaseLogic

/-! 已知原逻辑构造码时，完整FormulaCode精确选中唯一类型分支；不保留外部历史/载体前提。 -/
namespace PPAC.Migration.Internal.FormulaCodeKnownLogical
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open SyntaxLogicalSyntax (singleCode binaryCode binaryTag)
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeBranchSyntax FormulaCodeCaseLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode 4 w x n)) :
    Derives Γ ((formulaCode w n b f).iff (singleTypes false w b f x)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.single_iff hZ 4 false w b f x n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 1 4 w (fun _ => x) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (singleTypes false w b f x)) := by
      apply all_imp w n b f (singleTypes false w b f x)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 4
          (by decide) (by decide) (by decide) (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 1 4 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 1 4 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 1 4 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 1 4 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true 1 4 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true 1 4 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjL (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl)))))

theorem binary0_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode 0 w x y n)) :
    Derives Γ ((formulaCode w n b f).iff (binaryTypes w b f x y)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.binary_iff hZ 0 w b f x y n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 2 5 w (two x y) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (binaryTypes w b f x y)) := by
      apply all_imp w n b f (binaryTypes w b f x y)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 5
          (by decide) (by decide) (by decide) (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false 2 5 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 2 5 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 2 5 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 2 5 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true 2 5 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true 2 5 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjR (.disjL (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl))))))

theorem binary1_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode 1 w x y n)) :
    Derives Γ ((formulaCode w n b f).iff (binaryTypes w b f x y)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.binary_iff hZ 1 w b f x y n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 2 6 w (two x y) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (binaryTypes w b f x y)) := by
      apply all_imp w n b f (binaryTypes w b f x y)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 6
          (by decide) (by decide) (by decide) (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false 2 6 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 2 6 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 2 6 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 2 6 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true 2 6 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true 2 6 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjR (.disjR (.disjL (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl)))))))

theorem binary2_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode 2 w x y n)) :
    Derives Γ ((formulaCode w n b f).iff (binaryTypes w b f x y)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.binary_iff hZ 2 w b f x y n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 2 7 w (two x y) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (binaryTypes w b f x y)) := by
      apply all_imp w n b f (binaryTypes w b f x y)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 7
          (by decide) (by decide) (by decide) (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false 2 7 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 2 7 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 2 7 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 2 7 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true 2 7 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true 2 7 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjR (.disjR (.disjR (.disjL (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl))))))))

theorem binary3_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode 3 w x y n)) :
    Derives Γ ((formulaCode w n b f).iff (binaryTypes w b f x y)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.binary_iff hZ 3 w b f x y n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 2 8 w (two x y) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (binaryTypes w b f x y)) := by
      apply all_imp w n b f (binaryTypes w b f x y)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 8
          (by decide) (by decide) (by decide) (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false 2 8 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 2 8 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 2 8 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 2 8 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true 2 8 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true 2 8 (by decide) w b f n (two x y)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl)))))))))

theorem forall_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode 9 w x n)) :
    Derives Γ ((formulaCode w n b f).iff (singleTypes true w b f x)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.single_iff hZ 9 true w b f x n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 1 9 w (fun _ => x) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (singleTypes true w b f x)) := by
      apply all_imp w n b f (singleTypes true w b f x)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 9
          (by decide) (by decide) (by decide) (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false 1 9 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 1 9 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 1 9 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 1 9 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 1 9 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 10 true 1 9 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl))))))))))

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode 10 w x n)) :
    Derives Γ ((formulaCode w n b f).iff (singleTypes true w b f x)) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have ht := FormulaCodeBranchTyping.single_iff hZ 10 true w b f x n hw hc
  have hn := SyntaxNodeInjective.constructor_range hZ 1 10 w (fun _ => x) n hw hc
  apply Derives.conjI
  · apply Derives.impI
    let F := formulaCode w n b f
    let Ξ := Context.add F Γ
    have hall : Derives Ξ (allCases w n b f) := .conjR (.impE (add (.conjL hr) F) (.hyp (Or.inl rfl)))
    have himp : Derives Ξ ((allCases w n b f).imp (singleTypes true w b f x)) := by
      apply all_imp w n b f (singleTypes true w b f x)
      · apply Derives.impI
        exact .botE (atomic_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 10
          (by decide) (by decide) (by decide) (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 4 false 1 10 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 0 1 10 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 1 1 10 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 2 1 10 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.binary_conflict (ZFContext.add (ZFContext.add hZ F) _) 3 1 10 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .botE (FormulaCodeBranchReject.single_conflict (ZFContext.add (ZFContext.add hZ F) _) 9 true 1 10 (by decide) w b f n (fun _ => x)
          (add (add hw F) _) (add (add hc F) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (add (.conjL ht) F) _) (.hyp (Or.inl rfl))
    exact .impE himp hall
  · apply Derives.impI
    apply Derives.impE (add (.conjR hr) _)
    exact .conjI (add hn _) (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.impE (add (.conjR ht) _) (.hyp (Or.inl rfl))))))))))

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w b f x n k : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hk : Derives Γ (successor k b)) :
    Derives Γ ((formulaCode w n b f).iff ((contexts w b f).conj (formulaCode w x k f))) := by
  have hh : Derives Γ ((formulaCode w n b f).iff (singleTypes true w b f x)) := by
    cases universal
    · exact exists_iff hZ w b f x n hw hc
    · exact forall_iff hZ w b f x n hw hc
  exact SyntaxTypeLocalTransfer.iff_trans hh
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (FormulaCodeBranchSyntax.at_successor hZ w x b f k hk))

end PPAC.Migration.Internal.FormulaCodeKnownLogical
