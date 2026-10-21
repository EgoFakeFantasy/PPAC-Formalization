import PPAC.Migration.Internal.StructuralTreeRecursiveCorrespondence

/-! 对实际零/单位标志，树求值接受恰为递归子树条件，拒绝恰为其否定；真实求值总单值已消去。 -/
namespace PPAC.Migration.Internal.StructuralTreeCheck
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax StructuralTreeEvaluationSyntax StructuralTreeRecursiveSyntax
open StructuralTreeOperatorSyntax (good good_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem true_step_good {m} {Γ : Context m} (w z e n h : Fin m) (hz : Derives Γ (empty z))
    (he : Derives Γ (successor e z)) (hs : Derives Γ (StructuralTreeOperatorSyntax.step w z e n h e)) : Derives Γ (good w e n h) := by
  have hne := StructuralTreeHistory.unit_distinct z e hz he
  apply Derives.disjE hs
  · exact .conjL (.hyp (Or.inl rfl))
  · exact .botE (.impE (add hne _) (.conjR (.hyp (Or.inl rfl))))

theorem accepts_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hn : Derives Γ (ordinal n))
    (ha : Derives Γ (accepts w z e n)) : Derives Γ (branch w z e n) := by
  have hh := StructuralTreeHistory.from_value hZ w z e n e hn ha
  let H := (graph w.castSucc z.castSucc e.castSucc (Fin.last m) n.castSucc).conj
    (StructuralTreeOperatorSyntax.step w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m) e.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ H
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz H
  have he1 : Derives Δ (successor e.castSucc z.castSucc) := by simpa only [Formula.raise, successor_rename] using under he H
  have hn1 : Derives Δ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hg := true_step_good _ _ _ _ _ hz1 he1 (.conjR hH)
  have hout := StructuralTreeRecursiveCorrespondence.branch_of_good hZ1 _ _ _ _ _ hn1 (.conjL hH) hg
  simpa only [Formula.raise, branch_rename] using hout

theorem branch_accepts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ordinal n)) (hb : Derives Γ (branch w z e n)) : Derives Γ (accepts w z e n) := by
  have hv := StructuralTreeEvaluationExistence.exists_value hZ w z e n hn
  let Y := evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hv
  apply Derives.exE (p := Y) hv
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Y
  have hn1 : Derives Ξ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hh := StructuralTreeHistory.from_value hZ1 _ _ _ _ _ hn1 hY
  let H := (graph w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc).conj
    (StructuralTreeOperatorSyntax.step w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw Y) H
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn1 H
  have hb2 : Derives Δ (branch w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, branch_rename] using under (under hb Y) H
  have hY2 : Derives Δ (evaluation w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Y, Formula.raise, evaluation_rename] using under hY H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hg := StructuralTreeRecursiveCorrespondence.good_of_branch hZ2 _ _ _ _ _ hw2 hn2 (.conjL hH) hb2
  have heq := StructuralTreeOperatorStep.on_good _ _ _ _ _ _ hg (.conjR hH)
  have hout : Derives Δ (accepts w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc) := output_subst _ _ _ _ _ _ heq hY2
  simpa only [Formula.raise, accepts_rename] using hout

theorem accepts_iff_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (ordinal n)) : Derives Γ ((accepts w z e n).iff (branch w z e n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact accepts_branch (ZFContext.add hZ _) _ _ _ _ (add hz _) (add he _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact branch_accepts (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))

theorem exclusive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hn : Derives Γ (ordinal n))
    (ha : Derives Γ (accepts w z e n)) (hr : Derives Γ (rejects w z e n)) : Derives Γ .bot :=
  .impE (StructuralTreeHistory.unit_distinct z e hz he) (StructuralTreeEvaluationUnique.unique hZ w z e n e z hn ha hr)

theorem rejects_not_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (ordinal n)) (hr : Derives Γ (rejects w z e n)) : Derives Γ (branch w z e n).neg := by
  apply Derives.impI
  exact exclusive (ZFContext.add hZ _) _ _ _ _ (add hz _) (add he _) (add hn _)
    (branch_accepts (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))) (add hr _)

theorem not_branch_rejects {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (ordinal n)) (hb : Derives Γ (branch w z e n).neg) : Derives Γ (rejects w z e n) := by
  have hv := StructuralTreeEvaluationExistence.exists_value hZ w z e n hn
  let Y := evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hv
  apply Derives.exE (p := Y) hv
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Y
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz Y
  have he1 : Derives Δ (successor e.castSucc z.castSucc) := by simpa only [Formula.raise, successor_rename] using under he Y
  have hn1 : Derives Δ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn Y
  have hb1 : Derives Δ (branch w.castSucc z.castSucc e.castSucc n.castSucc).neg := by simpa only [Formula.raise, Formula.neg, Formula.rename, branch_rename] using under hb Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hbits := Derives.conjR (StructuralTreeHistory.range hZ1 _ _ _ _ _ hw1 hz1 he1 hn1 hY)
  apply Derives.disjE hbits
  · have hout : Derives (Context.add (Formula.equal (Fin.last m) z.castSucc) Δ) (rejects w.castSucc z.castSucc e.castSucc n.castSucc) :=
      output_subst _ _ _ _ _ _ (.hyp (Or.inl rfl)) (add hY _)
    simpa only [Formula.raise, rejects_rename] using hout
  · have hac : Derives (Context.add (Formula.equal (Fin.last m) e.castSucc) Δ) (accepts w.castSucc z.castSucc e.castSucc n.castSucc) :=
      output_subst _ _ _ _ _ _ (.hyp (Or.inl rfl)) (add hY _)
    have hbr := accepts_branch (ZFContext.add hZ1 _) _ _ _ _ (add hz1 _) (add he1 _) (add hn1 _) hac
    exact .botE (.impE (add hb1 _) hbr)

theorem rejects_iff_not_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (ordinal n)) : Derives Γ ((rejects w z e n).iff (branch w z e n).neg) := by
  apply Derives.conjI
  · apply Derives.impI
    exact rejects_not_branch (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hz _) (add he _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact not_branch_rejects (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hz _) (add he _) (add hn _) (.hyp (Or.inl rfl))

theorem classification {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (ordinal n)) : Derives Γ ((accepts w z e n).disj (rejects w z e n)) := by
  apply SourcePropositional.by_cases (branch w z e n) _
  · exact .disjL (branch_accepts (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl)))
  · exact .disjR (not_branch_rejects (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hz _) (add he _) (add hn _) (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.StructuralTreeCheck
