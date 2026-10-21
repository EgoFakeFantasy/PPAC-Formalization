import PPAC.Migration.Internal.ObjectNaturalRecursion

/-! 实际算子的零点和自然后继方程，及实际递归图中的对应输出规律。 -/
namespace PPAC.Migration.Internal.NaturalRecursionLaws
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalRecursionSyntax NaturalEvaluationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem no_predecessor_at_empty {m} {Γ : Context m} (w z : Fin m) (hz : Derives Γ (empty z)) :
    Derives Γ (OmegaStructureSyntax.predecessor w z).neg := by
  apply Derives.impI
  let P := OmegaStructureSyntax.predecessor w z
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (successor z.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise (Context.add P Γ))
  have hp : Derives (Context.add P Γ) (.ex T) := .hyp (Or.inl rfl)
  apply Derives.exE (p := T) hp
  have hzT : Derives Ξ (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under (add hz P) T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  exact .impE (empty_at z.castSucc (Fin.last m) hzT) (InsertLogic.new_member z.castSucc (Fin.last m) (Fin.last m) (.conjR hT))

theorem operation_zero {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a z h y : Fin m)
    (hz : Derives Γ (empty z)) (hy : Derives Γ (operation p ρ w a z h y)) : Derives Γ (.equal y a) := by
  apply Derives.disjE hy
  · exact .botE (.impE (add (no_predecessor_at_empty w z hz) _) (NaturalRecursionTotal.pred_of_step p ρ w z h y (.hyp (Or.inl rfl))))
  · exact .conjR (.hyp (Or.inl rfl))

theorem operation_successor {n m} {Γ : Context m} (hA : SequenceContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a s r h u y : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hf : Derives Γ (functionOn h s)) (hu : Derives Γ (edge h r u)) (hy : Derives Γ (operation p ρ w a s h y)) :
    Derives Γ (rel p ρ u y) := by
  apply Derives.disjE hy
  · let P := stepAt p ρ w s h y
    let W := stepWitness p ρ w s h y
    let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.add P Γ)))
    apply eliminate_step p ρ w s h y _ (Derives.hyp (Or.inl rfl))
    have hAW := SequenceContext.add (SequenceContext.rename (SequenceContext.rename (SequenceContext.add hA P) Fin.castSucc) Fin.castSucc) W
    have hsepW : Derives Ξ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two (add hsep P) W
    have hwW : Derives Ξ (omega w.castSucc.castSucc) := by
      simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw P) W
    have hrW : Derives Ξ (.mem r.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two (add hr P) W
    have hsW : Derives Ξ (successor s.castSucc.castSucc r.castSucc.castSucc) := by
      simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two (add hs P) W
    have hfW : Derives Ξ (functionOn h.castSucc.castSucc s.castSucc.castSucc) := by
      simpa only [Formula.raise, functionOn_rename] using OrderedPairElimination.under_two (add hf P) W
    have huW : Derives Ξ (edge h.castSucc.castSucc r.castSucc.castSucc u.castSucc.castSucc) := by
      simpa only [Formula.raise, edge_rename] using OrderedPairElimination.under_two (add hu P) W
    have hW : Derives Ξ W := .hyp (Or.inl rfl)
    have ht := OmegaStructureAlgebra.element_transitive_at w.castSucc.castSucc r.castSucc.castSucc
      (OmegaStructureInduction.elements_transitive w.castSucc.castSucc hsepW hwW) hrW
    have hn := ObjectIrreflexivity.no_self_member r.castSucc.castSucc hAW.foundation hAW.pairing
    have hrt := OmegaStructureAlgebra.successor_injective s.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc ht hn hsW (.conjR (.conjL hW))
    have hEdge := IterationValues.edge_subst_input h.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc (Fin.last (m+1)) (eq_symm hrt) (.conjL (.conjR hW))
    have heq := GraphProperties.single_valued h.castSucc.castSucc s.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc hAW.extensionality hfW hEdge huW
    simpa only [Formula.raise, rel_rename, paramsUp] using
      CheckedSequence.rel_subst_left p (paramsUp (paramsUp ρ)) (Fin.last (m+1)) u.castSucc.castSucc y.castSucc.castSucc heq (.conjR (.conjR hW))
  · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (NaturalRecursionTotal.pred_intro w s r (add hr _) (add hs _)))

theorem recursor_zero {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a z d f y : Fin m)
    (hz : Derives Γ (empty z)) (hs : Derives Γ (successor d z))
    (hf : Derives Γ (OrdinalRecursionSyntax.recursor (matrix p) (extend ρ w a) f d))
    (hy : Derives Γ (edge f z y)) : Derives Γ (.equal y a) := by
  have hzd := InsertLogic.new_member d z z hs
  have hh := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at (matrix p) (extend ρ w a) f d z y (.conjR hf)) hzd) hy
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc z.castSucc).conj
    (OrdinalRecursionSyntax.operator (matrix p) (paramsUp (extend ρ w a)) z.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hzH : Derives Ξ (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hz H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hop : Derives Ξ (operation p (paramsUp ρ) w.castSucc a.castSucc z.castSucc (Fin.last m) y.castSucc) := by
    simpa only [extend_up, matrix_operator] using Derives.conjR hH
  exact operation_zero p (paramsUp ρ) w.castSucc a.castSucc z.castSucc (Fin.last m) y.castSucc hzH hop

theorem evaluation_zero {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a z y : Fin m)
    (hz : Derives Γ (empty z)) (hy : Derives Γ (evaluation p ρ w a z y)) : Derives Γ (.equal y a) := by
  let Y := witness p ρ w a z y
  let Ξ := Context.add Y (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_evaluation p ρ w a z y _ hy
  have hzY : Derives Ξ (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hz Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  exact recursor_zero p (paramsUp (paramsUp ρ)) w.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc hzY (.conjL (.conjL hY)) (.conjR (.conjL hY)) (.conjR hY)
end PPAC.Migration.Internal.NaturalRecursionLaws
