import PPAC.Migration.Internal.NaturalRecursionTotal

/-! 自然前驱、历史输出与步进关系的唯一性共同给出算子单值性。 -/
namespace PPAC.Migration.Internal.NaturalRecursionDeterminism
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalRecursionSyntax

theorem step_points_equal {n m} {Γ : Context m} (hA : SequenceContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h t s u v y z : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn h x)) (hfun : Derives Γ (relationFunctional p ρ))
    (ht : Derives Γ (.mem t w))
    (hxt : Derives Γ (successor x t)) (hxs : Derives Γ (successor x s))
    (hu : Derives Γ (edge h t u)) (hv : Derives Γ (edge h s v))
    (hy : Derives Γ (rel p ρ u y)) (hz : Derives Γ (rel p ρ v z)) : Derives Γ (.equal y z) := by
  have htTrans := OmegaStructureAlgebra.element_transitive_at w t (OmegaStructureInduction.elements_transitive w hsep hw) ht
  have htNo := ObjectIrreflexivity.no_self_member t hA.foundation hA.pairing
  have hts := OmegaStructureAlgebra.successor_injective x t s htTrans htNo hxt hxs
  have hv' := IterationValues.edge_subst_input h s t v (eq_symm hts) hv
  have huv := GraphProperties.single_valued h x t u v hA.extensionality hf hu hv'
  have hz' := CheckedSequence.rel_subst_left p ρ v u z (eq_symm huv) hz
  exact .impE (.impE (functional_at p ρ u y z hfun) hy) hz'

theorem step_unique {n m} {Γ : Context m} (hA : SequenceContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x h y z : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn h x)) (hfun : Derives Γ (relationFunctional p ρ))
    (hy : Derives Γ (stepAt p ρ w x h y)) (hz : Derives Γ (stepAt p ρ w x h z)) : Derives Γ (.equal y z) := by
  let Y := stepWitness p ρ w x h y
  let Γy := Context.add Y (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_step p ρ w x h y _ hy
  have hAY := SequenceContext.add (SequenceContext.rename (SequenceContext.rename hA Fin.castSucc) Fin.castSucc) Y
  have hsepY : Derives Γy ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hsep Y
  have hwY : Derives Γy (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw Y
  have hfY : Derives Γy (functionOn h.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using OrderedPairElimination.under_two hf Y
  have hfunY : Derives Γy (relationFunctional p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, relationFunctional_rename, paramsUp] using OrderedPairElimination.under_two hfun Y
  have hzY : Derives Γy (stepAt p (paramsUp (paramsUp ρ)) w.castSucc.castSucc x.castSucc.castSucc h.castSucc.castSucc z.castSucc.castSucc) := by
    simpa only [Formula.raise, stepAt_rename, paramsUp] using OrderedPairElimination.under_two hz Y
  have hY : Derives Γy Y := .hyp (Or.inl rfl)
  let Z := stepWitness p (paramsUp (paramsUp ρ)) w.castSucc.castSucc x.castSucc.castSucc h.castSucc.castSucc z.castSucc.castSucc
  let Ξ := Context.add Z (Context.image Formula.raise (Context.image Formula.raise Γy))
  apply eliminate_step p (paramsUp (paramsUp ρ)) w.castSucc.castSucc x.castSucc.castSucc h.castSucc.castSucc z.castSucc.castSucc _ hzY
  have hAZ := SequenceContext.add (SequenceContext.rename (SequenceContext.rename hAY Fin.castSucc) Fin.castSucc) Z
  have hsepZ : Derives Ξ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hsepY Z
  have hwZ : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hwY Z
  have hfZ : Derives Ξ (functionOn h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using OrderedPairElimination.under_two hfY Z
  have hfunZ : Derives Ξ (relationFunctional p (paramsUp (paramsUp (paramsUp (paramsUp ρ))))) := by
    simpa only [Formula.raise, relationFunctional_rename, paramsUp] using OrderedPairElimination.under_two hfunY Z
  have htZ : Derives Ξ (.mem (Fin.last m).castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) :=
    OrderedPairElimination.under_two (.conjL (.conjL hY)) Z
  have hsY_Z : Derives Ξ (successor x.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two (.conjR (.conjL hY)) Z
  have huZ : Derives Ξ (edge h.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using OrderedPairElimination.under_two (.conjL (.conjR hY)) Z
  have hyZ : Derives Ξ (rel p (paramsUp (paramsUp (paramsUp (paramsUp ρ)))) (Fin.last (m+1)).castSucc.castSucc y.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, rel_rename, paramsUp] using OrderedPairElimination.under_two (.conjR (.conjR hY)) Z
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  exact step_points_equal hAZ p (paramsUp (paramsUp (paramsUp (paramsUp ρ))))
    w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))
    y.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc hsepZ hwZ hfZ hfunZ htZ
    hsY_Z (.conjR (.conjL hZ)) huZ (.conjL (.conjR hZ)) hyZ (.conjR (.conjR hZ))

theorem operation_unique {n m} {Γ : Context m} (hA : SequenceContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h y z : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn h x)) (hfun : Derives Γ (relationFunctional p ρ))
    (hy : Derives Γ (operation p ρ w a x h y)) (hz : Derives Γ (operation p ρ w a x h z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hz _)
    · exact step_unique (SequenceContext.add (SequenceContext.add hA _) _) p ρ w x h y z
        (add (add hsep _) _) (add (add hw _) _) (add (add hf _) _) (add (add hfun _) _)
        (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl)))
        (NaturalRecursionTotal.pred_of_step p ρ w x h y (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hz _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl))))
        (NaturalRecursionTotal.pred_of_step p ρ w x h z (.hyp (Or.inl rfl))))
    · exact eq_trans (.conjR (.hyp (Or.inr (Or.inl rfl)))) (eq_symm (.conjR (.hyp (Or.inl rfl))))

theorem functional_at_history {n m} {Γ : Context m} (hA : SequenceContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a x h : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hf : Derives Γ (functionOn h x)) (hfun : Derives Γ (relationFunctional p ρ)) :
    Derives Γ (OrdinalRecursionDeterminism.functional (matrix p) (extend ρ w a) x h) := by
  apply Derives.allI
  apply Derives.allI
  simp only [extend_up, matrix_operator]
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := SequenceContext.rename (SequenceContext.rename hA Fin.castSucc) Fin.castSucc
  have hsep' : Derives Δ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hsep)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hf' : Derives Δ (functionOn h.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hfun' : Derives Δ (relationFunctional p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, relationFunctional_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hfun)
  apply Derives.impI
  apply Derives.impI
  exact operation_unique (SequenceContext.add (SequenceContext.add hA' _) _) p (paramsUp (paramsUp ρ))
    w.castSucc.castSucc a.castSucc.castSucc x.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add hsep' _) _) (add (add hw' _) _) (add (add hf' _) _) (add (add hfun' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem operator_deterministic {n m} {Γ : Context m} (hA : SequenceContext.Evidence Γ)
    (p : Formula (n+2)) (ρ : Fin n → Fin m) (w a : Fin m)
    (hsep : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hfun : Derives Γ (relationFunctional p ρ)) :
    Derives Γ (OrdinalRecursionDeterminism.deterministic (matrix p) (extend ρ w a)) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := SequenceContext.rename (SequenceContext.rename hA Fin.castSucc) Fin.castSucc
  have hsep' : Derives Δ ((Source.SetLanguage.separation OmegaStructureSyntax.transitiveMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hsep)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hfun' : Derives Δ (relationFunctional p (paramsUp (paramsUp ρ))) := by
    simpa only [Formula.raise, relationFunctional_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hfun)
  apply Derives.impI
  let M := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  have hM : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  simpa only [extend_up] using functional_at_history (SequenceContext.add hA' M) p (paramsUp (paramsUp ρ))
    w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hsep' M) (add hw' M) (.conjR hM) (add hfun' M)
end PPAC.Migration.Internal.NaturalRecursionDeterminism
