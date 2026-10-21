import PPAC.Migration.Internal.StructuralTreeMarkerTransport

/-! 标志见证无关的原树判定；每个内部自然码有效或无效且二者互斥。 -/
namespace PPAC.Migration.Internal.StructuralTreeCanonical
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeValiditySyntax
open StructuralTreeRecursiveSyntax (accepts accepts_rename rejects rejects_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem valid_to_accepts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hv : Derives Γ (valid w n)) : Derives Γ (accepts w z e n) := by
  let V := validWitness w n
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_valid w n _ hv
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ V
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hz V
  have he2 : Derives Δ (successor e.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two he V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hzEq := OmegaUniversal.empty_unique _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjL (.conjL hV)) hz2
  have heEq := StructuralListUnits.unique hZ2 _ _ _ _ (.conjL (.conjL hV)) (.conjR (.conjL hV)) hz2 he2
  have hout := StructuralTreeMarkerTransport.accepts_transport _ _ _ _ _ _ hzEq heEq (.conjR hV)
  simpa only [Formula.raise, accepts_rename] using hout

theorem invalid_to_rejects {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hv : Derives Γ (invalid w n)) : Derives Γ (rejects w z e n) := by
  let V := invalidWitness w n
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_invalid w n _ hv
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ V
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hz V
  have he2 : Derives Δ (successor e.castSucc.castSucc z.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two he V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hzEq := OmegaUniversal.empty_unique _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjL (.conjL hV)) hz2
  have heEq := StructuralListUnits.unique hZ2 _ _ _ _ (.conjL (.conjL hV)) (.conjR (.conjL hV)) hz2 he2
  have hout := StructuralTreeMarkerTransport.rejects_transport _ _ _ _ _ _ hzEq heEq (.conjR hV)
  simpa only [Formula.raise, rejects_rename] using hout

theorem valid_iff_accepts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hn : Derives Γ (.mem n w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ ((valid w n).iff (accepts w z e n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact valid_to_accepts (ZFContext.add hZ _) _ _ _ _ (add hz _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_valid _ _ _ _ (add hn _) (add hz _) (add he _) (.hyp (Or.inl rfl))

theorem invalid_iff_rejects {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hn : Derives Γ (.mem n w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ ((invalid w n).iff (rejects w z e n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact invalid_to_rejects (ZFContext.add hZ _) _ _ _ _ (add hz _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_invalid _ _ _ _ (add hn _) (add hz _) (add he _) (.hyp (Or.inl rfl))

theorem classification {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((valid w n).disj (invalid w n)) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hn2 : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hn U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hbits := StructuralTreeCheck.classification hZ2 _ _ _ _ hw2 (.conjL hU) (.conjR hU) (NaturalOrderBasic.ordinal hZ2 _ _ hw2 hn2)
  have hout : Derives Δ ((valid w.castSucc.castSucc n.castSucc.castSucc).disj (invalid w.castSucc.castSucc n.castSucc.castSucc)) := by
    apply Derives.disjE hbits
    · exact .disjL (intro_valid _ _ _ _ (add hn2 _) (add (.conjL hU) _) (add (.conjR hU) _) (.hyp (Or.inl rfl)))
    · exact .disjR (intro_invalid _ _ _ _ (add hn2 _) (add (.conjL hU) _) (add (.conjR hU) _) (.hyp (Or.inl rfl)))
  simpa only [Formula.raise, Formula.rename, valid_rename, invalid_rename] using hout

theorem exclusive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) (hi : Derives Γ (invalid w n)) : Derives Γ .bot := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hv2 : Derives Δ (valid w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, valid_rename] using OrderedPairElimination.under_two hv U
  have hi2 : Derives Δ (invalid w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, invalid_rename] using OrderedPairElimination.under_two hi U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have ha := valid_to_accepts hZ2 _ _ _ _ (.conjL hU) (.conjR hU) hv2
  have hr := invalid_to_rejects hZ2 _ _ _ _ (.conjL hU) (.conjR hU) hi2
  exact StructuralTreeCheck.exclusive hZ2 _ _ _ _ (.conjL hU) (.conjR hU) (NaturalOrderBasic.ordinal hZ2 _ _ hw2 (.conjL hv2)) ha hr

theorem invalid_iff_not_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((invalid w n).iff (valid w n).neg) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    exact exclusive (ZFContext.add (ZFContext.add hZ _) _) _ _ (add (add hw _) _) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.disjE (add (classification hZ w n hw hn) _)
    · exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))
    · exact .hyp (Or.inl rfl)
end PPAC.Migration.Internal.StructuralTreeCanonical
