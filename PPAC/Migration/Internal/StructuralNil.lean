import PPAC.Migration.Internal.StructuralListUnits

/-! 原Nil实际值恰为内部一；完整唯一纤维和叶0的内部二值封装。 -/
namespace PPAC.Migration.Internal.StructuralNil
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic StructuralListSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem raw_unit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ (StructuralNodeSyntax.raw w z z e) :=
  StructuralNodeSyntax.intro_raw w z z e z (GodelUnpairTransitions.zero_code hZ w z hw hz) he

theorem at_unit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ (nilCode w e) :=
  intro_nil w e z hz (raw_unit hZ w z e hw hz he)

theorem value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (nilCode w n)) : Derives Γ (.equal n e) := by
  let N := nilWitness w n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_nil w n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz N
  have he1 : Derives Δ (successor e.castSucc z.castSucc) := by simpa only [Formula.raise, successor_rename] using under he N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hzs := OmegaUniversal.empty_unique z.castSucc (Fin.last m) (ZFContext.arithmetic hZ1).base.extensionality hz1 (.conjL hN)
  have hes := GodelUnpairArithmetic.successor_base_subst _ _ _ hzs he1
  have hsW := OmegaStructureAlgebra.zero_member _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 (.conjL hN)
  exact StructuralNodeCore.unique hZ1 _ _ _ _ _ hw1 hsW hsW (.conjR hN) (raw_unit hZ1 _ _ _ hw1 (.conjL hN) hes)

theorem value_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) : Derives Γ ((nilCode w n).iff (.equal n e)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact value (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hz _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hr := StructuralNodeSyntax.output_subst w z z e n (eq_symm (.hyp (Or.inl rfl))) (add (raw_unit hZ w z e hw hz he) _)
    exact intro_nil w n z (add hz _) hr

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) : Derives Γ (.mem n w) := by
  let N := nilWitness w n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_nil w n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  exact StructuralNodeProperties.range hZ1 _ _ _ _ hw1 (.conjR hN)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hr : Derives Γ (nilCode w r)) : Derives Γ (.equal n r) := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hn2 : Derives Δ (nilCode w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, nilCode_rename] using OrderedPairElimination.under_two hn U
  have hr2 : Derives Δ (nilCode w.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, nilCode_rename] using OrderedPairElimination.under_two hr U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  exact eq_trans (value hZ2 _ _ _ _ hw2 (.conjL hU) (.conjR hU) hn2) (eq_symm (value hZ2 _ _ _ _ hw2 (.conjL hU) (.conjR hU) hr2))

theorem unique_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (fiberNil w) := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heW := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hn := at_unit hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hu : Derives Δ (.all ((nilCode w.castSucc.castSucc.castSucc (Fin.last (m+2))).imp (.equal (Fin.last (m+2)) (Fin.last (m+1)).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let N := nilCode w.castSucc.castSucc.castSucc (Fin.last (m+2))
    let Ξ := Context.add N (Context.image Formula.raise Δ)
    have hZ3 : ZFContext.Evidence Ξ := ZFContext.under hZ2 N
    have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw2 N
    have hz3 : Derives Ξ (empty (Fin.last m).castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using under (Derives.conjL hU) N
    have he3 : Derives Ξ (successor (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using under (Derives.conjR hU) N
    exact value hZ3 _ _ _ _ hw3 hz3 he3 (.hyp (Or.inl rfl))
  have hout : Derives Δ (fiberNil w.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, Formula.rename, nilCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjI heW hn) hu
  simpa only [Formula.raise, fiberNil_rename] using hout

theorem leaf_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e two : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (htwo : Derives Γ (successor two e)) :
    Derives Γ (StructuralNodeSyntax.raw w z e two) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have heW := StructuralListUnits.member hZ w z e hw hz he
  have hp0 := mul_zero hZ w e z z hw heW hz hz
  have hs0 := NaturalArithmeticBounds.add_zero_left hZ w z e hw hz heW
  have hsq := mul_succ_backward hZ w e z e z e hw heW hzW he hp0 hs0
  have hzSum := add_zero hZ w e z hw heW hz
  have hpair : Derives Γ (GodelPairSyntax.code w z e e) := .disjL (.conjI (InsertLogic.new_member e z z he) (GodelPairSyntax.intro_lower w z e e e hsq hzSum))
  exact StructuralNodeSyntax.intro_raw w z e two e hpair htwo
end PPAC.Migration.Internal.StructuralNil
