import PPAC.Migration.Internal.SyntaxVariableDecodeSyntax

/-! 同码变量反向恢复唯一内部索引；实际解码纤维与原变量形状识别双条件。 -/
namespace PPAC.Migration.Internal.SyntaxVariableDecode
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxVariableSyntax SyntaxVariableDecodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem index_natural {m} {Γ : Context m} (bound : Bool) (w i n : Fin m)
    (hc : Derives Γ (code bound w i n)) : Derives Γ (.mem i w) := by
  let C := codeBody bound w i n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hc
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.tag_natural 0 _ _ Fin.elim0 _ (.conjL hC)

theorem index_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i j n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (code bound w i n)) (hj : Derives Γ (code bound w j n)) : Derives Γ (.equal i j) := by
  let I := codeBody bound w i n
  let Ξ := Context.add I (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hi
  have hj1 : Derives Ξ (code bound w.castSucc j.castSucc n.castSucc) := by simpa only [Formula.raise, code_rename] using under hj I
  let J := codeBody bound w.castSucc j.castSucc n.castSucc
  let Δ := Context.add J (Context.image Formula.raise Ξ)
  apply eliminate_code bound w.castSucc j.castSucc n.castSucc _ hj1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ I) J
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw I) J
  have hI : Derives Ξ I := .hyp (Or.inl rfl)
  have hI2 : Derives Δ ((scalar w.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      (constructor 1 (tag bound) w.castSucc.castSucc (fun _ => (Fin.last m).castSucc) n.castSucc.castSucc)) := by
    simpa only [I, codeBody, Formula.raise, Formula.rename, scalar_rename, constructor_rename] using under hI J
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hscalarEq := SyntaxNodeInjective.constructor_input_eq hZ2 1 (tag bound) (tag bound) _ _ _ _ 0 hw2 (.conjR hI2) (.conjR hJ)
  have hSame := SyntaxNodeInjective.scalar_output_subst _ _ _ _ hscalarEq (.conjL hI2)
  exact SyntaxNodes.tags_equal hZ2 0 0 _ _ _ Fin.elim0 Fin.elim0 _ hw2 hSame (.conjL hJ)

theorem unique_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) : Derives Γ (uniqueIndex bound w n i) := by
  apply Derives.allI
  apply Derives.impI
  let J := code bound w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add J (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw J
  have hc1 : Derives Δ (code bound w.castSucc i.castSucc n.castSucc) := by simpa only [Formula.raise, code_rename] using under hc J
  exact index_eq (ZFContext.under hZ J) bound _ _ _ _ hw1 (.hyp (Or.inl rfl)) hc1

theorem fiber_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) : Derives Γ (indexFiber bound w n) :=
  intro_fiber bound w n i (index_natural bound w i n hc) hc (unique_index hZ bound w n i hw hc)

theorem decode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (recognized bound w n)) : Derives Γ (indexFiber bound w n) := by
  let C := code bound w.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hr
  apply Derives.exE (p := C) hr
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := fiber_at_code (ZFContext.under hZ C) bound _ _ _ hw1 hC
  simpa only [Formula.raise, indexFiber_rename] using hout

theorem recognized_of_fiber {m} {Γ : Context m} (bound : Bool) (w n : Fin m)
    (hf : Derives Γ (indexFiber bound w n)) : Derives Γ (recognized bound w n) := by
  let F := ((Formula.mem (Fin.last m) w.castSucc).conj (code bound w.castSucc (Fin.last m) n.castSucc)).conj
    (uniqueIndex bound w.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hout := intro_recognized bound _ _ _ (.conjR (.conjL hF))
  simpa only [Formula.raise, recognized_rename] using hout

theorem decode_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((recognized bound w n).iff (indexFiber bound w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact decode (ZFContext.add hZ _) bound _ _ (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact recognized_of_fiber bound _ _ (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (code bound w i n)) : Derives Γ (.mem n w) := by
  let C := codeBody bound w i n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.constructor_range (ZFContext.under hZ C) 1 (tag bound) _ _ _ hw1 (.conjR hC)

theorem opposite_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w i j n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (code bound w i n)) (hj : Derives Γ (code (!bound) w j n)) : Derives Γ .bot := by
  cases bound with
  | false => exact SyntaxVariables.disjoint hZ w j i n hw hj hi
  | true => exact SyntaxVariables.disjoint hZ w i j n hw hi hj

theorem other_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k label : Nat) (hlabel : label ≠ tag bound)
    (w i n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hv : Derives Γ (code bound w i n)) (hc : Derives Γ (constructor k label w xs n)) : Derives Γ .bot := by
  let V := codeBody bound w i n
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hv
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw V
  have hc1 : Derives Δ (constructor k label w.castSucc (fun i => (xs i).castSucc) n.castSucc) := by simpa only [Formula.raise, constructor_rename] using under hc V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (ZFContext.under hZ V) 1 k (tag bound) label (Ne.symm hlabel) _ _ _ _ hw1 (.conjR hV) hc1
theorem other_raw_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (label : Nat) (hlabel : label ≠ tag bound)
    (w t p i n : Fin m) (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxNumeralSyntax.numeral label t))
    (hp : Derives Γ (.mem p w)) (hv : Derives Γ (code bound w i n))
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let V := codeBody bound w i n
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hv
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  let C := constructorBody 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply eliminate_constructor 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc _ (Derives.conjR hV)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ V) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw V) C
  have ht2 : Derives Δ (SyntaxNumeralSyntax.numeral label t.castSucc.castSucc) := by simpa only [Formula.raise, SyntaxNumeralSyntax.numeral_rename] using under (under ht V) C
  have hr2 : Derives Δ (StructuralNodeSyntax.raw w.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under (under hr V) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have htNat := SyntaxNumerals.range hZ2 label _ _ hw2 ht2
  have heq := SyntaxNodeInjective.raw_tag_eq hZ2 1 _ _ _ _ _ _ hw2 htNat (under (under hp V) C) (.conjR hC) hr2
  exact .impE (SyntaxNumerals.different hZ2 (tag bound) label (Ne.symm hlabel) _ _ (.conjL hC) ht2) heq
theorem unknown_raw_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w t p i n : Fin m) (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hbad : Derives Γ (SyntaxNumeralSyntax.numeral (tag bound) t).neg) (hv : Derives Γ (code bound w i n))
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let V := codeBody bound w i n
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hv
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  let C := constructorBody 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply eliminate_constructor 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc _ (Derives.conjR hV)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ V) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw V) C
  have hr2 : Derives Δ (StructuralNodeSyntax.raw w.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under (under hr V) C
  have hbad2 : Derives Δ (SyntaxNumeralSyntax.numeral (tag bound) t.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using under (under hbad V) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have heq := SyntaxNodeInjective.raw_tag_eq hZ2 1 _ _ _ _ _ _ hw2 (under (under ht V) C) (under (under hp V) C) (.conjR hC) hr2
  exact .impE hbad2 (SyntaxNumeralSyntax.output_subst (tag bound) _ _ heq (.conjL hC))
end PPAC.Migration.Internal.SyntaxVariableDecode
