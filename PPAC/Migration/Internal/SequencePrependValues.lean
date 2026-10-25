import PPAC.Migration.Internal.SequencePrependSyntax

/-! Actual prepend values have exact zero/successor equations, total internal fibers and original sequence bounds. -/
namespace PPAC.Migration.Internal.SequencePrependValues
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequencePrependSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_zero {m} {Γ : Context m} (f d n i y : Fin m) (hi : Derives Γ (empty i)) :
    Derives Γ ((value f d n i y).iff (.equal y n)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := value f d n i y
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H)
    · exact .conjR (.hyp (Or.inl rfl))
    · let S := shift f d i y
      let R := (Formula.mem (Fin.last m) d.castSucc).conj ((successor i.castSucc (Fin.last m)).conj (edge f.castSucc (Fin.last m) y.castSucc))
      let Δ := Context.add R (Context.image Formula.raise (Context.add S (Context.add H Γ)))
      apply Derives.exE (p := R) (.hyp (Or.inl rfl))
      have hR : Derives Δ R := .hyp (Or.inl rfl)
      have hi1 := of_eq (empty_rename i Fin.castSucc) (under (add (add hi H) S) R)
      exact .botE (.impE (OmegaStructureAlgebra.successor_not_empty _ _ (.conjL (.conjR hR))) hi1)
  · apply Derives.impI
    exact .disjL (.conjI (add hi _) (.hyp (Or.inl rfl)))

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n i j y : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hs : Derives Γ (successor i j)) :
    Derives Γ ((value f d n i y).iff ((Formula.mem j d).conj (edge f j y))) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := value f d n i y
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add H Γ) H)
    · exact .botE (.impE (add (add (OmegaStructureAlgebra.successor_not_empty i j hs) H) _) (.conjL (.hyp (Or.inl rfl))))
    · let S := shift f d i y
      let R := (Formula.mem (Fin.last m) d.castSucc).conj ((successor i.castSucc (Fin.last m)).conj (edge f.castSucc (Fin.last m) y.castSucc))
      let Δ := Context.add R (Context.image Formula.raise (Context.add S (Context.add H Γ)))
      apply Derives.exE (p := R) (.hyp (Or.inl rfl))
      have hR : Derives Δ R := .hyp (Or.inl rfl)
      have hZ1 := ZFContext.under (ZFContext.add (ZFContext.add hZ H) S) R
      have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add (add hw H) S) R)
      have hd1 : Derives Δ (.mem d.castSucc w.castSucc) := under (add (add hd H) S) R
      have hs1 := of_eq (successor_rename i j Fin.castSucc) (under (add (add hs H) S) R)
      have hjN := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 hd1 (.conjL hR)
      have he := SyntaxIndexLiftOrder.successor_injective hZ1 _ _ _ _ hw1 hjN (.conjL (.conjR hR)) hs1
      have hm := mem_subst he (.conjL hR)
      have hf := StructuralListTraceOrder.edge_input_subst _ _ _ _ he (.conjR (.conjR hR))
      simpa only [Formula.raise,Formula.rename,edge_rename] using Derives.conjI hm hf
  · apply Derives.impI
    have hR : Derives (Context.add ((Formula.mem j d).conj (edge f j y)) Γ) ((Formula.mem j d).conj (edge f j y)) := .hyp (Or.inl rfl)
    exact .disjR (intro_shift _ _ _ _ _ (.conjL hR) (add hs _) (.conjR hR))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n i y z : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hf : Derives Γ (SequenceSyntax.sequence f d w))
    (hy : Derives Γ (value f d n i y)) (hz : Derives Γ (value f d n i z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · let H := (empty i).conj (.equal y n)
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have he := Derives.impE (.conjL (at_zero f d n i z (.conjL hH))) (add hz H)
    exact eq_trans (.conjR hH) (eq_symm he)
  · let H := shift f d i y
    let R := (Formula.mem (Fin.last m) d.castSucc).conj ((successor i.castSucc (Fin.last m)).conj (edge f.castSucc (Fin.last m) y.castSucc))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under (add hf H) R)
    have hz1 := of_eq (value_rename f d n i z Fin.castSucc) (under (add hz H) R)
    have hNorm := at_successor hZ1 w.castSucc f.castSucc d.castSucc n.castSucc i.castSucc (Fin.last m) z.castSucc hw1 (under (add hd H) R) (.conjL (.conjR hR))
    have hEdge := Derives.conjR (.impE (.conjL hNorm) hz1)
    exact GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality (.conjL hf1) (.conjR (.conjR hR)) hEdge

theorem range {m} {Γ : Context m} (f d n w i y : Fin m) (hf : Derives Γ (SequenceSyntax.sequence f d w))
    (hn : Derives Γ (.mem n w)) (hv : Derives Γ (value f d n i y)) : Derives Γ (.mem y w) := by
  apply Derives.disjE hv
  · exact mem_subst (eq_symm (.conjR (.hyp (Or.inl rfl)))) (add hn _)
  · let H := shift f d i y
    let R := (Formula.mem (Fin.last m) d.castSucc).conj ((successor i.castSucc (Fin.last m)).conj (edge f.castSucc (Fin.last m) y.castSucc))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under (add hf H) R)
    exact .impE (SequenceSyntax.bounded_at _ _ _ _ (.conjR hf1)) (.conjR (.conjR hR))

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n e i : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (hi : Derives Γ (.mem i e)) : Derives Γ (existsValue f d n i) := by
  have heN := OmegaStructureAlgebra.successor_member w e d (ZFContext.arithmetic hZ).base.extensionality hw hd he
  have hiN := StructuralListTraceOrder.member_member hZ w i e hw heN hi
  have hSplit := OmegaStructureAlgebra.decomposition_at w i (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiN
  apply Derives.disjE hSplit
  · apply Derives.exI n
    have hV : Derives (Context.add (empty i) Γ) (value f d n i n) := .disjL (.conjI (.hyp (Or.inl rfl)) (.eqRefl n))
    exact of_eq (by simp only [Formula.instantiate,value_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hV
  · let H := OmegaStructureSyntax.predecessor w i
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) R)
    have he1 := of_eq (successor_rename e d Fin.castSucc) (under (add he H) R)
    have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under (add hf H) R)
    have hjD := SyntaxIndexLiftOrder.predecessor_member hZ1 _ _ _ _ _ hw1 (under (add hd H) R) he1 (under (add hi H) R) (.conjR hR)
    have hy := SequenceLogic.value_at _ _ _ _ hf1 hjD
    let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (valueAt f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Ξ := Context.add S (Context.image Formula.raise Δ)
    apply Derives.exE (p := S) hy
    have hS : Derives Ξ S := .hyp (Or.inl rfl)
    have hs2 := of_eq (successor_rename i.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) S)
    have hv : Derives Ξ (value f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) := .disjR (intro_shift _ _ _ _ _ (under hjD S) hs2 (.conjL (.conjR hS)))
    have hout : Derives Ξ (existsValue f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc) := by
      apply Derives.exI (Fin.last (m+1))
      exact of_eq (by simp only [Formula.instantiate,value_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hv
    simpa only [Formula.raise,existsValue_rename] using hout

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n e i : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (hi : Derives Γ (.mem i e)) : Derives Γ (valueFiber f d n i) := by
  let R := value f.castSucc d.castSucc n.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (exists_value hZ w f d n e i hw hd he hf hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hu : Derives Δ (.all ((value f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let S := value f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add S (Context.image Formula.raise Δ)
    have hZ2 := ZFContext.under (ZFContext.under hZ R) S
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) S)
    have hf2 : Derives Ξ (SequenceSyntax.sequence f.castSucc.castSucc d.castSucc.castSucc w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,SequenceSyntax.sequence_rename]) (under (under hf R) S)
    have hOld := of_eq (value_rename f.castSucc d.castSucc n.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under hR S)
    exact unique hZ2 _ _ _ _ _ _ _ hw2 (under (under hd R) S) hf2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Δ (valueFiber f.castSucc d.castSucc n.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hu)
  simpa only [Formula.raise,valueFiber_rename] using hout

end PPAC.Migration.Internal.SequencePrependValues
