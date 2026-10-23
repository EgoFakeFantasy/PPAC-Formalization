import PPAC.Migration.Internal.StrictLookupDomainSyntax

/-! 严格查表准确域的Cons推进，保留实际前驱索引和列表头尾见证。 -/
namespace PPAC.Migration.Internal.StrictLookupDomainStep
open Source SourceAlgebra SourceLogic OmegaSyntax StrictLookupSyntax StrictLookupDomainSyntax
open StructuralListSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem cons_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s h t n j i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hl : Derives Γ (hasLength w t r)) (hp : Derives Γ (property w r))
    (hj : Derives Γ (.mem j w)) (hi : Derives Γ (successor i j)) :
    Derives Γ ((returned w n i y).iff ((Formula.mem i s).conj (StructuralListFieldSyntax.field w n i y))) := by
  have hChild := at_field w r t j y hp hl hj
  have hRun := StrictLookupRules.successor_iff hZ w h t n j i y hw hh ht hj hi hc
  have hField := StructuralListFieldCons.successor_iff hZ w h t n j i y hw hh ht hj hi hc
  apply Derives.conjI
  · apply Derives.impI
    have hR : Derives (Context.add (returned w n i y) Γ) (returned w n i y) := .hyp (Or.inl rfl)
    have hData := Derives.impE (add (.conjL hChild) _) (.impE (add (.conjL hRun) _) hR)
    exact .conjI (SyntaxIndexLiftOrder.successor_member (ZFContext.add hZ _) w j r i s (add hw _) (add hj _) (add hr _) (.conjL hData) (add hi _) (add hs _))
      (returned_field w n i y hR)
  · apply Derives.impI
    have hP : Derives (Context.add ((Formula.mem i s).conj (StructuralListFieldSyntax.field w n i y)) Γ)
      ((Formula.mem i s).conj (StructuralListFieldSyntax.field w n i y)) := .hyp (Or.inl rfl)
    have hBound := SyntaxIndexLiftOrder.predecessor_member (ZFContext.add hZ _) w r s i j (add hw _) (add hr _) (add hs _) (.conjL hP) (add hi _)
    exact .impE (add (.conjR hRun) _) (.impE (add (.conjR hChild) _) (.conjI hBound (.impE (add (.conjL hField) _) (.conjR hP))))

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s h t n i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (consCode w h t n))
    (hl : Derives Γ (hasLength w t r)) (hp : Derives Γ (property w r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((returned w n i y).iff ((Formula.mem i s).conj (StructuralListFieldSyntax.field w n i y))) := by
  apply SourcePropositional.by_cases (empty i)
  · let Z := empty i
    have hz : Derives (Context.add Z Γ) Z := .hyp (Or.inl rfl)
    have hBound := SyntaxIndexLiftOrder.zero_member (ZFContext.add hZ Z) w r s i (add hw Z) (add hr Z) (add hs Z) hz
    apply Derives.conjI
    · apply Derives.impI
      exact .conjI (add hBound _) (returned_field w n i y (.hyp (Or.inl rfl)))
    · apply Derives.impI
      let P := (Formula.mem i s).conj (StructuralListFieldSyntax.field w n i y)
      have hP : Derives (Context.add P (Context.add Z Γ)) P := .hyp (Or.inl rfl)
      have hEq := StructuralListFieldCons.zero_point (ZFContext.add (ZFContext.add hZ Z) P) w h t n i y
        (add (add hw Z) P) (add (add hh Z) P) (add (add ht Z) P) (add (add hc Z) P) (add hz P) (.conjR hP)
      exact returned_output_subst w n i h y (eq_symm hEq)
        (StrictLookupFailure.cons_zero_returns (ZFContext.add (ZFContext.add hZ Z) P) w h t n i
          (add (add hw Z) P) (add (add hh Z) P) (add (add ht Z) P) (add (add hc Z) P) (add hz P))
  · let Z := (empty i).neg
    have hd := OmegaStructureAlgebra.decomposition_at w i
      (OmegaStructureInduction.decomposition w (ZFContext.separation (ZFContext.add hZ Z) OmegaStructureSyntax.splitMatrix) (add hw Z)) (add hi Z)
    have hx := OmegaStructureAlgebra.nonzero_predecessor w i hd (Derives.hyp (Γ := Context.add Z Γ) (Or.inl rfl))
    let J := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add J (Context.image Formula.raise (Context.add Z Γ))
    apply Derives.exE (p := J) hx
    have hZ1 := ZFContext.under (ZFContext.add hZ Z) J
    have lift {p : Formula m} (hh : Derives Γ p) : Derives Δ p.raise := under (add hh Z) J
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (lift hw)
    have hs1 : Derives Δ (successor s.castSucc r.castSucc) := of_eq (successor_rename s r Fin.castSucc) (lift hs)
    have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (consCode_rename w h t n Fin.castSucc) (lift hc)
    have hl1 : Derives Δ (hasLength w.castSucc t.castSucc r.castSucc) := of_eq (hasLength_rename w t r Fin.castSucc) (lift hl)
    have hp1 : Derives Δ (property w.castSucc r.castSucc) := of_eq (property_rename w r Fin.castSucc) (lift hp)
    have hJ : Derives Δ J := .hyp (Or.inl rfl)
    have ho := cons_successor hZ1 w.castSucc r.castSucc s.castSucc h.castSucc t.castSucc n.castSucc (Fin.last m) i.castSucc y.castSucc hw1 (lift hr) hs1 (lift hh) (lift ht) hc1 hl1 hp1 (.conjL hJ) (.conjR hJ)
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, returned_rename, StructuralListFieldSyntax.field_rename]) ho

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s n i y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hp : Derives Γ (property w r)) (hl : Derives Γ (hasLength w n s)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((returned w n i y).iff ((Formula.mem i s).conj (StructuralListFieldSyntax.field w n i y))) := by
  have hx := StructuralListCodeLength.successor_view hZ w n r s hw hr hs hl
  let B := StructuralListCodeSyntax.consViewBody w n r
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hx
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (SyntaxRenameBinders.under_2 hs B)
  have hp2 : Derives Δ (property w.castSucc.castSucc r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, property_rename]) (SyntaxRenameBinders.under_2 hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := cons_point hZ2 w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc hw2 (SyntaxRenameBinders.under_2 hr B) hs2 (.conjL (.conjL hB)) (StructuralListLengthBasic.code_member _ _ _ (.conjR (.conjL hB))) (.conjR hB) (.conjR (.conjL hB)) hp2 (SyntaxRenameBinders.under_2 hi B)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, returned_rename, StructuralListFieldSyntax.field_rename]) ho

end PPAC.Migration.Internal.StrictLookupDomainStep
