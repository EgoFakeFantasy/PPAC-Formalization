import PPAC.Migration.Internal.StrictLookupValueSyntax

/-! 严格查表的全内部单值性、合法域存在唯一、越界拒绝和原替换表字段对应。 -/
namespace PPAC.Migration.Internal.StrictLookupValue
open Source SourceAlgebra SourceLogic OmegaSyntax StrictLookupSyntax StrictLookupValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem output_natural {m} {Γ : Context m} (w n i y : Fin m) (hy : Derives Γ (returned w n i y)) :
    Derives Γ (.mem y w) := by
  let B := StrictLookupSyntax.body w n i y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact StructuralListProjection.selected_range true w.castSucc (Fin.last m) y.castSucc (.conjR hB)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y z : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (returned w n i y)) (hz : Derives Γ (returned w n i z)) : Derives Γ (.equal y z) :=
  StructuralListFieldValues.unique hZ w n i y z hw hi
    (StrictLookupDomainSyntax.returned_field w n i y hy) (StrictLookupDomainSyntax.returned_field w n i z hz)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hy : Derives Γ (returned w n i y)) :
    Derives Γ (uniqueOutput w n i y) := by
  apply Derives.allI
  apply Derives.impI
  let Z := returned w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hy1 : Derives Δ (returned w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (returned_rename w n i y Fin.castSucc) (under hy Z)
  exact unique (ZFContext.under hZ Z) w.castSucc n.castSucc i.castSucc (Fin.last m) y.castSucc hw1 (under hi Z) (.hyp (Or.inl rfl)) hy1

theorem at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hy : Derives Γ (returned w n i y)) :
    Derives Γ (value w n i y) :=
  .conjI hy (.conjI (output_natural w n i y hy) (unique_output hZ w n i y hw hi hy))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r))
    (hi : Derives Γ (.mem i r)) : Derives Γ (fiber w n i) := by
  have hir := StructuralListTraceOrder.member_member hZ w i r hw (StructuralListLengthBasic.length_member w n r hl) hi
  have he := StructuralListFieldValues.exists_value hZ w n i hw hir
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListFieldSyntax.field w.castSucc n.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hZ1 := ZFContext.under hZ Y
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Y)
  have hl1 : Derives Δ (StructuralListLengthSyntax.hasLength w.castSucc n.castSucc r.castSucc) := of_eq (StructuralListLengthSyntax.hasLength_rename w n r Fin.castSucc) (under hl Y)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hRun := Derives.impE (.conjR (StrictLookupDomainInduction.at_length hZ1 w.castSucc n.castSucc r.castSucc i.castSucc (Fin.last m) hw1 hl1 (under hir Y)))
    (.conjI (under hi Y) (.conjR hY))
  have ho := intro_fiber w.castSucc n.castSucc i.castSucc (Fin.last m) (at_candidate hZ1 w.castSucc n.castSucc i.castSucc (Fin.last m) hw1 (under hir Y) hRun)
  exact of_eq (fiber_rename w n i Fin.castSucc).symm ho

theorem has_output_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r))
    (hi : Derives Γ (.mem i w)) (he : Derives Γ (hasOutput w n i)) : Derives Γ (.mem i r) := by
  let Y := returned w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Y)
  have hl1 : Derives Δ (StructuralListLengthSyntax.hasLength w.castSucc n.castSucc r.castSucc) := of_eq (StructuralListLengthSyntax.hasLength_rename w n r Fin.castSucc) (under hl Y)
  exact .conjL (.impE (.conjL (StrictLookupDomainInduction.at_length (ZFContext.under hZ Y) w.castSucc n.castSucc r.castSucc i.castSucc (Fin.last m) hw1 hl1 (under hi Y))) (.hyp (Or.inl rfl)))

theorem fiber_iff_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((fiber w n i).iff (.mem i r)) := by
  apply Derives.conjI
  · apply Derives.impI
    let F := fiber w n i
    let Y := value w.castSucc n.castSucc i.castSucc (Fin.last m)
    let Δ := Context.add Y (Context.image Formula.raise (Context.add F Γ))
    apply Derives.exE (p := Y) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw F) Y)
    have hl1 : Derives Δ (StructuralListLengthSyntax.hasLength w.castSucc n.castSucc r.castSucc) := of_eq (StructuralListLengthSyntax.hasLength_rename w n r Fin.castSucc) (under (add hl F) Y)
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    exact has_output_bound (ZFContext.under (ZFContext.add hZ F) Y) w.castSucc n.castSucc r.castSucc i.castSucc hw1 hl1 (under (add hi F) Y)
      (intro_hasOutput w.castSucc n.castSucc i.castSucc (Fin.last m) (.conjL hY))
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w n r i (add hw _) (add hl _) (.hyp (Or.inl rfl))

theorem out_of_bounds_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r))
    (hi : Derives Γ (.mem i w)) (hb : Derives Γ (Formula.mem i r).neg) : Derives Γ (rejected w n i) := by
  apply Derives.impI
  exact .impE (add hb _) (has_output_bound (ZFContext.add hZ _) w n r i (add hw _) (add hl _) (add hi _) (.hyp (Or.inl rfl)))

theorem free_image_at_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c L J r i j q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxFreeSubstSyntax.codeConversion w a c L J))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c J)) (he : Derives Γ (GraphSyntax.edge r i j)) :
    Derives Γ ((returned w L i q).iff (SyntaxVariableSyntax.code false w j q)) := by
  have hm := Derives.conjR hr
  have ha := Derives.conjL (.conjL hm)
  have hi := SyntaxIndexMapSyntax.edge_source hZ w r a c i j hm he
  have hiW := StructuralListTraceOrder.member_member hZ w i a hw ha hi
  have hCode := FreeSubstImageCode.same_code hZ w a a c L J hw ha hl
  have hList := IndexTermImageCodeTyping.term_list false w J L a a c hCode
  have hLen := Derives.conjR (.conjL (.conjR (.conjR hList)))
  exact SyntaxTypeLocalTransfer.iff_trans (StrictLookupDomainInduction.at_length hZ w L a i q hw hLen hiW)
    (IndexTermImageCodeFields.at_edge hZ false w J L a a c r i j q hCode hr he)

theorem has_output_of_fiber {m} {Γ : Context m} (w n i : Fin m) (hf : Derives Γ (fiber w n i)) :
    Derives Γ (hasOutput w n i) := by
  let Y := value w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) hf
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  exact of_eq (hasOutput_rename w n i Fin.castSucc).symm
    (intro_hasOutput w.castSucc n.castSucc i.castSucc (Fin.last m) (.conjL hY))

theorem has_output_iff_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((hasOutput w n i).iff (.mem i r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact has_output_bound (ZFContext.add hZ _) w n r i (add hw _) (add hl _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact has_output_of_fiber w n i (actual_fiber (ZFContext.add hZ _) w n r i (add hw _) (add hl _) (.hyp (Or.inl rfl)))

theorem rejected_iff_not_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((rejected w n i).iff (Formula.mem i r).neg) := by
  have hh := has_output_iff_bound hZ w n r i hw hl hi
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    exact .impE (.hyp (Or.inr (Or.inl rfl))) (.impE (add (add (.conjR hh) _) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact out_of_bounds_rejected (ZFContext.add hZ _) w n r i (add hw _) (add hl _) (add hi _) (.hyp (Or.inl rfl))

theorem in_range_field_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i r)) :
    Derives Γ ((returned w n i y).iff (StructuralListFieldSyntax.field w n i y)) := by
  have hiW := StructuralListTraceOrder.member_member hZ w i r hw (StructuralListLengthBasic.length_member w n r hl) hi
  have hh := StrictLookupDomainInduction.at_length hZ w n r i y hw hl hiW
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjI (add hi _) (.hyp (Or.inl rfl)))

theorem checked_iff_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w n r)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((checked w n i y).iff ((Formula.mem i r).conj (StructuralListFieldSyntax.field w n i y))) := by
  have hh := StrictLookupDomainInduction.at_length hZ w n r i y hw hl hi
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hh) _) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .conjI (.conjI (add (StructuralListLengthBasic.code_member w n r hl) _) (add hi _))
      (.impE (add (.conjR hh) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.StrictLookupValue
