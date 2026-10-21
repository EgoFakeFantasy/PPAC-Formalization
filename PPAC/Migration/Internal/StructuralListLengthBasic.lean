import PPAC.Migration.Internal.StructuralListLengthSyntax

/-! 实际长度关系的自然范围、有效性、参数替换及真实长度存在。 -/
namespace PPAC.Migration.Internal.StructuralListLengthBasic
open Source SourceAlgebra SourceLogic StructuralListTraceSyntax StructuralListLengthSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem valid_of_length {m} {Γ : Context m} (w n l : Fin m) (hl : Derives Γ (hasLength w n l)) : Derives Γ (valid w n) := by
  let L := lengthBody w n l
  let Δ := Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_length w n l _ hl
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hout := intro_valid _ _ _ _ _ _ _ hL
  simpa only [Formula.raise, valid_rename] using hout

theorem length_member {m} {Γ : Context m} (w n l : Fin m) (hl : Derives Γ (hasLength w n l)) : Derives Γ (.mem l w) := by
  let L := lengthBody w n l
  let Δ := Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_length w n l _ hl
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact StructuralListTraceProperties.length_at _ _ _ _ _ _ _ hL

theorem code_member {m} {Γ : Context m} (w n l : Fin m) (hl : Derives Γ (hasLength w n l)) : Derives Γ (.mem n w) :=
  StructuralListValidity.range w n (valid_of_length w n l hl)

theorem from_existsTrace {m} {Γ : Context m} (w z e l d n : Fin m) (hf : Derives Γ (existsTrace w z e l d n)) : Derives Γ (hasLength w n l) := by
  let F := trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hout := intro_length _ _ _ _ _ _ _ hF
  simpa only [Formula.raise, hasLength_rename] using hout

theorem code_subst {m} {Γ : Context m} (w n p l : Fin m) (he : Derives Γ (.equal n p)) (hl : Derives Γ (hasLength w n l)) : Derives Γ (hasLength w p l) := by
  have hi : Derives Γ ((hasLength w.castSucc (Fin.last m) l.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hl
  have ho := Derives.eqSubst (hasLength w.castSucc (Fin.last m) l.castSucc) he hi
  simpa only [Formula.instantiate, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem intro_existsLength {m} {Γ : Context m} (w n l : Fin m) (hl : Derives Γ (.mem l w)) (hL : Derives Γ (hasLength w n l)) : Derives Γ (existsLength w n) := by
  apply Derives.exI l
  simp only [Formula.instantiate, Formula.rename, hasLength_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hl hL

theorem exists_length {m} {Γ : Context m} (w n : Fin m) (hv : Derives Γ (valid w n)) : Derives Γ (existsLength w n) := by
  let V := validBody w n
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
  apply eliminate_valid w n _ hv
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hlW := StructuralListTraceProperties.length_at _ _ _ _ _ _ _ hV
  have hLen := intro_length _ _ _ _ _ _ _ hV
  have hout := intro_existsLength _ _ _ hlW hLen
  simpa only [Formula.raise, existsLength_rename] using hout
end PPAC.Migration.Internal.StructuralListLengthBasic
