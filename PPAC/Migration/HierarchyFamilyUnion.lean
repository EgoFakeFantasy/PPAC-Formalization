import PPAC.Migration.HierarchyLayerCollection

/-! 全部早层的精确像集合与并成员式严格对应，实际层值是该集合的原Union。 -/
namespace PPAC.Migration.HierarchyFamilyUnion
open Source SourceAlgebra SourceLogic HierarchyLayerSyntax HierarchyLimitSyntax HierarchyFamilySyntax InsertSyntax

theorem forward {m} {Γ : Context m} (c a z : Fin m)
    (hr : Derives Γ (range c a)) (hz : Derives Γ (unionMember a z)) : Derives Γ (unionFiber c z) := by
  let W := unionWitnesses a z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_unionMember a z _ hz
  have hrW : Derives Ξ (range c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using OrderedPairElimination.under_two hr W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hi := intro_image a.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc (.conjL hW) (.conjL (.conjR hW))
  have hm := Derives.impE (.conjR (range_at c.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1)) hrW)) hi
  simpa only [Formula.raise, unionFiber_rename] using InsertLogic.fiber_intro c.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1)) hm (.conjR (.conjR hW))

theorem backward {m} {Γ : Context m} (c a z : Fin m)
    (hr : Derives Γ (range c a)) (hz : Derives Γ (unionFiber c z)) : Derives Γ (unionMember a z) := by
  let V := (Formula.mem (Fin.last m) c.castSucc).conj (.mem z.castSucc (Fin.last m))
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hz
  apply Derives.exE (p := V) hz
  have hrV : Derives Γv (range c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  have hi := Derives.impE (.conjL (range_at c.castSucc a.castSucc (Fin.last m) hrV)) (.conjL hV)
  let B := (Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).conj
    (layer (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add B (Context.image Formula.raise Γv)
  change Derives Γv (.ex B) at hi
  apply Derives.exE (p := B) hi
  have hzB : Derives Ξ (.mem z.castSucc.castSucc (Fin.last m).castSucc) := under (.conjR hV) B
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  simpa only [Formula.raise, unionMember_rename] using intro_unionMember a.castSucc.castSucc z.castSucc.castSucc
    (Fin.last (m+1)) (Fin.last m).castSucc (.conjI (.conjL hB) (.conjI (.conjR hB) hzB))

theorem union_of_equation {m} {Γ : Context m} (c a y : Fin m)
    (hr : Derives Γ (range c a)) (heq : Derives Γ (unionEquation a y)) : Derives Γ (unionOf y c) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hr' : Derives Δ (range c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have heq' : Derives Δ (unionEquation a.castSucc y.castSucc) := by
    simpa only [Formula.raise, unionEquation_rename] using Derives.rename Fin.castSucc heq
  have hc := equation_at a.castSucc y.castSucc (Fin.last m) heq'
  apply Derives.conjI
  · apply Derives.impI
    let M := Formula.mem (Fin.last m) y.castSucc
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    exact forward c.castSucc a.castSucc (Fin.last m) (add hr' M) (.impE (.conjL (add hc M)) hm)
  · apply Derives.impI
    let M := unionFiber c.castSucc (Fin.last m)
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    exact .impE (.conjR (add hc M)) (backward c.castSucc a.castSucc (Fin.last m) (add hr' M) hm)

theorem exists_union {m} {Γ : Context m} (a y : Fin m)
    (hx : Derives Γ (rangeExists a)) (heq : Derives Γ (unionEquation a y)) : Derives Γ (assembled a y) := by
  let C := range (Fin.last m) a.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hx
  apply Derives.exE (p := C) hx
  have heqC : Derives Ξ (unionEquation a.castSucc y.castSucc) := by
    simpa only [Formula.raise, unionEquation_rename] using under heq C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hu := union_of_equation (Fin.last m) a.castSucc y.castSucc hC heqC
  have hout : Derives Ξ (assembled a.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, range_rename, unionOf_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hC hu
  simpa only [Formula.raise, assembled_rename] using hout
end PPAC.Migration.HierarchyFamilyUnion
