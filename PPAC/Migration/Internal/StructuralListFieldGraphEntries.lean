import PPAC.Migration.Internal.StructuralListFieldGraphSyntax

/-! 字段索引对精确像排除图杂项，并逐实际见证解码原Kuratowski输入和字段值。 -/
namespace PPAC.Migration.Internal.StructuralListFieldGraphEntries
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem decode_entry {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g p i y : Fin m)
    (hg : Derives Γ (graph w n l g)) (hp : Derives Γ (.mem p g)) (ho : Derives Γ (ordered p i y)) :
    Derives Γ ((Formula.mem i l).conj (field w n i y)) := by
  have hx := Derives.impE (.conjL (graph_at w n l g p hg)) hp
  let X := (Formula.mem (Fin.last m) l.castSucc).conj (entry w.castSucc n.castSucc (Fin.last m) p.castSucc)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at hx
  apply Derives.exE (p := X) hx
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  let Y := (field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy : Derives Ξ (.ex Y) := .conjR hX
  apply Derives.exE (p := Y) hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ X) Y
  have ho2 : Derives Δ (ordered p.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under (under ho X) Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have heq := OrderedPairLogic.injective _ _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjR hY) ho2 (.eqRefl _)
  have hm := mem_subst (.conjL heq) (under (.conjL hX) Y)
  have hf := StructuralListFieldSyntax.index_subst _ _ _ _ _ (.conjL heq) (.conjL hY)
  have hout := Derives.conjI hm (StructuralListFieldSyntax.output_subst _ _ _ _ _ (.conjR heq) hf)
  simpa only [Formula.raise, Formula.rename, field_rename] using hout

theorem entry_on {m} {Γ : Context m} (w n l g p : Fin m) (hg : Derives Γ (graph w n l g))
    (hp : Derives Γ (.mem p g)) : Derives Γ (entryOn l p) := by
  have hx := Derives.impE (.conjL (graph_at w n l g p hg)) hp
  let X := (Formula.mem (Fin.last m) l.castSucc).conj (entry w.castSucc n.castSucc (Fin.last m) p.castSucc)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at hx
  apply Derives.exE (p := X) hx
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  let Y := (field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy : Derives Ξ (.ex Y) := .conjR hX
  apply Derives.exE (p := Y) hy
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hout := GraphLogic.entry_intro _ _ _ _ (under (.conjL hX) Y) (.conjR hY)
  simpa only [Formula.raise, entryOn_rename] using hout

theorem entries {m} {Γ : Context m} (w n l g : Fin m) (hg : Derives Γ (graph w n l g)) : Derives Γ (entriesOn g l) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) g.castSucc
  have hg1 : Derives (Context.add M (Context.image Formula.raise Γ)) (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, graph_rename] using under hg M
  exact entry_on _ _ _ _ _ hg1 (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListFieldGraphEntries
