import PPAC.Migration.Internal.SyntaxIndexLiftPoint

/-! 提升关系在所有内部候选上的单值性；前驱单射与原图单值性均在对象层使用。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxIndexMapSyntax SyntaxIndexLiftSyntax SyntaxIndexLiftPoint
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c x y z : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c))
    (hy : Derives Γ (value r a x y)) (hz : Derives Γ (value r a x z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · let Z := (empty x).conj (empty y)
    have hZp : Derives (Context.add Z Γ) Z := .hyp (Or.inl rfl)
    have hzero := zero_output r a x z (.conjL hZp) (add hz Z)
    exact OmegaUniversal.empty_unique y z (ZFContext.arithmetic (ZFContext.add hZ Z)).base.extensionality (.conjR hZp) hzero
  · let V := shifted r a x y
    let B := shiftBody r a x y
    let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.add V Γ)))
    apply eliminate_shifted r a x y _ (.hyp (Or.inl rfl))
    have hZ2 := ZFContext.under_two (ZFContext.add hZ V) B
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by
      simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two (add hw V) B
    have hm2 : Derives Ξ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
      simpa only [Formula.raise, indexMap_rename] using OrderedPairElimination.under_two (add hm V) B
    have hz2 : Derives Ξ (value r.castSucc.castSucc a.castSucc.castSucc x.castSucc.castSucc z.castSucc.castSucc) := by
      simpa only [Formula.raise, value_rename] using OrderedPairElimination.under_two (add hz V) B
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have hkNat := StructuralListTraceOrder.member_member hZ2 _ _ _ hw2 (.conjL (.conjL hm2)) (.conjL (.conjL hB))
    have hd := at_successor hZ2 _ _ _ _ _ _ hw2 hkNat (.conjL (.conjR hB)) hz2
    let L := (edge r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).conj
      (successor z.castSucc.castSucc.castSucc (Fin.last (m+2)))
    let Δ := Context.add L (Context.image Formula.raise Ξ)
    have he : Derives Ξ (.ex L) := .conjR hd
    apply Derives.exE he
    have hZ3 := ZFContext.under hZ2 L
    have hm3 : Derives Δ (indexMap w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, indexMap_rename] using under hm2 L
    have he3 : Derives Δ (edge r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := by
      simpa only [Formula.raise, edge_rename] using under (Derives.conjR (.conjL hB)) L
    have hy3 : Derives Δ (successor y.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := by
      simpa only [Formula.raise, successor_rename] using under (Derives.conjR (.conjR hB)) L
    have hL : Derives Δ L := .hyp (Or.inl rfl)
    have hEq := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality
      (.conjL (.conjR hm3)) he3 (.conjL hL)
    have hyL := GodelUnpairArithmetic.successor_base_subst _ _ _ hEq hy3
    exact OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ3).base.extensionality hyL (.conjR hL)
end PPAC.Migration.Internal.SyntaxIndexLiftUnique
