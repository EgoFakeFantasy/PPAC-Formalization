import PPAC.Migration.Internal.FormulaCodeShapeSyntax

/-! 任意精确原构造码实际解码为唯一完整字段图；不要求子树有效性或宿主解码器。 -/
namespace PPAC.Migration.Internal.FormulaCodeShape
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax
open StructuralTreeOperatorSyntax FormulaCodeShapeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forest_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (p : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (forest k w xs p)) :
    Derives Γ (StructuralListTraceSyntax.valid w p) := by
  have he := SyntaxNumerals.exists_numeral hZ k w hw
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral k (Fin.last m))
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) he
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hf1 : Derives Δ (forest k w.castSucc (fun i => (xs i).castSucc) p.castSucc) := by
    simpa only [Formula.raise, forest_rename] using under hf L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hl := SyntaxForestLength.at_numeral (ZFContext.under hZ L) k w.castSucc (fun i => (xs i).castSucc)
    p.castSucc (Fin.last m) hw1 hf1 (.conjR hL)
  have hout := StructuralListLengthBasic.valid_of_length _ _ _ hl
  simpa only [Formula.raise, StructuralListTraceSyntax.valid_rename] using hout

theorem unique_formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ (uniqueShape w n t p l g) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let S := shapeBody w n
  let Δ := Context.add S (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using StructuralListLengthSyntax.under_four hw S
  have hs4 : Derives Δ (shape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
      t.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc
      l.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using StructuralListLengthSyntax.under_four hs S
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact StructuralTreeShapeUnique.unique (StructuralListLengthSyntax.zf_under_four hZ S) _ _ _ _ _ _ _ _ _ _ hw4 hS hs4

theorem from_node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w t : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (node k w t xs n)) : Derives Γ (shapeFiber w n) := by
  let N := nodeBody k w t xs n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w t xs n _ hn
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hv := forest_valid hZ1 k w.castSucc (fun i => (xs i).castSucc) (Fin.last m) hw1 (.conjL (.conjR hN))
  have hd := StructuralListFieldDecode.exists_decoded hZ1 w.castSucc (Fin.last m) hw1 hv
  let D := StructuralListFieldGraphSyntax.decodedBody w.castSucc (Fin.last m)
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply StructuralListFieldDecode.eliminate_decoded w.castSucc (Fin.last m) _ hd
  have hZ3 := ZFContext.under_two hZ1 D
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw1 D
  have hN3 : Derives Δ ((Formula.mem t.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc).conj
        (StructuralNodeSyntax.raw w.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc))) := by
    simpa only [N, nodeBody, Formula.raise, Formula.rename, forest_rename, StructuralNodeSyntax.raw_rename] using OrderedPairElimination.under_two hN D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hs : Derives Δ (shape w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))) :=
    .conjI (.conjI (.conjL hN3) (.conjR (.conjR hN3))) (.conjI (.conjR (.conjL hD)) (.conjR hD))
  have hu := unique_formula hZ3 _ _ _ _ _ _ hw3 hs
  have hout := intro_fiber _ _ _ _ _ _ hs hu
  simpa only [Formula.raise, shapeFiber_rename] using hout

theorem from_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n)) : Derives Γ (shapeFiber w n) := by
  let C := constructorBody k tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := from_node (ZFContext.under hZ C) k w.castSucc (Fin.last m) (fun i => (xs i).castSucc) n.castSucc hw1 (.conjR hC)
  simpa only [Formula.raise, shapeFiber_rename] using hout
end PPAC.Migration.Internal.FormulaCodeShape
