import PPAC.Migration.Internal.SyntaxCheckedFieldSyntax

/-! 原构造及完整字段图上，任意纯谓词字段检查精确等价于原输入的对象谓词。 -/
namespace PPAC.Migration.Internal.SyntaxCheckedFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxSlotSyntax SyntaxCheckedFieldSyntax MinimalPredicates
open ReplacementPredicates (paramsUp)
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem iff_at_constructor {q m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a : Formula (q+1)) (ρ : Fin q → Fin m)
    (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n t p l g : Fin m) (j : Fin k)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((checked a ρ g j.val).iff (pred a ρ (xs j))) := by
  apply Derives.conjI
  · apply Derives.impI
    let P := checked a ρ g j.val
    let B := (slot g.castSucc j.val (Fin.last m)).conj (pred a (paramsUp ρ) (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ P) B
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) B
    have hc1 : Derives Δ (constructor k tag w.castSucc (fun i => (xs i).castSucc) n.castSucc) := by
      simpa only [Formula.raise, constructor_rename] using under (add hc P) B
    have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
      simpa only [Formula.raise, shape_rename] using under (add hs P) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hh := SyntaxConstructorSlots.slot_iff hZ1 k tag w.castSucc (fun i => (xs i).castSucc)
      n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc j (Fin.last m) hw1 hc1 hs1
    have he := Derives.impE (.conjL hh) (.conjL hB)
    have hout := pred_subst a (paramsUp ρ) (Fin.last m) (xs j).castSucc he (.conjR hB)
    simpa only [Formula.raise, pred_rename, paramsUp] using hout
  · apply Derives.impI
    have hh := SyntaxConstructorSlots.slot_iff hZ k tag w xs n t p l g j (xs j) hw hc hs
    have hslot := Derives.impE (.conjR hh) (.eqRefl (xs j))
    exact intro_checked a ρ g j.val (xs j) (add hslot _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxCheckedFields
