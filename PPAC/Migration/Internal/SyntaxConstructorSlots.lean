import PPAC.Migration.Internal.SyntaxSlotSyntax

/-! 任意同根真实Shape中，每个原字段位置实际存在且精确等于给定原字段。 -/
namespace PPAC.Migration.Internal.SyntaxConstructorSlots
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxNumeralSyntax SyntaxSlotSyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem slot_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n t p l g : Fin m) (j : Fin k) (y : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((slot g j.val y).iff (.equal y (xs j))) := by
  apply Derives.conjI
  · apply Derives.impI
    let P := slot g j.val y
    let I := body g j.val y
    let Δ := Context.add I (Context.image Formula.raise (Context.add P Γ))
    apply eliminate_slot g j.val y _ (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ P) I
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) I
    have hc1 : Derives Δ (constructor k tag w.castSucc (fun a => (xs a).castSucc) n.castSucc) := by
      simpa only [Formula.raise, constructor_rename] using under (add hc P) I
    have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
      simpa only [Formula.raise, shape_rename] using under (add hs P) I
    have hI : Derives Δ I := .hyp (Or.inl rfl)
    have he := SyntaxNodeFields.edge_at_constructor hZ1 k tag w.castSucc (fun a => (xs a).castSucc)
      n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc j (Fin.last m) y.castSucc hw1 hc1 hs1 (.conjL hI)
    exact .impE (.conjL he) (.conjR hI)
  · apply Derives.impI
    let P := Formula.equal y (xs j)
    have hn := SyntaxNumerals.exists_numeral (ZFContext.add hZ P) j.val w (add hw P)
    let I := (Formula.mem (Fin.last m) w.castSucc).conj (numeral j.val (Fin.last m))
    let Δ := Context.add I (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := I) hn
    have hZ1 := ZFContext.under (ZFContext.add hZ P) I
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) I
    have hc1 : Derives Δ (constructor k tag w.castSucc (fun a => (xs a).castSucc) n.castSucc) := by
      simpa only [Formula.raise, constructor_rename] using under (add hc P) I
    have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
      simpa only [Formula.raise, shape_rename] using under (add hs P) I
    have hp : Derives Δ (.equal y.castSucc (xs j).castSucc) := under (.hyp (Or.inl rfl) : Derives (Context.add P Γ) P) I
    have hI : Derives Δ I := .hyp (Or.inl rfl)
    have he := SyntaxNodeFields.edge_at_constructor hZ1 k tag w.castSucc (fun a => (xs a).castSucc)
      n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc j (Fin.last m) y.castSucc hw1 hc1 hs1 (.conjR hI)
    have hout := intro_slot g.castSucc j.val y.castSucc (Fin.last m) (.conjR hI) (.impE (.conjR he) hp)
    simpa only [Formula.raise, slot_rename] using hout
end PPAC.Migration.Internal.SyntaxConstructorSlots
