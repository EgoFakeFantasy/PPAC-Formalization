import PPAC.Migration.Internal.ProofTreeEntrySyntax

/-! 实际数值构造器的自然值域与同码字段相等；全部数码见证均对象消去。 -/
namespace PPAC.Migration.Internal.ProofTreeConstructorFacts
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w n : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n)) : Derives Γ (.mem n w) := by
  let B := SyntaxNodeSyntax.constructorBody k tag w xs n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor k tag w xs n _ hn
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxNodes.range (ZFContext.under hZ B) k w.castSucc (Fin.last m) (fun i => (xs i).castSucc) n.castSucc hw1 (.conjR hB)

theorem field_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w n : Fin m)
    (xs ys : Fin k → Fin m) (i : Fin k) (hw : Derives Γ (omega w))
    (hx : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n)) (hy : Derives Γ (SyntaxNodeSyntax.constructor k tag w ys n)) :
    Derives Γ (.equal (xs i) (ys i)) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral i.val (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (SyntaxNumerals.exists_numeral hZ i.val w hw)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hx1 := of_eq (SyntaxNodeSyntax.constructor_rename k tag w xs n Fin.castSucc) (under hx B)
  have hy1 := of_eq (SyntaxNodeSyntax.constructor_rename k tag w ys n Fin.castSucc) (under hy B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hfx := RawCodeFieldAtConstructor.constructor_at hZ1 k tag w.castSucc (fun j => (xs j).castSucc) n.castSucc i (Fin.last m) (xs i).castSucc hw1 hx1 (.conjR hB)
  have hfy := RawCodeFieldAtConstructor.constructor_at hZ1 k tag w.castSucc (fun j => (ys j).castSucc) n.castSucc i (Fin.last m) (xs i).castSucc hw1 hy1 (.conjR hB)
  exact .impE (.conjL hfy) (.impE (.conjR hfx) (.eqRefl _))

end PPAC.Migration.Internal.ProofTreeConstructorFacts
