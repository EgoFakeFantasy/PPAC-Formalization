import PPAC.Migration.Internal.FormulaCodeAcceptedShape

/-! 任意内部实际长度与原精确字段数对应；错误长度不只检查外部标准长度样本。 -/
namespace PPAC.Migration.Internal.FormulaCodeFieldArity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax SyntaxNumeralSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forest_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (p l : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (forest k w xs p)) (hl : Derives Γ (hasLength w p l)) :
    Derives Γ (numeral k l) := by
  have he := SyntaxNumerals.exists_numeral hZ k w hw
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (numeral k (Fin.last m))
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply Derives.exE (p := L) he
  have hZ1 := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hf1 : Derives Δ (forest k w.castSucc (fun i => (xs i).castSucc) p.castSucc) := by
    simpa only [Formula.raise, forest_rename] using under hf L
  have hl1 : Derives Δ (hasLength w.castSucc p.castSucc l.castSucc) := by
    simpa only [Formula.raise, hasLength_rename] using under hl L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hn := SyntaxForestLength.at_numeral hZ1 k w.castSucc (fun i => (xs i).castSucc) p.castSucc (Fin.last m)
    hw1 hf1 (.conjR hL)
  have hs := StructuralListLengthUnique.unique hZ1 w.castSucc p.castSucc (Fin.last m) l.castSucc hw1 hn hl1
  have hout := output_subst k (Fin.last m) l.castSucc hs (.conjR hL)
  simpa only [Formula.raise, numeral_rename] using hout

theorem node_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w t : Fin m) (xs : Fin k → Fin m)
    (n a p l g : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (node k w t xs n))
    (hs : Derives Γ (shape w n a p l g)) : Derives Γ (numeral k l) := by
  let N := nodeBody k w t xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w t xs n _ hn
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hs1 : Derives Δ (shape w.castSucc n.castSucc a.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hq := SyntaxForests.range hZ1 k w.castSucc (fun i => (xs i).castSucc) (Fin.last m) hw1 (.conjL (.conjR hN))
  have hp := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR hs1))
  have he := StructuralNodeCore.injective hZ1 _ _ _ _ _ _ hw1 (.conjL hN) hq (.conjL (.conjL hs1)) hp
    (.conjR (.conjR hN)) (.conjR (.conjL hs1))
  have hl := StructuralListLengthBasic.code_subst _ _ _ _ (eq_symm (.conjR he)) (.conjL (.conjR hs1))
  have hout := forest_length hZ1 k _ _ _ _ hw1 (.conjL (.conjR hN)) hl
  simpa only [Formula.raise, numeral_rename] using hout

theorem constructor_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n a p l g : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n))
    (hs : Derives Γ (shape w n a p l g)) : Derives Γ (numeral k l) := by
  let C := constructorBody k tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc a.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := node_length (ZFContext.under hZ C) k w.castSucc (Fin.last m) (fun i => (xs i).castSucc)
    n.castSucc a.castSucc p.castSucc l.castSucc g.castSucc hw1 (.conjR hC) hs1
  simpa only [Formula.raise, numeral_rename] using hout

theorem wrong_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n a p l g : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n))
    (hs : Derives Γ (shape w n a p l g)) (hb : Derives Γ (numeral k l).neg) : Derives Γ .bot :=
  .impE hb (constructor_length hZ k tag w xs n a p l g hw hc hs)
theorem constructor_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n a p l g : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n))
    (hs : Derives Γ (shape w n a p l g)) : Derives Γ (numeral tag a) := by
  let C := constructorBody k tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hc
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc a.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hp := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR hs1))
  have he := SyntaxNodeInjective.raw_tag_eq hZ1 k w.castSucc (Fin.last m) a.castSucc p.castSucc
    (fun i => (xs i).castSucc) n.castSucc hw1 (.conjL (.conjL hs1)) hp (.conjR hC) (.conjR (.conjL hs1))
  have hout := output_subst tag (Fin.last m) a.castSucc he (.conjL hC)
  simpa only [Formula.raise, numeral_rename] using hout

end PPAC.Migration.Internal.FormulaCodeFieldArity
