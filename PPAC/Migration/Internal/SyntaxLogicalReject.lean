import PPAC.Migration.Internal.SyntaxLogicalDecode

/-! 七种逻辑局部分支拒绝错误标签及缺失的真实子式上下文状态。 -/
namespace PPAC.Migration.Internal.SyntaxLogicalReject
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxLogicalSyntax SyntaxContextReadSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (arity other : Nat) (hne : other ≠ tag) (w b f h n : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity other w xs n))
    (hs : Derives Γ (single tag advance w b f h n)) : Derives Γ .bot := by
  let C := singleBody tag advance w b f h n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hc1 : Derives Δ (constructor arity other w.castSucc (fun i => (xs i).castSucc) n.castSucc) := by
    simpa only [Formula.raise, constructor_rename] using under hc C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (ZFContext.under hZ C) arity 1 other tag hne _ _ _ _ hw1 hc1 (.conjL hC)

theorem single_unknown_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f h t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hbad : Derives Γ (SyntaxNumeralSyntax.numeral tag t).neg)
    (hs : Derives Γ (single tag advance w b f h n)) (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let C := singleBody tag advance w b f h n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc t.castSucc p.castSucc n.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under hr C
  have hbad1 : Derives Δ (SyntaxNumeralSyntax.numeral tag t.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using under hbad C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxAtomReject.constructor_unknown_tag (ZFContext.under hZ C) 1 tag _ _ _ _ _ hw1 (under ht C) (under hp C) hbad1 (.conjL hC) hr1

theorem binary_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (arity other : Nat) (hne : other ≠ (binaryTag kind)) (w b f h n : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor arity other w xs n))
    (hs : Derives Γ (binary kind w b f h n)) : Derives Γ .bot := by
  let C := binaryBody kind w b f h n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hc1 : Derives Δ (constructor arity other w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc) := by
    simpa only [Formula.raise, constructor_rename] using OrderedPairElimination.under_two hc C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (ZFContext.under_two hZ C) arity 2 other (binaryTag kind) hne _ _ _ _ hw1 hc1 (.conjL hC)

theorem binary_unknown_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hbad : Derives Γ (SyntaxNumeralSyntax.numeral (binaryTag kind) t).neg)
    (hs : Derives Γ (binary kind w b f h n)) (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let C := binaryBody kind w b f h n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f h n _ hs
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using OrderedPairElimination.under_two hr C
  have hbad1 : Derives Δ (SyntaxNumeralSyntax.numeral (binaryTag kind) t.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using OrderedPairElimination.under_two hbad C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxAtomReject.constructor_unknown_tag (ZFContext.under_two hZ C) 2 (binaryTag kind) _ _ _ _ _ hw1 (OrderedPairElimination.under_two ht C) (OrderedPairElimination.under_two hp C) hbad1 (.conjL hC) hr1

theorem single_not_check {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f h x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode tag w x n))
    (hb : Derives Γ (check advance h x b f).neg) : Derives Γ (single tag advance w b f h n).neg := by
  apply Derives.impI
  have ht := SyntaxLogicalTyping.single_types (ZFContext.add hZ (single tag advance w b f h n)) tag advance w b f h x n (add hw _) (add hc _) (.hyp (Or.inl rfl))
  exact .impE (add hb _) (.conjR ht)

theorem binary_not_reads {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f h x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n))
    (hb : Derives Γ ((read h x b f).conj (read h y b f)).neg) : Derives Γ (binary kind w b f h n).neg := by
  apply Derives.impI
  have ht := SyntaxLogicalTyping.binary_types (ZFContext.add hZ (binary kind w b f h n)) kind w b f h x y n (add hw _) (add hc _) (.hyp (Or.inl rfl))
  exact .impE (add hb _) (.conjR ht)

theorem quantified_not_read {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w b f h x n k : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode (quantifierTag universal) w x n)) (hk : Derives Γ (successor k b))
    (hb : Derives Γ (read h x k f).neg) : Derives Γ (quantified universal w b f h n).neg := by
  have hh := SyntaxLogicalTyping.quantified_iff hZ universal w b f h x n k hw hc hk
  apply Derives.impI
  exact .impE (add hb _) (.conjR (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl))))
end PPAC.Migration.Internal.SyntaxLogicalReject
