import PPAC.Migration.Internal.FormulaCodeShape

/-! 任意接受公式码实际解码全部字段并可重编码回原码；包含内部非标准码/长度候选。 -/
namespace PPAC.Migration.Internal.FormulaCodeAcceptedShape
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open SyntaxLogicalSyntax (singleCode binaryCode binaryTag)
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeShapeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.membership w b f n)) : Derives Γ (shapeFiber w n) := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply SyntaxAtomLogic.eliminate_member w b f n _ hc
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using SyntaxAtomLogic.under_three hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := FormulaCodeShape.from_constructor (SyntaxAtomLogic.zf_under_three hZ C) 3 2 _
    (three (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))) _ hw3 (.conjR hC)
  simpa only [Formula.raise, shapeFiber_rename] using hout

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.equality w b f n)) : Derives Γ (shapeFiber w n) := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxAtomLogic.eliminate_equality w b f n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := FormulaCodeShape.from_constructor (ZFContext.under_two hZ C) 2 3 _
    (two (Fin.last m).castSucc (Fin.last (m+1))) _ hw2 (.conjR hC)
  simpa only [Formula.raise, shapeFiber_rename] using hout

theorem atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.atomic w b f n)) : Derives Γ (shapeFiber w n) := by
  apply Derives.disjE hc
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact FormulaCodeShape.from_constructor (ZFContext.add (ZFContext.add hZ _) _) 0 0 w Fin.elim0 n
        (add (add hw _) _) (.conjR (.hyp (Or.inl rfl)))
    · exact FormulaCodeShape.from_constructor (ZFContext.add (ZFContext.add hZ _) _) 0 1 w Fin.elim0 n
        (add (add hw _) _) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact membership (ZFContext.add (ZFContext.add hZ _) _) w b f n (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact equality (ZFContext.add (ZFContext.add hZ _) _) w b f n (add (add hw _) _) (.hyp (Or.inl rfl))

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCase tag advance w b f n)) : Derives Γ (shapeFiber w n) := by
  let C := singleCaseBody tag advance w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := FormulaCodeShape.from_constructor (ZFContext.under hZ C) 1 tag w.castSucc (fun _ => Fin.last m) n.castSucc hw1 (.conjL hC)
  simpa only [Formula.raise, shapeFiber_rename] using hout

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCase kind w b f n)) : Derives Γ (shapeFiber w n) := by
  let C := binaryCaseBody kind w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := FormulaCodeShape.from_constructor (ZFContext.under_two hZ C) 2 (binaryTag kind) _
    (two (Fin.last m).castSucc (Fin.last (m+1))) _ hw2 (.conjL hC)
  simpa only [Formula.raise, shapeFiber_rename] using hout

theorem accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f)) : Derives Γ (shapeFiber w n) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have hh : Derives Γ ((allCases w n b f).imp (shapeFiber w n)) := by
    apply FormulaCodeCaseLogic.all_imp w n b f (shapeFiber w n)
    · apply Derives.impI
      exact atomic (ZFContext.add hZ _) w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single (ZFContext.add hZ _) 4 false w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary (ZFContext.add hZ _) 0 w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary (ZFContext.add hZ _) 1 w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary (ZFContext.add hZ _) 2 w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary (ZFContext.add hZ _) 3 w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single (ZFContext.add hZ _) 9 true w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single (ZFContext.add hZ _) 10 true w b f n (add hw _) (.hyp (Or.inl rfl))
  exact .impE hh (.conjR (.impE (.conjL hr) hc))

theorem reencoding {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g r : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f))
    (hs : Derives Γ (StructuralTreeOperatorSyntax.shape w n t p l g))
    (he : Derives Γ (StructuralTreeEncodeSyntax.encoding w t l g r)) :
    Derives Γ ((Formula.equal r n).conj (formulaCode w r b f)) := by
  have hsame := StructuralTreeEncodeReadback.decode_then_encode hZ w n t p l g r hw hs he
  exact .conjI hsame (FormulaCodeTransport.code_root w n b f r (eq_symm hsame) hc)
def roundTripAt {m} (w n b f t p l g : Fin m) : Formula m :=
  (StructuralTreeOperatorSyntax.shape w n t p l g).conj ((StructuralTreeEncodeSyntax.encoding w t l g n).conj (.all
    ((StructuralTreeEncodeSyntax.encoding w.castSucc t.castSucc l.castSucc g.castSucc (Fin.last m)).imp
      ((Formula.equal (Fin.last m) n.castSucc).conj
        (formulaCode w.castSucc (Fin.last m) b.castSucc f.castSucc)))))

theorem roundTripAt_rename {m k} (w n b f t p l g : Fin m) (s : Fin m → Fin k) :
    (roundTripAt w n b f t p l g).rename s =
      roundTripAt (s w) (s n) (s b) (s f) (s t) (s p) (s l) (s g) := by
  simp only [roundTripAt, Formula.rename, StructuralTreeEncodeSyntax.encoding_rename, StructuralTreeOperatorSyntax.shape_rename, formulaCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem at_shape {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f))
    (hs : Derives Γ (StructuralTreeOperatorSyntax.shape w n t p l g)) :
    Derives Γ (roundTripAt w n b f t p l g) := by
  apply Derives.conjI hs
  apply Derives.conjI (StructuralTreeEncodeSyntax.intro_encoding w t l g n p hs)
  apply Derives.allI
  apply Derives.impI
  let E := StructuralTreeEncodeSyntax.encoding w.castSucc t.castSucc l.castSucc g.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hc1 : Derives Δ (formulaCode w.castSucc n.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using under hc E
  have hs1 : Derives Δ (StructuralTreeOperatorSyntax.shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, StructuralTreeOperatorSyntax.shape_rename] using under hs E
  exact reencoding (ZFContext.under hZ E) w.castSucc n.castSucc b.castSucc f.castSucc t.castSucc p.castSucc l.castSucc g.castSucc
    (Fin.last m) hw1 hc1 hs1 (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.FormulaCodeAcceptedShape
