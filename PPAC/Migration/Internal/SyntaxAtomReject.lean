import PPAC.Migration.Internal.SyntaxAtomCases

/-! 关系编号检查以及遍历全部内部自然标签的原子码拒绝；无外部标签界。 -/
namespace PPAC.Migration.Internal.SyntaxAtomReject
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem symbol_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f i s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (scalar w i s)) (hc : Derives Γ (memberCode w s x y n)) :
    Derives Γ ((membership w b f n).iff ((SyntaxNumeralSyntax.numeral 0 i).conj ((term w b f x).conj (term w b f y)))) := by
  have hz := SyntaxZeroScalar.index_iff hZ w i s hw hs
  apply Derives.conjI
  · apply Derives.impI
    have ht := SyntaxAtomTyping.member_types (ZFContext.add hZ (membership w b f n)) w b f s x y n (add hw _) (add hc _) (.hyp (Or.inl rfl))
    exact .conjI (.impE (add (.conjL hz) _) (.conjL ht)) (.conjR ht)
  · apply Derives.impI
    have ht : Derives (Context.add ((SyntaxNumeralSyntax.numeral 0 i).conj ((term w b f x).conj (term w b f y))) Γ)
        ((SyntaxNumeralSyntax.numeral 0 i).conj ((term w b f x).conj (term w b f y))) := .hyp (Or.inl rfl)
    exact intro_member _ _ _ _ _ _ _ (.conjI (.conjI (.impE (add (.conjR hz) _) (.conjL ht)) (.conjR ht)) (add hc _))

theorem bad_symbol {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f i s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (scalar w i s)) (hc : Derives Γ (memberCode w s x y n))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral 0 i).neg) : Derives Γ (membership w b f n).neg := by
  have hh := Derives.conjL (symbol_iff hZ w b f i s x y n hw hs hc)
  apply Derives.impI
  exact .impE (add hi _) (.conjL (.impE (add hh _) (.hyp (Or.inl rfl))))

theorem constructor_unknown_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k label : Nat)
    (w t p n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hbad : Derives Γ (SyntaxNumeralSyntax.numeral label t).neg) (hc : Derives Γ (constructor k label w xs n))
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let C := constructorBody k label w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k label w xs n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc t.castSucc p.castSucc n.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under hr C
  have hbad1 : Derives Δ (SyntaxNumeralSyntax.numeral label t.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using under hbad C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have heq := SyntaxNodeInjective.raw_tag_eq (ZFContext.under hZ C) k _ _ _ _ _ _ hw1 (under ht C) (under hp C) (.conjR hC) hr1
  exact .impE hbad1 (SyntaxNumeralSyntax.output_subst label _ _ heq (.conjL hC))

theorem member_unknown_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hbad : Derives Γ (SyntaxNumeralSyntax.numeral 2 t).neg) (hm : Derives Γ (membership w b f n))
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_member w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_three hw C
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under_three hr C
  have hbad1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 t.castSucc.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using under_three hbad C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact constructor_unknown_tag (zf_under_three hZ C) 3 2 _ _ _ _ _ hw1 (under_three ht C) (under_three hp C) hbad1 (.conjR hC) hr1

theorem equal_unknown_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (hbad : Derives Γ (SyntaxNumeralSyntax.numeral 3 t).neg) (hm : Derives Γ (equality w b f n))
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ .bot := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_equality w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using OrderedPairElimination.under_two hr C
  have hbad1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 t.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, SyntaxNumeralSyntax.numeral_rename] using OrderedPairElimination.under_two hbad C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact constructor_unknown_tag (ZFContext.under_two hZ C) 2 3 _ _ _ _ _ hw1 (OrderedPairElimination.under_two ht C) (OrderedPairElimination.under_two hp C) hbad1 (.conjR hC) hr1

theorem atomic_unknown_tag {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f t p n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hp : Derives Γ (.mem p w))
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 t).neg) (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 t).neg)
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 t).neg) (h3 : Derives Γ (SyntaxNumeralSyntax.numeral 3 t).neg)
    (hr : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ (atomic w b f n).neg := by
  apply Derives.impI
  apply Derives.disjE (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact constructor_unknown_tag (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 0 0 w t p n Fin.elim0 (add (add (add hw _) _) _) (add (add (add ht _) _) _) (add (add (add hp _) _) _) (add (add (add h0 _) _) _) (.conjR (.hyp (Or.inl rfl))) (add (add (add hr _) _) _)
    · exact constructor_unknown_tag (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 0 1 w t p n Fin.elim0 (add (add (add hw _) _) _) (add (add (add ht _) _) _) (add (add (add hp _) _) _) (add (add (add h1 _) _) _) (.conjR (.hyp (Or.inl rfl))) (add (add (add hr _) _) _)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact member_unknown_tag (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) w b f t p n (add (add (add hw _) _) _) (add (add (add ht _) _) _) (add (add (add hp _) _) _) (add (add (add h2 _) _) _) (.hyp (Or.inl rfl)) (add (add (add hr _) _) _)
    · exact equal_unknown_tag (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) w b f t p n (add (add (add hw _) _) _) (add (add (add ht _) _) _) (add (add (add hp _) _) _) (add (add (add h3 _) _) _) (.hyp (Or.inl rfl)) (add (add (add hr _) _) _)
end PPAC.Migration.Internal.SyntaxAtomReject
