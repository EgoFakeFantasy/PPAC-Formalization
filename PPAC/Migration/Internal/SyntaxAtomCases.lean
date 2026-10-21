import PPAC.Migration.Internal.SyntaxAtomDecode

/-! 原子类型的范围、四分支精确性及错误构造标签排除。 -/
namespace PPAC.Migration.Internal.SyntaxAtomCases
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem context {m} {Γ : Context m} (w b f n : Fin m) (ha : Derives Γ (atomic w b f n)) : Derives Γ (contexts w b f) := by
  apply Derives.disjE ha
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))

theorem nullary_atomic_iff {m} {Γ : Context m} (truth : Bool) (w b f n : Fin m)
    (hc : Derives Γ (constructor 0 (nullaryTag truth) w Fin.elim0 n)) : Derives Γ ((atomic w b f n).iff (contexts w b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact context _ _ _ _ (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hn : Derives (Context.add (contexts w b f) Γ) (nullary truth w b f n) := .conjI (.hyp (Or.inl rfl)) (add hc _)
    cases truth with
    | false => exact .disjL (.disjL hn)
    | true => exact .disjL (.disjR hn)

theorem member_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (membership w b f n)) : Derives Γ (.mem n w) := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_member w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_three hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.constructor_range (zf_under_three hZ C) 3 2 _ _ _ hw1 (.conjR hC)

theorem member_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k label : Nat) (hlabel : label ≠ 2)
    (w b f n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor k label w xs n)) (hm : Derives Γ (membership w b f n)) : Derives Γ .bot := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_member w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_three hw C
  have hc1 : Derives Δ (constructor k label w.castSucc.castSucc.castSucc (fun i => (xs i).castSucc.castSucc.castSucc) n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, constructor_rename] using under_three hc C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (zf_under_three hZ C) k 3 label 2 hlabel _ _ _ _ hw1 hc1 (.conjR hC)

theorem equal_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (equality w b f n)) : Derives Γ (.mem n w) := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_equality w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxNodeInjective.constructor_range (ZFContext.under_two hZ C) 2 3 _ _ _ hw1 (.conjR hC)

theorem equal_conflict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k label : Nat) (hlabel : label ≠ 3)
    (w b f n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (constructor k label w xs n)) (hm : Derives Γ (equality w b f n)) : Derives Γ .bot := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_equality w b f n _ hm
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hc1 : Derives Δ (constructor k label w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc) := by
    simpa only [Formula.raise, constructor_rename] using OrderedPairElimination.under_two hc C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint (ZFContext.under_two hZ C) k 2 label 3 hlabel _ _ _ _ hw1 hc1 (.conjR hC)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (atomic w b f n)) : Derives Γ (.mem n w) := by
  apply Derives.disjE ha
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact SyntaxNodeInjective.constructor_range (ZFContext.add (ZFContext.add hZ _) _) 0 0 _ Fin.elim0 _ (add (add hw _) _) (.conjR (.hyp (Or.inl rfl)))
    · exact SyntaxNodeInjective.constructor_range (ZFContext.add (ZFContext.add hZ _) _) 0 1 _ Fin.elim0 _ (add (add hw _) _) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact member_range (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ (add (add hw _) _) (.hyp (Or.inl rfl))
    · exact equal_range (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ (add (add hw _) _) (.hyp (Or.inl rfl))

theorem member_atomic_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) : Derives Γ ((atomic w b f n).iff (memberTypes w b f s x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    have hrel : Derives (Context.add (atomic w b f n) Γ) (membership w b f n) := by
      apply Derives.disjE (.hyp (Or.inl rfl))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact .botE (SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 3 0 2 0 (by decide) _ (three s x y) Fin.elim0 _ (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.conjR (.hyp (Or.inl rfl))))
        · exact .botE (SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 3 0 2 1 (by decide) _ (three s x y) Fin.elim0 _ (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.conjR (.hyp (Or.inl rfl))))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact .hyp (Or.inl rfl)
        · exact .botE (equal_conflict (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 3 2 (by decide) w b f n (three s x y) (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.hyp (Or.inl rfl)))
    exact SyntaxAtomTyping.member_types (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hc _) hrel
  · apply Derives.impI
    have hh := intro_member w b f s x y n (.conjI (.hyp (Or.inl rfl)) (add hc _))
    exact .disjR (.disjL hh)

theorem equal_atomic_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) : Derives Γ ((atomic w b f n).iff (equalTypes w b f x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    have hrel : Derives (Context.add (atomic w b f n) Γ) (equality w b f n) := by
      apply Derives.disjE (.hyp (Or.inl rfl))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact .botE (SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 2 0 3 0 (by decide) _ (two x y) Fin.elim0 _ (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.conjR (.hyp (Or.inl rfl))))
        · exact .botE (SyntaxConstructors.disjoint (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 2 0 3 1 (by decide) _ (two x y) Fin.elim0 _ (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.conjR (.hyp (Or.inl rfl))))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact .botE (member_conflict (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 2 3 (by decide) w b f n (two x y) (add (add (add hw _) _) _) (add (add (add hc _) _) _) (.hyp (Or.inl rfl)))
        · exact .hyp (Or.inl rfl)
    exact SyntaxAtomTyping.equal_types (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hc _) hrel
  · apply Derives.impI
    have hh := intro_equality w b f x y n (.conjI (.hyp (Or.inl rfl)) (add hc _))
    exact .disjR (.disjR hh)
end PPAC.Migration.Internal.SyntaxAtomCases
