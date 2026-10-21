import PPAC.Migration.Internal.SyntaxRenameTermExistence

/-! 所有内部纯项在任意合法完整映射图下的实际唯一重命名纤维和类型双向合同。 -/
namespace PPAC.Migration.Internal.SyntaxRenameTerm
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxIndexMapSyntax SyntaxRenameTermSyntax
open SyntaxTermSyntax (term term_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d))
    (hn : Derives Γ (term w a b n)) : Derives Γ (fiber w r s a b c d n) := by
  have he := SyntaxRenameTermExistence.for_term hZ w r s a b c d n hw hm hn
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have ht := SyntaxRenameTermTyping.target_term _ _ _ _ _ _ _ _ _ (.conjR hQ)
  have hu : Derives Ξ (.all
      ((renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
        c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let R := renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
      c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add R (Context.image Formula.raise Ξ)
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 R
    have hq2 : Derives Δ (renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
        c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, renamed_rename] using under (Derives.conjR hQ) R
    exact SyntaxRenameTermUnique.unique (ZFContext.under hZ1 R) _ _ _ _ _ _ _ _ _ _ hw2 (.hyp (Or.inl rfl)) hq2
  have ho : Derives Ξ (fiber w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, renamed_rename, term_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjI (.conjL hQ) (.conjI (.conjR hQ) ht)) hu
  simpa only [Formula.raise, fiber_rename] using ho

theorem term_of_exists {m} {Γ : Context m} (w r s a b c d n : Fin m)
    (he : Derives Γ (existsRenamed w r s a b c d n)) : Derives Γ (term w a b n) := by
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj
    (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at he
  apply Derives.exE he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxRenameTermTyping.source_term _ _ _ _ _ _ _ _ _ (.conjR hQ)
  simpa only [Formula.raise, term_rename] using ho

theorem term_of_fiber {m} {Γ : Context m} (w r s a b c d n : Fin m)
    (he : Derives Γ (fiber w r s a b c d n)) : Derives Γ (term w a b n) := by
  let Q := ((Formula.mem (Fin.last m) w.castSucc).conj
    ((renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
      (term w.castSucc c.castSucc d.castSucc (Fin.last m)))).conj
    (.all ((renamed w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
      c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at he
  apply Derives.exE he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxRenameTermTyping.source_term _ _ _ _ _ _ _ _ _ (.conjL (.conjR (.conjL hQ)))
  simpa only [Formula.raise, term_rename] using ho

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ ((term w a b n).iff (existsRenamed w r s a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxRenameTermExistence.for_term (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hm _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact term_of_exists _ _ _ _ _ _ _ _ (.hyp (Or.inl rfl))

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (maps w r s a b c d)) :
    Derives Γ ((term w a b n).iff (fiber w r s a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hm _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact term_of_fiber _ _ _ _ _ _ _ _ (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxRenameTerm
