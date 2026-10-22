import PPAC.Migration.Internal.SyntaxMixedTermSyntax

/-! 混合项替换恢复源类型、准确目标类型和自然码值域，不限制目标变量类别。 -/
namespace PPAC.Migration.Internal.SyntaxMixedTermTyping
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedTermSyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename maps maps_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem branch_source {m} {Γ : Context m} (bound : Bool) (w r s a b c d n q : Fin m)
    (hm : Derives Γ (maps w r s a b c d))
    (hb : Derives Γ (branch bound w (SyntaxIndexMapSyntax.selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q)) :
    Derives Γ (SyntaxTermSyntax.term w a b n) := by
  let B := branchBody bound w (SyntaxIndexMapSyntax.selectMap bound r s) (SyntaxTermSyntax.limit bound a b) n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hb
  have hm1 : Derives Δ (maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) :=
    of_eq (maps_rename w r s a b c d Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi : Derives Δ (.mem (Fin.last m) (SyntaxTermSyntax.limit bound a.castSucc b.castSucc)) :=
    of_eq (by simp only [SyntaxTermSyntax.limit_map]) (.conjL hB)
  have ho := SyntaxTermSyntax.intro_term bound w.castSucc a.castSucc b.castSucc n.castSucc (Fin.last m)
    (.conjI (SyntaxTermImageSyntax.source_contexts _ _ _ _ _ _ _ hm1) hi) (.conjL (.conjR hB))
  exact of_eq (SyntaxTermSyntax.term_rename w a b n Fin.castSucc).symm ho

theorem branch_target {m} {Γ : Context m} (bound : Bool) (w f a c d n q : Fin m)
    (hm : Derives Γ (imageMap w f a c d)) (hb : Derives Γ (branch bound w f a n q)) :
    Derives Γ (SyntaxTermSyntax.term w c d q) := by
  let B := branchBody bound w f a n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hb
  have hm1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) :=
    of_eq (imageMap_rename w f a c d Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxTermImageSyntax.image_type w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) q.castSucc hm1 (.conjR (.conjR hB))
  exact of_eq (SyntaxTermSyntax.term_rename w c d q Fin.castSucc).symm ho

theorem branch_natural {m} {Γ : Context m} (bound : Bool) (w f a c d n q : Fin m)
    (hm : Derives Γ (imageMap w f a c d)) (hb : Derives Γ (branch bound w f a n q)) : Derives Γ (.mem q w) := by
  let B := branchBody bound w f a n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hb
  have hm1 : Derives Δ (imageMap w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc) :=
    of_eq (imageMap_rename w f a c d Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxTermImageSyntax.image_natural w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) q.castSucc hm1 (.conjR (.conjR hB))

theorem source_type {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hq : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (SyntaxTermSyntax.term w a b n) := by
  apply Derives.disjE (.conjR hq)
  · exact branch_source true w r s a b c d n q (add (.conjL hq) _) (.hyp (Or.inl rfl))
  · exact branch_source false w r s a b c d n q (add (.conjL hq) _) (.hyp (Or.inl rfl))

theorem target_type {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hq : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (SyntaxTermSyntax.term w c d q) := by
  apply Derives.disjE (.conjR hq)
  · exact branch_target true w r a c d n q (add (.conjL (.conjL hq)) _) (.hyp (Or.inl rfl))
  · exact branch_target false w s b c d n q (add (.conjR (.conjL hq)) _) (.hyp (Or.inl rfl))

theorem output_natural {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hq : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (.mem q w) := by
  apply Derives.disjE (.conjR hq)
  · exact branch_natural true w r a c d n q (add (.conjL (.conjL hq)) _) (.hyp (Or.inl rfl))
  · exact branch_natural false w s b c d n q (add (.conjR (.conjL hq)) _) (.hyp (Or.inl rfl))

theorem input_of_substituted {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hq : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (input w r s a b c d n) :=
  .conjI (.conjL hq) (source_type w r s a b c d n q hq)

end PPAC.Migration.Internal.SyntaxMixedTermTyping
