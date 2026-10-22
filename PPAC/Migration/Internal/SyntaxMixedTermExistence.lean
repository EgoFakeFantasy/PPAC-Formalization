import PPAC.Migration.Internal.SyntaxMixedTermKnown

/-! 混合替换的全内部实际输出存在；由完整项像表取得输出，不作目标类别选择。 -/
namespace PPAC.Migration.Internal.SyntaxMixedTermExistence
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxRenameQuerySyntax SyntaxMixedTermSyntax
open SyntaxTermImageSyntax (maps maps_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_index {m} {Γ : Context m} (bound : Bool) (w r s a b c d n i : Fin m)
    (hm : Derives Γ (maps w r s a b c d)) (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound a b)))
    (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) : Derives Γ (existsOutput w r s a b c d n) := by
  let f := SyntaxIndexMapSyntax.selectMap bound r s
  let l := SyntaxTermSyntax.limit bound a b
  have hf := SyntaxTermImageSyntax.selected bound w r s a b c d hm
  have he := GraphProperties.output_exists f l i (SyntaxTermImageSyntax.image_function _ _ _ _ _ hf) hi
  let Q := edge f.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hm1 : Derives Δ (maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) :=
    of_eq (maps_rename w r s a b c d Fin.castSucc) (under hm Q)
  have hi1 : Derives Δ (.mem i.castSucc (SyntaxTermSyntax.limit bound a.castSucc b.castSucc)) :=
    of_eq (by simp only [Formula.raise, Formula.rename, SyntaxTermSyntax.limit_map]) (under hi Q)
  have hn1 : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc i.castSucc n.castSucc) :=
    of_eq (SyntaxVariableSyntax.code_rename bound w i n Fin.castSucc) (under hn Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hq1 : Derives Δ (edge (SyntaxIndexMapSyntax.selectMap bound r.castSucc s.castSucc) i.castSucc (Fin.last m)) :=
    of_eq (by simp only [Q, f, SyntaxIndexMapSyntax.selectMap_map]) hQ
  have hb := intro_branch bound w.castSucc (SyntaxIndexMapSyntax.selectMap bound r.castSucc s.castSucc)
    (SyntaxTermSyntax.limit bound a.castSucc b.castSucc) n.castSucc (Fin.last m) i.castSucc hi1 hn1 hq1
  have hs := intro_substituted bound w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hm1 hb
  have ho := intro_exists w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hs
  exact of_eq (existsOutput_rename w r s a b c d n Fin.castSucc).symm ho

theorem for_branch {m} {Γ : Context m} (bound : Bool) (w r s a b c d n : Fin m)
    (hm : Derives Γ (maps w r s a b c d))
    (hn : Derives Γ (SyntaxTermSyntax.branch bound w (SyntaxTermSyntax.limit bound a b) n)) : Derives Γ (existsOutput w r s a b c d n) := by
  let I := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a b) n
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch bound w (SyntaxTermSyntax.limit bound a b) n _ hn
  have hm1 : Derives Δ (maps w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) :=
    of_eq (maps_rename w r s a b c d Fin.castSucc) (under hm I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hi1 : Derives Δ (.mem (Fin.last m) (SyntaxTermSyntax.limit bound a.castSucc b.castSucc)) :=
    of_eq (by simp only [SyntaxTermSyntax.limit_map]) (.conjL hI)
  have ho := at_index bound w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hm1 hi1 (.conjR hI)
  exact of_eq (existsOutput_rename w r s a b c d n Fin.castSucc).symm ho

theorem exists_output {m} {Γ : Context m} (w r s a b c d n : Fin m)
    (hi : Derives Γ (input w r s a b c d n)) : Derives Γ (existsOutput w r s a b c d n) := by
  apply Derives.disjE (.conjR (.conjR hi))
  · exact for_branch true w r s a b c d n (add (.conjL hi) _) (.hyp (Or.inl rfl))
  · exact for_branch false w r s a b c d n (add (.conjL hi) _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedTermExistence
