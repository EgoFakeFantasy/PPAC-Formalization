import PPAC.Migration.Internal.IndexTermImageCodeSyntax

/-! 转换的完整合法域、目标项列表类型和指定原图下的实际对齐。 -/
namespace PPAC.Migration.Internal.IndexTermImageCodeTyping
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermImageCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_converted {m} {Γ : Context m} (isBound : Bool) (w I T a c d : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d)) : Derives Γ (input isBound w I a c d) := by
  let B := body isBound w I T a c d
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := Derives.conjL (Derives.conjR hB)
  have ho : Derives Δ (input isBound w.castSucc.castSucc I.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc) :=
    .conjI (.conjL (.conjL hm)) (SyntaxMapCodeSyntax.intro_code w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (SyntaxTermSyntax.limit isBound c.castSucc.castSucc d.castSucc.castSucc) I.castSucc.castSucc (.conjL hB))
  exact of_eq (by simp only [Formula.raise, input_rename]) ho

theorem term_list {m} {Γ : Context m} (isBound : Bool) (w I T a c d : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a c d T) := by
  let B := body isBound w I T a c d
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxMixedImageCodeFields.term_list w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc T.castSucc.castSucc (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) ho

theorem code_natural {m} {Γ : Context m} (isBound : Bool) (w I T a c d : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d)) : Derives Γ (.mem T w) :=
  .conjL (.conjL (.conjR (.conjR (term_list isBound w I T a c d hc))))

theorem at_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I T a c d r : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit isBound c d) I)) :
    Derives Γ (atGraph isBound w r T a c d) := by
  let B := body isBound w I T a c d
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hc
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hr2 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc (SyntaxTermSyntax.limit isBound c.castSucc.castSucc d.castSucc.castSucc) I.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename, SyntaxTermSyntax.limit_map]) (SyntaxRenameBinders.under_2 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := SyntaxMapCode.unique_graph hZ2 w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc a.castSucc.castSucc (SyntaxTermSyntax.limit isBound c.castSucc.castSucc d.castSucc.castSucc) I.castSucc.castSucc (.conjL hB) hr2
  have hm := SyntaxVariableImageFields.mapped_subst_index_graph isBound w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) r.castSucc.castSucc he (.conjL (.conjR hB))
  have ho := intro_atGraph isBound w.castSucc.castSucc r.castSucc.castSucc T.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) hm (.conjR (.conjR hB))
  exact of_eq (by simp only [Formula.raise, atGraph_rename]) ho

theorem from_graph {m} {Γ : Context m} (isBound : Bool) (w I T a c d r : Fin m)
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit isBound c d) I))
    (hf : Derives Γ (atGraph isBound w r T a c d)) : Derives Γ (converted isBound w I T a c d) := by
  let F := (SyntaxVariableImageSyntax.mapped isBound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc T.castSucc)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE hf
  have hr1 : Derives Δ (SyntaxMapCodeSyntax.encoded w.castSucc r.castSucc a.castSucc (SyntaxTermSyntax.limit isBound c.castSucc d.castSucc) I.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMapCodeSyntax.encoded_rename, SyntaxTermSyntax.limit_map]) (under hr F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have ho := intro_converted isBound w.castSucc I.castSucc T.castSucc a.castSucc c.castSucc d.castSucc r.castSucc (Fin.last m) (.conjI hr1 hF)
  exact of_eq (by simp only [Formula.raise, converted_rename]) ho

theorem graph_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I T a c d r : Fin m)
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit isBound c d) I)) :
    Derives Γ ((converted isBound w I T a c d).iff (atGraph isBound w r T a c d)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_graph (ZFContext.add hZ _) isBound w I T a c d r (.hyp (Or.inl rfl)) (add hr _)
  · apply Derives.impI
    exact from_graph isBound w I T a c d r (add hr _) (.hyp (Or.inl rfl))

theorem environment_lists {m} {Γ : Context m} (w I J R S a b c d : Fin m)
    (he : Derives Γ (environment w I J R S a b c d)) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) :=
  .conjI (term_list true w I R a c d (.conjL he)) (term_list false w J S b c d (.conjR he))

end PPAC.Migration.Internal.IndexTermImageCodeTyping
