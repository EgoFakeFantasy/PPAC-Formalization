import PPAC.Migration.Internal.StructuralListTraceProperties

/-! 相邻Cons步在旧边包含下真实迁移；末索引的新步单独构造并加入。 -/
namespace PPAC.Migration.Internal.StructuralListTraceRows
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListTraceSyntax GraphPointwiseSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem old_included {m} {Γ : Context m} (g f d y : Fin m) (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f d y)) : Derives Γ (edgeIncluded f g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hl2 : Derives Δ (GraphInsertSyntax.edgeLaw g.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, GraphInsertSyntax.edgeLaw_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hl)
  apply Derives.impI
  exact .impE (.conjR (SequenceSyntax.law_at _ _ _ _ _ _ (add hl2 _))) (.disjL (.hyp (Or.inl rfl)))

theorem new_edge {m} {Γ : Context m} (g f d y : Fin m) (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f d y)) : Derives Γ (edge g d y) :=
  .impE (.conjR (SequenceSyntax.law_at g f d y d y hl)) (.disjR (.conjI (.eqRefl d) (.eqRefl y)))

theorem row_map {m} {Γ : Context m} (w f g i : Fin m) (hi : Derives Γ (edgeIncluded f g))
    (hr : Derives Γ (row w f i)) : Derives Γ (row w g i) := by
  let R := rowWitness w f i
  let Δ := Context.add R (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_row w f i _ hr
  have hi3 : Derives Δ (edgeIncluded f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, edgeIncluded_rename] using GraphInsertElimination.under_three hi R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have ha := Derives.impE (edgeIncluded_at _ _ _ _ hi3) (.conjL (.conjR hR))
  have hb := Derives.impE (edgeIncluded_at _ _ _ _ hi3) (.conjL (.conjR (.conjR hR)))
  have hout := intro_row _ _ _ _ _ _ (.conjL hR) ha hb (.conjR (.conjR (.conjR hR)))
  simpa only [Formula.raise, row_rename] using hout

theorem links_map {m} {Γ : Context m} (w l f g : Fin m) (hl : Derives Γ (links w l f)) (hi : Derives Γ (edgeIncluded f g)) : Derives Γ (links w l g) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) l.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hl1 : Derives Δ (links w.castSucc l.castSucc f.castSucc) := by simpa only [Formula.raise, links_rename] using under hl M
  have hi1 : Derives Δ (edgeIncluded f.castSucc g.castSucc) := by simpa only [Formula.raise, edgeIncluded_rename] using under hi M
  exact row_map _ _ _ _ hi1 (StructuralListTraceSyntax.links_at _ _ _ _ hl1 (.hyp (Or.inl rfl)))

theorem row_index_subst {m} {Γ : Context m} (w f i j : Fin m) (he : Derives Γ (.equal i j)) (hr : Derives Γ (row w f i)) : Derives Γ (row w f j) := by
  have hi : Derives Γ ((row w.castSucc f.castSucc (Fin.last m)).instantiate i) := by
    simpa only [Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst (row w.castSucc f.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem append_links {m} {Γ : Context m} (w l d f g : Fin m) (hd : Derives Γ (successor d l))
    (hl : Derives Γ (links w l f)) (hi : Derives Γ (edgeIncluded f g)) (hnew : Derives Γ (row w g l)) : Derives Γ (links w d g) := by
  have hmap := links_map w l f g hl hi
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hd1 : Derives Δ (successor d.castSucc l.castSucc) := by simpa only [Formula.raise, successor_rename] using under hd M
  have hm1 : Derives Δ (links w.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, links_rename] using under hmap M
  have hn1 : Derives Δ (row w.castSucc g.castSucc l.castSucc) := by simpa only [Formula.raise, row_rename] using under hnew M
  apply Derives.disjE (InsertLogic.member_cases _ _ _ _ hd1 (.hyp (Or.inl rfl)))
  · exact StructuralListTraceSyntax.links_at _ _ _ _ (add hm1 _) (.hyp (Or.inl rfl))
  · exact row_index_subst _ _ _ _ (eq_symm (.hyp (Or.inl rfl))) (add hn1 _)
end PPAC.Migration.Internal.StructuralListTraceRows
