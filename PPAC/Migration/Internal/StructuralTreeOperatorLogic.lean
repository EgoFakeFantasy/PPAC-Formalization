import PPAC.Migration.Internal.StructuralTreeOperatorSyntax

/-! 原完整字段图已推出全部子码界；树算子的严格历史查询不额外排除原合法字段。 -/
namespace PPAC.Migration.Internal.StructuralTreeOperatorLogic
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralTreeOperatorSyntax
open StructuralListLengthSyntax (hasLength under_four)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem shape_edge_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f i y : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) (he : Derives Γ (edge f i y)) : Derives Γ (.mem y n) :=
  StructuralListFieldBounds.raw_edge_member hZ w tag p n l f i y hw (.conjL (.conjL hs)) (.conjR (.conjL hs)) (.conjL (.conjR hs)) (.conjR (.conjR hs)) he

theorem children_of_marks {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f e h : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) (hm : Derives Γ (marks e f h)) : Derives Γ (children e n f h) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) E
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hq)) E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs2 : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc tag.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, shape_rename] using lift hs
  have hm2 : Derives Δ (marks e.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc) := by simpa only [Formula.raise, marks_rename] using lift hm
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact .conjI (shape_edge_bound hZ2 _ _ _ _ _ _ _ _ hw2 hs2 hE) (marks_at _ _ _ _ _ hm2 hE)

theorem marks_of_children {m} {Γ : Context m} (e n f h : Fin m) (hc : Derives Γ (children e n f h)) : Derives Γ (marks e f h) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hc2 : Derives Δ (children e.castSucc.castSucc n.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc) := by
    simpa only [Formula.raise, children_rename] using add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)) E
  exact .conjR (children_at _ _ _ _ _ _ hc2 (.hyp (Or.inl rfl)))

theorem children_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n tag p l f e h : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) : Derives Γ ((marks e f h).iff (children e n f h)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact children_of_marks (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hs _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact marks_of_children _ _ _ _ (.hyp (Or.inl rfl))

theorem marks_empty {m} {Γ : Context m} (w p l f e h : Fin m)
    (hf : Derives Γ (StructuralListFieldGraphSyntax.fields w p l f)) (hz : Derives Γ (empty l)) : Derives Γ (marks e f h) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hq)) E
  have hf2 : Derives Δ (StructuralListFieldGraphSyntax.fields w.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, StructuralListFieldGraphSyntax.fields_rename] using lift hf
  have hz2 : Derives Δ (empty l.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hlaw := StructuralListFieldGraphSyntax.law_at _ _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) (.conjR (.conjR hf2))
  have hi := Derives.conjL (.impE (.conjL hlaw) hE)
  exact .botE (.impE (empty_at _ _ hz2) hi)

theorem leaf_good {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e n h tag p l f : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n tag p l f)) (hz : Derives Γ (empty l)) : Derives Γ (good w e n h) :=
  intro_good w e n h tag p l f hs (children_of_marks hZ w n tag p l f e h hw hs (marks_empty w p l f e h (.conjR (.conjR hs)) hz))

theorem positive_good {m} {Γ : Context m} (w e n h : Fin m) (hg : Derives Γ (good w e n h)) : Derives Γ (empty n).neg := by
  let B := goodBody w e n h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_good w e n h _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := StructuralNodeProperties.positive _ _ _ _ (.conjR (.conjL (.conjL hB)))
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem empty_not_good {m} {Γ : Context m} (w e n h : Fin m) (hz : Derives Γ (empty n)) : Derives Γ (good w e n h).neg := by
  apply Derives.impI
  exact .impE (positive_good _ _ _ _ (.hyp (Or.inl rfl))) (add hz _)
end PPAC.Migration.Internal.StructuralTreeOperatorLogic
