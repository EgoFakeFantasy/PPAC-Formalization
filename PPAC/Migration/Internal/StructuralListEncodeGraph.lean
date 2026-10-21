import PPAC.Migration.Internal.StructuralListEncodeSyntax

/-! 从源完整函数图和全部域内字段双条件恢复原精确Kuratowski图像。 -/
namespace PPAC.Migration.Internal.StructuralListEncodeGraph
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax GraphSyntax SequenceSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax StructuralListSuffixSyntax StructuralListEncodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem pair_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f p i y : Fin m)
    (hy : Derives Γ (edge f i y)) (hp : Derives Γ (ordered p i y)) : Derives Γ (.mem p f) := by
  let Q := (Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) i.castSucc y.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply GraphLogic.edge_elim f i y _ hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Q
  have hp1 : Derives Δ (ordered p.castSucc i.castSucc y.castSucc) := by simpa only [Formula.raise, ordered_rename] using under hp Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have heq := OrderedPairLogic.unique _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality (.conjR hQ) hp1
  exact mem_subst heq (.conjL hQ)

theorem member_image {m} {Γ : Context m} (w f l n p : Fin m)
    (hf : Derives Γ (functionOn f l)) (hr : Derives Γ (reading w f l n)) (hp : Derives Γ (.mem p f)) : Derives Γ (image w n l p) := by
  have he := Derives.impE (entries_at f l p (.conjL hf)) hp
  let I := Formula.ex ((Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))
  let Ξ := Context.add I (Context.image Formula.raise Γ)
  change Derives Γ (.ex I) at he
  apply Derives.exE (p := I) he
  let Y := (Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy : Derives Ξ (.ex Y) := .hyp (Or.inl rfl)
  apply Derives.exE (p := Y) hy
  have hr2 : Derives Δ (reading w.castSucc.castSucc f.castSucc.castSucc l.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, reading_rename] using under (under hr I) Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have he2 := GraphLogic.edge_intro _ _ _ _ (under (under hp I) Y) (.conjR hY)
  have hread := reading_at _ _ _ _ _ (Fin.last (m+1)) hr2 (.conjL hY)
  have hfield := Derives.impE (.conjR hread) he2
  have hentry := StructuralListFieldPairSyntax.intro_entry _ _ _ _ _ hfield (.conjR hY)
  have hout := StructuralListFieldPairSyntax.intro_image _ _ _ _ _ (.conjL hY) hentry
  simpa only [Formula.raise, image_rename] using hout

theorem image_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l n p : Fin m)
    (hr : Derives Γ (reading w f l n)) (hp : Derives Γ (image w n l p)) : Derives Γ (.mem p f) := by
  let I := (Formula.mem (Fin.last m) l.castSucc).conj (entry w.castSucc n.castSucc (Fin.last m) p.castSucc)
  let Ξ := Context.add I (Context.image Formula.raise Γ)
  change Derives Γ (.ex I) at hp
  apply Derives.exE (p := I) hp
  have hI : Derives Ξ I := .hyp (Or.inl rfl)
  let Y := (field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy : Derives Ξ (.ex Y) := .conjR hI
  apply Derives.exE (p := Y) hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ I) Y
  have hr2 : Derives Δ (reading w.castSucc.castSucc f.castSucc.castSucc l.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, reading_rename] using under (under hr I) Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hread := reading_at _ _ _ _ _ (Fin.last (m+1)) hr2 (under (.conjL hI) Y)
  have he := Derives.impE (.conjL hread) (.conjL hY)
  exact pair_member hZ2 _ _ _ _ he (.conjR hY)

theorem graph_from_reading {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l n : Fin m)
    (hf : Derives Γ (functionOn f l)) (hr : Derives Γ (reading w f l n)) : Derives Γ (graph w n l f) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hZ1 : ZFContext.Evidence Δ := ZFContext.rename hZ Fin.castSucc
  have hf1 : Derives Δ (functionOn f.castSucc l.castSucc) := by simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  have hr1 : Derives Δ (reading w.castSucc f.castSucc l.castSucc n.castSucc) := by simpa only [Formula.raise, reading_rename] using Derives.rename Fin.castSucc hr
  apply Derives.conjI
  · apply Derives.impI
    exact member_image _ _ _ _ _ (add hf1 _) (add hr1 _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact image_member (ZFContext.add hZ1 _) _ _ _ _ _ (add hr1 _) (.hyp (Or.inl rfl))

theorem zero_reading {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l z n : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hz : Derives Γ (empty z))
    (ha : Derives Γ (aligned w f z l n)) : Derives Γ (reading w f l n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc l.castSucc.castSucc
  let Δ := Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ M
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise := OrderedPairElimination.under_two ha M
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  have ha2 : Derives Δ (aligned w.castSucc.castSucc f.castSucc.castSucc z.castSucc.castSucc l.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, aligned_rename] using lift ha
  have hi : Derives Δ M := .hyp (Or.inl rfl)
  have hiW := StructuralListTraceOrder.member_member hZ2 _ _ _ hw2 (lift hl) hi
  have hsum := NaturalArithmeticBounds.add_zero_left hZ2 _ _ _ hw2 hz2 hiW
  exact aligned_at _ _ _ _ _ _ _ (Fin.last (m+1)) ha2 hi hsum

theorem fields_from_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l z n : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hl : Derives Γ (.mem l w))
    (hz : Derives Γ (empty z)) (ha : Derives Γ (aligned w f z l n)) : Derives Γ (fields w n l f) := by
  have hr := zero_reading hZ w f l z n hw hl hz ha
  have hg := graph_from_reading hZ w f l n (.conjL hf) hr
  exact StructuralListFieldGraphFunction.complete hZ w n l f hw hl hg
end PPAC.Migration.Internal.StructuralListEncodeGraph
