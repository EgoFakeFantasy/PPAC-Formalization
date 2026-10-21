import PPAC.Migration.SelectedGraphLogic

/-! 选择对精确像满足原完整choiceOn，定义域与所有输出均由对象量词处理。 -/
namespace PPAC.Migration.SelectedGraphChoice
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax TaggedRowSyntax SelectedPairSyntax

theorem value_and_choice {m} {Γ : Context m} (f x y : Fin m)
    (hv : Derives Γ (valueAt f x y)) (hy : Derives Γ (.mem y x)) :
    Derives Γ ((valueExists f x).conj (ChoiceSyntax.choiceValue f x)) := by
  apply Derives.conjI (GraphLogic.value_exists f x y hv)
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, edge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjL hv) hy

theorem from_selected {m} {Γ : Context m} (f s a p x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (graph f s a)) (hx : Derives Γ (.mem x a))
    (hp : Derives Γ (selected s x p)) :
    Derives Γ ((valueExists f x).conj (ChoiceSyntax.choiceValue f x)) := by
  have hy : Derives Γ (entry x p) := .conjR (.conjL hp)
  let Y := (Formula.mem (Fin.last m) x.castSucc).conj (ordered p.castSucc x.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have heY : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Y
  have hgY : Derives Ξ (graph f.castSucc s.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using under hg Y
  have hxY : Derives Ξ (.mem x.castSucc a.castSucc) := under hx Y
  have hpY : Derives Ξ (selected s.castSucc x.castSucc p.castSucc) := by
    simpa only [Formula.raise, selected_rename] using under hp Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hv := SelectedGraphLogic.value_for_selected f.castSucc s.castSucc a.castSucc p.castSucc x.castSucc (Fin.last m)
    heY hgY hxY hpY (.conjR hY)
  simpa only [Formula.raise, Formula.rename, valueExists_rename, ChoiceSyntax.choiceValue_rename] using
    value_and_choice f.castSucc x.castSucc (Fin.last m) hv (.conjL hY)

theorem for_input {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (f s b a x : Fin m)
    (hg : Derives Γ (graph f s a)) (hf : Derives Γ (TaggedFamilySyntax.family b a))
    (hs : Derives Γ (ChoiceSyntax.selector s b)) (hx : Derives Γ (.mem x a)) :
    Derives Γ ((valueExists f x).conj (ChoiceSyntax.choiceValue f x)) := by
  have hp := SelectedPairFiber.exists_fiber hA s b a x hf hs hx
  let P := selected s.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hAP := TaggedFamilyContext.under hA P
  have hgP : Derives Ξ (graph f.castSucc s.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using under hg P
  have hxP : Derives Ξ (.mem x.castSucc a.castSucc) := under hx P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  simpa only [Formula.raise, Formula.rename, valueExists_rename, ChoiceSyntax.choiceValue_rename] using
    from_selected f.castSucc s.castSucc a.castSucc (Fin.last m) x.castSucc hAP.extensionality hgP hxP hP

theorem choice_on {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (f s b a : Fin m)
    (hg : Derives Γ (graph f s a)) (hf : Derives Γ (TaggedFamilySyntax.family b a))
    (hs : Derives Γ (ChoiceSyntax.selector s b)) : Derives Γ (ChoiceSyntax.choiceOn f a) := by
  have hentries := SelectedGraphLogic.entries f s a hg
  have htotal : Derives Γ (.all ((Formula.mem (Fin.last m) a.castSucc).imp
      ((valueExists f.castSucc (Fin.last m)).conj (ChoiceSyntax.choiceValue f.castSucc (Fin.last m))))) := by
    apply Derives.allI
    let Δ := Context.image Formula.raise Γ
    have hA' := TaggedFamilyContext.rename hA Fin.castSucc
    have hg' : Derives Δ (graph f.castSucc s.castSucc a.castSucc) := by
      simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc hg
    have hf' : Derives Δ (TaggedFamilySyntax.family b.castSucc a.castSucc) := by
      simpa only [Formula.raise, TaggedFamilySyntax.family_rename] using Derives.rename Fin.castSucc hf
    have hs' : Derives Δ (ChoiceSyntax.selector s.castSucc b.castSucc) := by
      simpa only [Formula.raise, ChoiceSyntax.selector_rename] using Derives.rename Fin.castSucc hs
    apply Derives.impI
    exact for_input (TaggedFamilyContext.add hA' _) f.castSucc s.castSucc b.castSucc a.castSucc (Fin.last m)
      (add hg' _) (add hf' _) (add hs' _) (.hyp (Or.inl rfl))
  have hv : Derives Γ (totalOn f a) := by
    apply Derives.allI
    have ht := Derives.allE (Fin.last m) (Derives.rename Fin.castSucc htotal)
    have ht' : Derives (Context.image Formula.raise Γ) ((Formula.mem (Fin.last m) a.castSucc).imp
        ((valueExists f.castSucc (Fin.last m)).conj (ChoiceSyntax.choiceValue f.castSucc (Fin.last m)))) := by
      simpa only [Formula.raise, Formula.instantiate, Formula.rename, valueExists_rename,
        ChoiceSyntax.choiceValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
    apply Derives.impI
    exact .conjL (.impE (add ht' _) (.hyp (Or.inl rfl)))
  apply Derives.conjI (.conjI hentries hv)
  apply Derives.allI
  have ht := Derives.allE (Fin.last m) (Derives.rename Fin.castSucc htotal)
  have ht' : Derives (Context.image Formula.raise Γ) ((Formula.mem (Fin.last m) a.castSucc).imp
      ((valueExists f.castSucc (Fin.last m)).conj (ChoiceSyntax.choiceValue f.castSucc (Fin.last m)))) := by
    simpa only [Formula.raise, Formula.instantiate, Formula.rename, valueExists_rename,
      ChoiceSyntax.choiceValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ht
  apply Derives.impI
  exact .conjR (.impE (add ht' _) (.hyp (Or.inl rfl)))

theorem from_selector {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (s b a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hf : Derives Γ (TaggedFamilySyntax.family b a)) (hs : Derives Γ (ChoiceSyntax.selector s b)) :
    Derives Γ (ChoiceSyntax.graphExists a) := by
  have hg := SelectedPairFiber.exists_graph hA s b a hr hf hs
  let F := graph (Fin.last m) s.castSucc a.castSucc
  let Ξ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hg
  apply Derives.exE (p := F) hg
  have hAF := TaggedFamilyContext.under hA F
  have hfF : Derives Ξ (TaggedFamilySyntax.family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, TaggedFamilySyntax.family_rename] using under hf F
  have hsF : Derives Ξ (ChoiceSyntax.selector s.castSucc b.castSucc) := by
    simpa only [Formula.raise, ChoiceSyntax.selector_rename] using under hs F
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  have hc := choice_on hAF (Fin.last m) s.castSucc b.castSucc a.castSucc hF hfF hsF
  have hout : Derives Ξ (ChoiceSyntax.graphExists a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, ChoiceSyntax.choiceOn_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact hc
  simpa only [Formula.raise, ChoiceSyntax.graphExists_rename] using hout
end PPAC.Migration.SelectedGraphChoice
