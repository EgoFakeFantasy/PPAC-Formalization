import PPAC.Migration.SelectedPairSyntax

/-! 由实际行中的唯一选择点取得实际标签对的唯一纤维。 -/
namespace PPAC.Migration.SelectedPairFiber
open Source SourceAlgebra SourceLogic TaggedRowSyntax SelectedPairSyntax

theorem from_selected {m} {Γ : Context m} (s r x p : Fin m)
    (hr : Derives Γ (row r x)) (hp : Derives Γ (ChoiceSyntax.selected s r p)) :
    Derives Γ (selected s x p) := by
  have hm := Derives.conjL hp
  have he := Derives.impE (.conjL (row_at r x p hr)) (.conjR hm)
  apply Derives.conjI (.conjI (.conjL hm) he)
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hr' : Derives Δ (row r.castSucc x.castSucc) := by
    simpa only [Formula.raise, row_rename] using Derives.rename Fin.castSucc hr
  have hp' : Derives Δ (ChoiceSyntax.selected s.castSucc r.castSucc p.castSucc) := by
    simpa only [Formula.raise, ChoiceSyntax.selected_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  let M := chosen s.castSucc x.castSucc (Fin.last m)
  have hM : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  have hq := Derives.impE (.conjR (row_at r.castSucc x.castSucc (Fin.last m) (add hr' M))) (.conjR hM)
  have hu := Derives.allE (Fin.last m) (.conjR (add hp' M))
  have hu' : Derives (Context.add M Δ) ((ChoiceSyntax.chosen s.castSucc r.castSucc (Fin.last m)).imp
      (.equal (Fin.last m) p.castSucc)) := by
    simpa only [Formula.instantiate, Formula.rename, ChoiceSyntax.chosen_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hu
  exact .impE hu' (.conjI (.conjL hM) hq)

theorem for_row {m} {Γ : Context m} (s b r x : Fin m)
    (hr : Derives Γ (row r x)) (hb : Derives Γ (.mem r b))
    (hs : Derives Γ (ChoiceSyntax.selector s b)) : Derives Γ (fiber s x) := by
  have hp := Derives.impE (ChoiceSyntax.selector_at s b r hs) hb
  let P := ChoiceSyntax.selected s.castSucc r.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hrP : Derives Ξ (row r.castSucc x.castSucc) := by
    simpa only [Formula.raise, row_rename] using under hr P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hsel := from_selected s.castSucc r.castSucc x.castSucc (Fin.last m) hrP hP
  have hout : Derives Ξ (fiber s.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact hsel
  simpa only [Formula.raise, fiber_rename] using hout

theorem exists_fiber {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (s b a x : Fin m)
    (hf : Derives Γ (TaggedFamilySyntax.family b a)) (hs : Derives Γ (ChoiceSyntax.selector s b))
    (hx : Derives Γ (.mem x a)) : Derives Γ (fiber s x) := by
  have hr := TaggedRowExistence.exists_row x hA.pairing hA.extensionality hA.pairReplacement
  let R := row (Fin.last m) x.castSucc
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hr
  apply Derives.exE (p := R) hr
  have hfR : Derives Ξ (TaggedFamilySyntax.family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, TaggedFamilySyntax.family_rename] using under hf R
  have hsR : Derives Ξ (ChoiceSyntax.selector s.castSucc b.castSucc) := by
    simpa only [Formula.raise, ChoiceSyntax.selector_rename] using under hs R
  have hxR : Derives Ξ (.mem x.castSucc a.castSucc) := under hx R
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hi := TaggedFamilySyntax.intro_image a.castSucc (Fin.last m) x.castSucc hxR hR
  have hb := Derives.impE (.conjR (TaggedFamilySyntax.family_at b.castSucc a.castSucc (Fin.last m) hfR)) hi
  simpa only [Formula.raise, fiber_rename] using for_row s.castSucc b.castSucc (Fin.last m) x.castSucc hR hb hsR

theorem total {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (s b a : Fin m)
    (hf : Derives Γ (TaggedFamilySyntax.family b a)) (hs : Derives Γ (ChoiceSyntax.selector s b)) :
    Derives Γ (ReplacementPredicates.total matrix (fun _ => s) a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hf' : Derives Δ (TaggedFamilySyntax.family b.castSucc a.castSucc) := by
    simpa only [Formula.raise, TaggedFamilySyntax.family_rename] using Derives.rename Fin.castSucc hf
  have hs' : Derives Δ (ChoiceSyntax.selector s.castSucc b.castSucc) := by
    simpa only [Formula.raise, ChoiceSyntax.selector_rename] using Derives.rename Fin.castSucc hs
  apply Derives.impI
  simp only [matrix_fiber, ReplacementPredicates.paramsUp]
  exact exists_fiber (TaggedFamilyContext.add (TaggedFamilyContext.rename hA Fin.castSucc) _)
    s.castSucc b.castSucc a.castSucc (Fin.last m) (add hf' _) (add hs' _) (.hyp (Or.inl rfl))

theorem exists_graph {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (s b a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hf : Derives Γ (TaggedFamilySyntax.family b a)) (hs : Derives Γ (ChoiceSyntax.selector s b)) :
    Derives Γ (graphExists s a) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix (fun _ => s) a hr) (total hA s b a hf hs)
  simpa only [ReplacementPredicates.imageExists, matrix_graph, graphExists] using hi
end PPAC.Migration.SelectedPairFiber
