import PPAC.Migration.SelectedPairFiber

/-! 精确选择对像是完整函数图：实际有序对、正确定义域与唯一输出。 -/
namespace PPAC.Migration.SelectedGraphLogic
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax TaggedRowSyntax SelectedPairSyntax

theorem entry_decode {m} {Γ : Context m} (u p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hu : Derives Γ (entry u p)) (ho : Derives Γ (ordered p x y)) :
    Derives Γ ((Formula.equal u x).conj (.mem y x)) := by
  let W := (Formula.mem (Fin.last m) u.castSucc).conj (ordered p.castSucc u.castSucc (Fin.last m))
  let Ξ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at hu
  apply Derives.exE (p := W) hu
  have heW : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he W
  have hoW : Derives Ξ (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under ho W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hi := OrderedPairLogic.injective p.castSucc p.castSucc u.castSucc (Fin.last m) x.castSucc y.castSucc
    heW (.conjR hW) hoW (.eqRefl _)
  have hm := UnorderedPairLogic.mem_container_subst u.castSucc x.castSucc (Fin.last m) (.conjL hi) (.conjL hW)
  exact .conjI (.conjL hi) (mem_subst (.conjR hi) hm)

theorem decode {m} {Γ : Context m} (f s a p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (graph f s a)) (hp : Derives Γ (.mem p f)) (ho : Derives Γ (ordered p x y)) :
    Derives Γ ((chosen s x p).conj (.mem y x)) := by
  have hi := Derives.impE (.conjL (graph_at f s a p hg)) hp
  let U := (Formula.mem (Fin.last m) a.castSucc).conj (chosen s.castSucc (Fin.last m) p.castSucc)
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hi
  apply Derives.exE (p := U) hi
  have heU : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he U
  have hoU : Derives Ξ (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under ho U
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hd := entry_decode (Fin.last m) p.castSucc x.castSucc y.castSucc heU (.conjR (.conjR hU)) hoU
  have hc : Derives Ξ (chosen s.castSucc x.castSucc p.castSucc) :=
    Derives.conjI (.conjL (.conjR hU)) (intro_entry x.castSucc p.castSucc y.castSucc (.conjR hd) hoU)
  simpa only [Formula.raise, Formula.rename, chosen_rename] using Derives.conjI hc (.conjR hd)

theorem entry_on {m} {Γ : Context m} (f s a p : Fin m)
    (hg : Derives Γ (graph f s a)) (hp : Derives Γ (.mem p f)) : Derives Γ (entryOn a p) := by
  have hi := Derives.impE (.conjL (graph_at f s a p hg)) hp
  let U := (Formula.mem (Fin.last m) a.castSucc).conj (chosen s.castSucc (Fin.last m) p.castSucc)
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hi
  apply Derives.exE (p := U) hi
  have hU : Derives Γu U := .hyp (Or.inl rfl)
  have hy : Derives Γu (entry (Fin.last m) p.castSucc) := .conjR (.conjR hU)
  let Y := (Formula.mem (Fin.last (m+1)) (Fin.last m).castSucc).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Γu)
  change Derives Γu (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have huY : Derives Ξ (.mem (Fin.last m).castSucc a.castSucc.castSucc) := under (.conjL hU) Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hout := GraphLogic.entry_intro a.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) huY (.conjR hY)
  simpa only [Formula.raise, entryOn_rename] using hout

theorem entries {m} {Γ : Context m} (f s a : Fin m) (hg : Derives Γ (graph f s a)) :
    Derives Γ (entriesOn f a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hg' : Derives Δ (graph f.castSucc s.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc hg
  apply Derives.impI
  exact entry_on f.castSucc s.castSucc a.castSucc (Fin.last m) (add hg' _) (.hyp (Or.inl rfl))

theorem unique_output {m} {Γ : Context m} (f s a p x y z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (graph f s a)) (hp : Derives Γ (selected s x p))
    (ho : Derives Γ (ordered p x y)) (hz : Derives Γ (edge f x z)) : Derives Γ (.equal z y) := by
  let Q := (Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) x.castSucc z.castSucc)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  apply GraphLogic.edge_elim f x z _ hz
  have heQ : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Q
  have hgQ : Derives Ξ (graph f.castSucc s.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using under hg Q
  have hpQ : Derives Ξ (selected s.castSucc x.castSucc p.castSucc) := by
    simpa only [Formula.raise, selected_rename] using under hp Q
  have hoQ : Derives Ξ (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under ho Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hc := Derives.conjL (decode f.castSucc s.castSucc a.castSucc (Fin.last m) x.castSucc z.castSucc heQ hgQ (.conjL hQ) (.conjR hQ))
  have hqp := Derives.impE (unique_at s.castSucc x.castSucc p.castSucc (Fin.last m) hpQ) hc
  exact .conjR (OrderedPairLogic.injective (Fin.last m) p.castSucc x.castSucc z.castSucc x.castSucc y.castSucc heQ (.conjR hQ) hoQ hqp)

theorem value_for_selected {m} {Γ : Context m} (f s a p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (graph f s a)) (hx : Derives Γ (.mem x a))
    (hp : Derives Γ (selected s x p)) (ho : Derives Γ (ordered p x y)) : Derives Γ (valueAt f x y) := by
  have hpf := Derives.impE (.conjR (graph_at f s a p hg)) (intro_image s a x p hx (.conjL hp))
  apply Derives.conjI (GraphLogic.edge_intro f x y p hpf ho)
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hg' : Derives Δ (graph f.castSucc s.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc hg
  have hp' : Derives Δ (selected s.castSucc x.castSucc p.castSucc) := by
    simpa only [Formula.raise, selected_rename] using Derives.rename Fin.castSucc hp
  have ho' : Derives Δ (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc ho
  apply Derives.impI
  exact unique_output f.castSucc s.castSucc a.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)
    (add he' _) (add hg' _) (add hp' _) (add ho' _) (.hyp (Or.inl rfl))
end PPAC.Migration.SelectedGraphLogic
