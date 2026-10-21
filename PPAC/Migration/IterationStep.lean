import PPAC.Migration.IterationValues

/-! 传递域中，内部后继的共同位置具有共同前驱；用原exE保留前驱输出见证。 -/
namespace PPAC.Migration.IterationStep
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax IterationSyntax

theorem predecessor_member {m} {Γ : Context m} (d j k : Fin m)
    (ht : Derives Γ (transitive d)) (hs : Derives Γ (successor k j)) (hk : Derives Γ (.mem k d)) :
    Derives Γ (.mem j d) :=
  .impE (RestrictionSyntax.subset_at k d j (.impE (transitive_at d k ht) hk)) (InsertLogic.new_member k j j hs)

theorem successor_agrees {m} {Γ : Context m} (f g d e z a j k : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a))
    (hd : Derives Γ (transitive d)) (hc : Derives Γ (transitive e))
    (hj : Derives Γ (commonAt f g d e j)) (hs : Derives Γ (successor k j))
    (hkd : Derives Γ (.mem k d)) (hke : Derives Γ (.mem k e)) : Derives Γ (agreesAt f g k) := by
  have hjd := predecessor_member d j k hd hs hkd
  have hje := predecessor_member e j k hc hs hke
  have ha : Derives Γ (agreesAt f g j) := .impE (.impE hj hjd) hje
  have hu := GraphProperties.output_exists f d j (.conjL hf) hjd
  let U := edge f.castSucc j.castSucc (Fin.last m)
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have heU : Derives Γu (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he U
  have hfU : Derives Γu (next f.castSucc) := by
    simpa only [Formula.raise, next_rename] using under (.conjR (.conjR hf)) U
  have hgU : Derives Γu (track g.castSucc e.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, track_rename] using under hg U
  have haU : Derives Γu (agreesAt f.castSucc g.castSucc j.castSucc) := by
    simpa only [Formula.raise, agreesAt_rename] using under ha U
  have hsU : Derives Γu (successor k.castSucc j.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs U
  have hjeU : Derives Γu (.mem j.castSucc e.castSucc) := under hje U
  have hv := GraphProperties.output_exists g.castSucc e.castSucc j.castSucc (.conjL hgU) hjeU
  let V := edge g.castSucc.castSucc j.castSucc.castSucc (Fin.last (m+1))
  let Γv := Context.add V (Context.image Formula.raise Γu)
  change Derives Γu (.ex V) at hv
  apply Derives.exE (p := V) hv
  have heV : Derives Γv (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under heU V
  have hfV : Derives Γv (next f.castSucc.castSucc) := by
    simpa only [Formula.raise, next_rename] using under hfU V
  have hgV : Derives Γv (next g.castSucc.castSucc) := by
    simpa only [Formula.raise, next_rename] using under (.conjR (.conjR hgU)) V
  have haV : Derives Γv (agreesAt f.castSucc.castSucc g.castSucc.castSucc j.castSucc.castSucc) := by
    simpa only [Formula.raise, agreesAt_rename] using under haU V
  have hsV : Derives Γv (successor k.castSucc.castSucc j.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hsU V
  have hU : Derives Γu U := .hyp (Or.inl rfl)
  have hUV : Derives Γv (edge f.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, U, edge_rename] using under hU V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  have hr := IterationValues.step_agrees f.castSucc.castSucc g.castSucc.castSucc j.castSucc.castSucc k.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) heV hfV hgV hsV haV hUV hV
  simpa only [Formula.raise, agreesAt_rename] using hr

theorem successor_common {m} {Γ : Context m} (f g d e z a j k : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a))
    (hd : Derives Γ (transitive d)) (hc : Derives Γ (transitive e))
    (hj : Derives Γ (commonAt f g d e j)) (hs : Derives Γ (successor k j)) :
    Derives Γ (commonAt f g d e k) := by
  apply Derives.impI
  apply Derives.impI
  exact successor_agrees f g d e z a j k (add (add he _) _) (add (add hf _) _) (add (add hg _) _)
    (add (add hd _) _) (add (add hc _) _) (add (add hj _) _) (add (add hs _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.IterationStep
