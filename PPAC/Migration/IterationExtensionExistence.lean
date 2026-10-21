import PPAC.Migration.IterationExtension
import PPAC.Migration.IterationBaseExistence

/-! 原Pairing/Union/Extensionality构造真实后继轨迹，不把图存在作为字段。 -/
namespace PPAC.Migration.IterationExtensionExistence
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax InsertSyntax IterationSyntax FiniteIterationSyntax

theorem eliminate_three {m} {Γ : Context m} (p : Formula (m+3)) (q : Formula m)
    (h : Derives Γ (.ex (.ex (.ex p))))
    (hc : Derives (Context.add p (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
      q.raise.raise.raise) : Derives Γ q := by
  apply Derives.exE h
  apply Derives.exE (Derives.hyp (Or.inl rfl))
  apply Derives.exE (p := p) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, ⟨t, ⟨u, hu, heu⟩, het⟩, hes⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, hu, heu⟩, het⟩, hes⟩

theorem with_union {m} {Γ : Context m} (f n s r v z a : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f s z a)) (hn : Derives Γ (transitive n)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem n n).neg) (hsno : Derives Γ (Formula.mem s s).neg)
    (hsn : Derives Γ (successor s n)) (hr : Derives Γ (edge f n r)) (hv : Derives Γ (unionOf v r)) :
    Derives Γ (existsTrack s z a) := by
  have hext := GraphInsertExistence.exists_extension f s s v hp hu he (.conjL hf) hsno
  let W := GraphInsertSyntax.witness (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    f.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc
  let Γw := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  change Derives Γ (.ex (.ex (.ex W))) at hext
  apply eliminate_three W _ hext
  have heW : Derives Γw (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using IterationBaseExistence.under_three he W
  have hfW : Derives Γw (track f.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, track_rename] using IterationBaseExistence.under_three hf W
  have hnW : Derives Γw (transitive n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using IterationBaseExistence.under_three hn W
  have htW : Derives Γw (transitive s.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using IterationBaseExistence.under_three ht W
  have hnoW : Derives Γw ((Formula.mem n.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using IterationBaseExistence.under_three hno W
  have hsnoW : Derives Γw ((Formula.mem s.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using IterationBaseExistence.under_three hsno W
  have hsnW : Derives Γw (successor s.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using IterationBaseExistence.under_three hsn W
  have hrW : Derives Γw (edge f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using IterationBaseExistence.under_three hr W
  have hvW : Derives Γw (unionOf v.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using IterationBaseExistence.under_three hv W
  have hW : Derives Γw W := .hyp (Or.inl rfl)
  have hw := IterationExtension.witness_preserved (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc
    r.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc
    heW hfW hnW htW hnoW hsnoW hsnW hrW hvW hW
  have hrx := intro_track (Fin.last (m+2)) (Fin.last (m+1)).castSucc
    s.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc hw
  simpa only [Formula.raise, existsTrack_rename] using hrx

theorem with_value {m} {Γ : Context m} (f n s r z a : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f s z a)) (hn : Derives Γ (transitive n)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem n n).neg) (hsno : Derives Γ (Formula.mem s s).neg)
    (hsn : Derives Γ (successor s n)) (hr : Derives Γ (edge f n r)) : Derives Γ (existsTrack s z a) := by
  have hv := union_instance r hu
  let V := unionOf (Fin.last m) r.castSucc
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hpV : Derives Γv (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp V
  have huV : Derives Γv (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu V
  have heV : Derives Γv (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he V
  have hfV : Derives Γv (track f.castSucc s.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, track_rename] using under hf V
  have hnV : Derives Γv (transitive n.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using under hn V
  have htV : Derives Γv (transitive s.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using under ht V
  have hnoV : Derives Γv ((Formula.mem n.castSucc n.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using under hno V
  have hsnoV : Derives Γv ((Formula.mem s.castSucc s.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using under hsno V
  have hsnV : Derives Γv (successor s.castSucc n.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hsn V
  have hrV : Derives Γv (edge f.castSucc n.castSucc r.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hr V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  have hrx := with_union f.castSucc n.castSucc s.castSucc r.castSucc (Fin.last m) z.castSucc a.castSucc
    hpV huV heV hfV hnV htV hnoV hsnoV hsnV hrV hV
  simpa only [Formula.raise, existsTrack_rename] using hrx

theorem exists_successor {m} {Γ : Context m} (f n s z a : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (hu : Derives Γ (Source.SetLanguage.union.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f s z a)) (hn : Derives Γ (transitive n)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem n n).neg) (hsno : Derives Γ (Formula.mem s s).neg)
    (hsn : Derives Γ (successor s n)) : Derives Γ (existsTrack s z a) := by
  have hr := GraphProperties.output_exists f s n (.conjL hf) (InsertLogic.new_member s n n hsn)
  let R := edge f.castSucc n.castSucc (Fin.last m)
  let Γr := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hr
  apply Derives.exE (p := R) hr
  have hpR : Derives Γr (Source.SetLanguage.pairing.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp R
  have huR : Derives Γr (Source.SetLanguage.union.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hu R
  have heR : Derives Γr (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he R
  have hfR : Derives Γr (track f.castSucc s.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, track_rename] using under hf R
  have hnR : Derives Γr (transitive n.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using under hn R
  have htR : Derives Γr (transitive s.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using under ht R
  have hnoR : Derives Γr ((Formula.mem n.castSucc n.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using under hno R
  have hsnoR : Derives Γr ((Formula.mem s.castSucc s.castSucc).neg) := by
    simpa only [Formula.raise, Formula.neg, Formula.rename] using under hsno R
  have hsnR : Derives Γr (successor s.castSucc n.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hsn R
  have hR : Derives Γr R := .hyp (Or.inl rfl)
  have hrx := with_value f.castSucc n.castSucc s.castSucc (Fin.last m) z.castSucc a.castSucc
    hpR huR heR hfR hnR htR hnoR hsnoR hsnR hR
  simpa only [Formula.raise, existsTrack_rename] using hrx
end PPAC.Migration.IterationExtensionExistence
