import PPAC.Migration.IterationBase

/-! 在原Pairing和Extensionality中取得真实零长度轨迹，不抽取宿主见证。 -/
namespace PPAC.Migration.IterationBaseExistence
open Source SourceAlgebra SourceLogic OmegaSyntax FiniteIterationSyntax

abbrev singletonWitnesses {m} (z a : Fin m) : Formula (m+3) := SingletonMap.witness
  (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc

theorem singleton_elim {m} {Γ : Context m} (z a : Fin m) (q : Formula m)
    (h : Derives Γ (SingletonMap.existsMap z a))
    (hc : Derives (Context.add (singletonWitnesses z a)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))) q.raise.raise.raise) :
    Derives Γ q := by
  change Derives Γ (.ex (.ex (.ex (singletonWitnesses z a)))) at h
  apply Derives.exE h
  apply Derives.exE (Derives.hyp (Or.inl rfl))
  apply Derives.exE (p := singletonWitnesses z a) (Derives.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, ⟨t, ⟨u, hu, heu⟩, het⟩, hes⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, hu, heu⟩, het⟩, hes⟩

theorem under_three {m} {Γ : Context m} {q : Formula m} (h : Derives Γ q) (b : Formula (m+3)) :
    Derives (Context.add b (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
      q.raise.raise.raise :=
  .weaken (fun _ h => Or.inr h) (.rename Fin.castSucc (.rename Fin.castSucc (.rename Fin.castSucc h)))

theorem exists_base {m} {Γ : Context m} (z a : Fin m)
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hz : Derives Γ (empty z)) :
    Derives Γ (existsTrack z z a) := by
  have hm := SingletonMap.exists_map z a hp he
  let W := singletonWitnesses z a
  let Γw := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply singleton_elim z a _ hm
  have heW : Derives Γw (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under_three he W
  have hzW : Derives Γw (empty z.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under_three hz W
  have hW : Derives Γw W := .hyp (Or.inl rfl)
  have hw := IterationBase.from_singleton (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
    z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc heW hzW hW
  have hr := intro_track (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc
    z.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc hw
  simpa only [Formula.raise, existsTrack_rename] using hr
end PPAC.Migration.IterationBaseExistence
