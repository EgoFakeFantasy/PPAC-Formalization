import PPAC.Migration.TransitiveCoverExistence
import PPAC.Migration.ZFReplay

/-! 无额外背景假设的原ZF对象传递覆盖，以及实际精确末值集合的原核证书。 -/
namespace PPAC.Migration.ObjectTransitiveCover
open Source SourceAlgebra SourceLogic OmegaSyntax IterationValueSyntax IterationRangeSyntax TransitiveCoverSyntax

def rangeSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((empty 1).imp
  (.ex (IterationValueSyntax.range (Fin.last 3) (0 : Fin 3).castSucc (1 : Fin 3).castSucc (2 : Fin 3).castSucc)))).close

def propertiesSentence : Source.Sentence := ((omega (1 : Fin 4)).imp ((empty 2).imp
  ((IterationValueSyntax.range 0 1 2 3).imp ((Formula.mem 3 0).conj (closedUnion 0))))).close

def coverSentence : Source.Sentence := (coverExists (0 : Fin 1)).close

theorem closed_at {T : Theory} {p : Source.Sentence} (h : Derives (T.at 0) p) (m) :
    Derives (T.at m) (p.rename Fin.elim0) := by
  refine Derives.weaken ?_ (Derives.rename (Fin.elim0 : Fin 0 → Fin m) h)
  rintro q ⟨r, ⟨s, hs, rfl⟩, rfl⟩
  exact ⟨s, hs, (closed_rename s (Fin.elim0 : Fin 0 → Fin m)).symm⟩

theorem empty_exists_at {m} {Γ : Context m} (h : Derives Γ (Source.SetLanguage.emptySet.rename Fin.elim0)) :
    Derives Γ (.ex (empty (Fin.last m))) := by
  have h0 : Formula.liftRen (Fin.elim0 : Fin 0 → Fin m) (0 : Fin 1) = Fin.last m := by
    change Fin.lastCases (Fin.last m) (fun i : Fin 0 => (Fin.elim0 i : Fin m).castSucc) (Fin.last 0) = Fin.last m
    exact Fin.lastCases_last
  simpa only [Source.SetLanguage.emptySet, empty_original, Formula.rename, empty_rename, h0] using h

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have hr : Derives (Source.SetLanguage.ZF.at 3) ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩
  exact IterationValueCollection.exists_range (IterationContext.add (IterationContext.add (IterationContext.source_ZF 3) _) _)
    1 2 0 (add (add hr _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_properties : Derives (Source.SetLanguage.ZF.at 0) propertiesSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (IterationValueSyntax.range (0 : Fin 4) 1 2 3)
    (Context.add (empty 2) (Context.add (omega 1) (Source.SetLanguage.ZF.at 4)))
  have hA : IterationContext.Evidence Δ :=
    IterationContext.add (IterationContext.add (IterationContext.add (IterationContext.source_ZF 4) _) _) _
  have hw : Derives Δ (omega 1) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have hz : Derives Δ (empty 2) := .hyp (Or.inr (Or.inl rfl))
  have hc : Derives Δ (IterationValueSyntax.range 0 1 2 3) := .hyp (Or.inl rfl)
  exact .conjI (IterationRangeSeed.seed_member hA 0 1 2 3 hw hz hc) (IterationRangeClosed.closed_range hA 0 1 2 3 hw hz hc)

theorem source_cover : Derives (Source.SetLanguage.ZF.at 0) coverSentence := by
  apply close_derives
  have hraw : Derives (Source.SetLanguage.ZF.at 1) (Source.SetLanguage.emptySet.rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.emptySet, rfl⟩
  have hz := empty_exists_at hraw
  have hw : Derives (Source.SetLanguage.ZF.at 1) (.ex (omega (Fin.last 1))) := by
    simpa only [omegaExists_at] using closed_at ObjectOmega.source_ZF_existence 1
  have hr : Derives (Source.SetLanguage.ZF.at 1) ((Source.SetLanguage.replacement matrix).rename Fin.elim0) :=
    .hyp ⟨_, Source.SetLanguage.IsZFAxiom.replacement matrix, rfl⟩
  let Z := empty (Fin.last 1)
  let Γz := Context.add Z (Context.image Formula.raise (Source.SetLanguage.ZF.at 1))
  apply Derives.exE (p := Z) hz
  have hAZ := IterationContext.under (IterationContext.source_ZF 1) Z
  have hwZ : Derives Γz (.ex (omega (Fin.last 2))) := by
    simpa only [Formula.raise, Formula.rename, omega_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc] using under hw Z
  let W := omega (Fin.last 2)
  let Γw := Context.add W (Context.image Formula.raise Γz)
  apply Derives.exE (p := W) hwZ
  have hAW := IterationContext.under hAZ W
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  have hzW : Derives Γw (empty (Fin.last 1).castSucc) := by
    simpa only [Formula.raise, Z, empty_rename] using under hZ W
  have hrZ : Derives Γz ((Source.SetLanguage.replacement matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hr Z
  have hrW : Derives Γw ((Source.SetLanguage.replacement matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hrZ W
  have hW : Derives Γw W := .hyp (Or.inl rfl)
  have hres := TransitiveCoverExistence.exists_cover hAW (Fin.last 1).castSucc (0 : Fin 1).castSucc.castSucc (Fin.last 2) hrW hW hzW
  simpa only [Formula.raise, coverExists_rename] using hres

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem properties_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence propertiesSentence) := TheoryTransport.sentence source_properties

theorem cover_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory Source.SetLanguage.ZF) []
    (Translation.sentence coverSentence) := TheoryTransport.sentence source_cover

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) :=
  ZFReplay.replay range_kernel_certificate

theorem native_properties : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence propertiesSentence) :=
  ZFReplay.replay properties_kernel_certificate

theorem native_cover : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence coverSentence) :=
  ZFReplay.replay cover_kernel_certificate
end PPAC.Migration.ObjectTransitiveCover
