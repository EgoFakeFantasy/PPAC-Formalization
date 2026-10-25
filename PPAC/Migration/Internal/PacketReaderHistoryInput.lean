import PPAC.Migration.Internal.PacketReaderHistoryStates

/-! Actual history-input fields exist uniquely at every internal domain index; no host field extraction is used. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryInput
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d i n l : Fin m)
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (he : Derives Γ (edge f i n)) :
    Derives Γ ((inputAt w f i l).iff (input w n l)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := inputAt w f i l
    let R := (edge f.castSucc i.castSucc (Fin.last m)).conj (input w.castSucc (Fin.last m) l.castSucc)
    let Δ := Context.add R (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) R
    have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under (add hf H) R)
    have he1 := of_eq (edge_rename f i n Fin.castSucc) (under (add he H) R)
    have hn := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality (.conjL hf1) (.conjL hR) he1
    simpa only [Formula.raise,input_rename] using PacketReaderConsumptionTransport.input_source _ _ _ _ hn (.conjR hR)
  · apply Derives.impI
    exact intro_at w f i l n (add he _) (.hyp (Or.inl rfl))

theorem valid_at {m} {Γ : Context m} (w f i l : Fin m) (hi : Derives Γ (inputAt w f i l)) : Derives Γ (StructuralListTraceSyntax.valid w l) := by
  let R := (edge f.castSucc i.castSucc (Fin.last m)).conj (input w.castSucc (Fin.last m) l.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using PacketReaderInputProjection.valid_input _ _ _ (.conjR hR)

theorem unique_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d i l L : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (SequenceSyntax.sequence f d w))
    (hl : Derives Γ (inputAt w f i l)) (hL : Derives Γ (inputAt w f i L)) : Derives Γ (.equal l L) := by
  let R := (edge f.castSucc i.castSucc (Fin.last m)).conj (input w.castSucc (Fin.last m) l.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hl
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under hf R)
  have hL1 := of_eq (inputAt_rename w f i L Fin.castSucc) (under hL R)
  have hiL := Derives.impE (.conjL (at_edge hZ1 _ _ _ _ _ _ hf1 (.conjL hR))) hL1
  exact PacketReaderInputProjection.unique hZ1 _ _ _ _ hw1 (.conjR hR) hiL

theorem exists_on_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f))
    (he : Derives Γ (edge f i N)) : Derives Γ (existsAt w f i) := by
  have hc := PacketReaderHistoryStates.at_edge hZ w B z o n r l d f i N hw hh he
  have hex := PacketReaderInputProjection.exists_of_carrier w N hc
  let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (input w.castSucc N.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he1 := of_eq (edge_rename f i N Fin.castSucc) (under he R)
  have hi := intro_at _ _ _ _ _ he1 (.conjR hR)
  have hout : Derives Δ (existsAt w.castSucc f.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListTraceSyntax.valid_rename,inputAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hR) hi)
  simpa only [Formula.raise,existsAt_rename] using hout

theorem exists_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f))
    (hi : Derives Γ (.mem i d)) : Derives Γ (existsAt w f i) := by
  have hex := SequenceLogic.value_at f d w i (PacketReaderHistoryLaws.sequence_at _ _ _ _ _ _ _ _ _ hh) hi
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (valueAt f.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (PacketReaderHistorySyntax.history_rename w B z o n r l d f Fin.castSucc) (under hh R)
  simpa only [Formula.raise,existsAt_rename] using exists_on_edge hZ1 _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 (.conjL (.conjR hR))

def uniqueAt {m} (w f i l : Fin m) : Formula m := .all
  ((inputAt w.castSucc f.castSucc i.castSucc (Fin.last m)).imp (.equal (Fin.last m) l.castSucc))
def fiberAt {m} (w f i : Fin m) : Formula m := .ex
  (((StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m))).conj
    (uniqueAt w.castSucc f.castSucc i.castSucc (Fin.last m)))
theorem uniqueAt_rename {m k} (w f i l : Fin m) (ρ : Fin m → Fin k) :
    (uniqueAt w f i l).rename ρ = uniqueAt (ρ w) (ρ f) (ρ i) (ρ l) := by
  simp only [uniqueAt,Formula.rename,inputAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]
theorem fiberAt_rename {m k} (w f i : Fin m) (ρ : Fin m → Fin k) :
    (fiberAt w f i).rename ρ = fiberAt (ρ w) (ρ f) (ρ i) := by
  simp only [fiberAt,Formula.rename,StructuralListTraceSyntax.valid_rename,inputAt_rename,uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem exists_unique_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f))
    (hi : Derives Γ (.mem i d)) : Derives Γ (fiberAt w f i) := by
  let R := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (inputAt w.castSucc f.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (exists_at hZ w B z o n r l d f i hw hh hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hseq := PacketReaderHistoryLaws.sequence_at _ _ _ _ _ _ _ _ _ hh
  have hf1 := of_eq (SequenceSyntax.sequence_rename f d w Fin.castSucc) (under hseq R)
  have hu : Derives Δ (uniqueAt w.castSucc f.castSucc i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let H := inputAt w.castSucc.castSucc f.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    have hZ2 := ZFContext.under hZ1 H
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 H)
    have hf2 := of_eq (SequenceSyntax.sequence_rename f.castSucc d.castSucc w.castSucc Fin.castSucc) (under hf1 H)
    have hold := of_eq (inputAt_rename w.castSucc f.castSucc i.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hR) H)
    exact unique_at hZ2 _ _ _ _ _ _ hw2 hf2 (.hyp (Or.inl rfl)) hold
  have hout : Derives Δ (fiberAt w.castSucc f.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,StructuralListTraceSyntax.valid_rename,inputAt_rename,uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hu)
  simpa only [Formula.raise,fiberAt_rename] using hout

end PPAC.Migration.Internal.PacketReaderHistoryInput
