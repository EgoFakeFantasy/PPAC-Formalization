import PPAC.Migration.Internal.PacketReaderHistoryRowMap

/-! Original sequence append constructs the actual longer history with exact restriction to the old graph. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryAppend
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax GraphPointwiseSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

def extension {m} (w B z o n s d e f : Fin m) : Formula m := .ex
  ((SequenceSyntax.append (Fin.last m) e.castSucc f.castSucc d.castSucc s.castSucc w.castSucc).conj
    (history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc s.castSucc d.castSucc e.castSucc (Fin.last m)))
theorem extension_rename {m k} (w B z o n s d e f : Fin m) (ρ : Fin m → Fin k) :
    (extension w B z o n s d e f).rename ρ = extension (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ s) (ρ d) (ρ e) (ρ f) := by
  simp only [extension,Formula.rename,SequenceSyntax.append_rename,history_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem from_append {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r s l d e f g : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o r s)) (he : Derives Γ (successor e d))
    (hg : Derives Γ (SequenceSyntax.append g e f d s w)) : Derives Γ (history w B z o n s d e g) := by
  have hinc := StructuralListTraceRows.old_included g f d s (.conjL (.conjR hg))
  have hseed := Derives.impE (edgeIncluded_at f g z n hinc) (seed_at _ _ _ _ _ _ _ _ _ hh)
  have hlast := Derives.impE (edgeIncluded_at f g l r hinc) (last_at _ _ _ _ _ _ _ _ _ hh)
  have hnew := StructuralListTraceRows.new_edge g f d s (.conjL (.conjR hg))
  have hrow := intro_row w B z o g l d r s (successor_at _ _ _ _ _ _ _ _ _ hh) hlast hnew ht
  have hl := PacketReaderHistoryRowMap.append_links w B z o l d f g (successor_at _ _ _ _ _ _ _ _ _ hh) (links_at_history _ _ _ _ _ _ _ _ _ hh) hinc hrow
  have hd := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw
    (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  exact .conjI (source_at _ _ _ _ _ _ _ _ _ hh) (.conjI (zero_at _ _ _ _ _ _ _ _ _ hh)
    (.conjI hd (.conjI he (.conjI (.conjL hg) (.conjI hseed (.conjI hnew hl))))))

theorem exists_extension {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r s l d e f : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o r s)) (he : Derives Γ (successor e d)) :
    Derives Γ (extension w B z o n s d e f) := by
  have hs := Derives.conjR (PacketReaderCodedNormalize.domain hZ w B z o r s hw ht)
  have hex := SequenceAppend.exists_append (ZFContext.arithmetic hZ).base e f d s w (sequence_at _ _ _ _ _ _ _ _ _ hh) hs he
  let R := SequenceSyntax.append (Fin.last m) e.castSucc f.castSucc d.castSucc s.castSucc w.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under hh R)
  have ht1 := of_eq (PacketReaderCodedSyntax.step_rename w B z o r s Fin.castSucc) (under ht R)
  have he1 := of_eq (successor_rename e d Fin.castSucc) (under he R)
  have hnew := from_append hZ1 _ _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 ht1 he1 hR
  have hout : Derives Δ (extension w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc s.castSucc d.castSucc e.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,SequenceSyntax.append_rename,history_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hnew)
  simpa only [Formula.raise,extension_rename] using hout

end PPAC.Migration.Internal.PacketReaderHistoryAppend
