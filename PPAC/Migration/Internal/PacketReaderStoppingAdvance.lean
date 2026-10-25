import PPAC.Migration.Internal.PacketReaderStoppingInitial

/-! A real prefix either halts at its actual endpoint or is extended by the original graph append. -/
namespace PPAC.Migration.Internal.PacketReaderStoppingAdvance
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderStoppingSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem from_extension {m} {Γ : Context m} (w B z o n s d e f : Fin m)
    (he : Derives Γ (PacketReaderHistoryAppend.extension w B z o n s d e f)) : Derives Γ (prefixAt w B z o n d) := by
  let R := (SequenceSyntax.append (Fin.last m) e.castSucc f.castSucc d.castSucc s.castSucc w.castSucc).conj
    (history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc s.castSucc d.castSucc e.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,prefixAt_rename] using intro_prefix _ _ _ _ _ _ _ _ _ (.conjR hR)

theorem from_coded_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r s i d f j : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r i d f))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o r s)) (hj : Derives Γ (successor j i)) :
    Derives Γ (prefixAt w B z o n j) := by
  have hd := OmegaStructureAlgebra.successor_member w d i (ZFContext.arithmetic hZ).base.extensionality hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hEq := OmegaUniversal.successor_unique d j i (ZFContext.arithmetic hZ).base.extensionality (successor_at _ _ _ _ _ _ _ _ _ hh) hj
  have hex := Derives.impE (OmegaSyntax.step_at w d (.conjL hw)) hd
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) d.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (history_rename w B z o n r i d f Fin.castSucc) (under hh R)
  have ht1 := of_eq (PacketReaderCodedSyntax.step_rename w B z o r s Fin.castSucc) (under ht R)
  have he1 : Derives Δ (.equal d.castSucc j.castSucc) := under hEq R
  have hext := PacketReaderHistoryAppend.exists_extension hZ1 _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 ht1 (.conjR hR)
  have hp := from_extension _ _ _ _ _ _ _ _ _ hext
  simpa only [Formula.raise,prefixAt_rename] using prefix_index _ _ _ _ _ _ _ he1 hp

theorem from_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r i d f j : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r i d f))
    (he : Derives Γ (PacketReaderCodedSyntax.existsNext w B z o r)) (hj : Derives Γ (successor j i)) :
    Derives Γ (prefixAt w B z o n j) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (PacketReaderCodedSyntax.step w.castSucc B.castSucc z.castSucc o.castSucc r.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (history_rename w B z o n r i d f Fin.castSucc) (under hh R)
  have hj1 := of_eq (successor_rename j i Fin.castSucc) (under hj R)
  simpa only [Formula.raise,prefixAt_rename] using from_coded_step hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc r.castSucc (Fin.last m) i.castSucc d.castSucc f.castSucc j.castSucc hw1 hh1 (.conjR hR) hj1

theorem from_history {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r i d f j : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r i d f))
    (hj : Derives Γ (successor j i)) : Derives Γ (progress w B z o n j) := by
  apply SourcePropositional.by_cases (PacketReaderCodedSyntax.existsNext w B z o r)
  · let H := PacketReaderCodedSyntax.existsNext w B z o r
    exact .disjR (from_next (ZFContext.add hZ H) _ _ _ _ _ _ _ _ _ _ (add hw H) (add hh H) (.hyp (Or.inl rfl)) (add hj H))
  · exact .disjL (intro_complete _ _ _ _ _ _ _ _ _ (.conjI (add hh _) (.hyp (Or.inl rfl))))

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n i j : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (progress w B z o n i))
    (hj : Derives Γ (successor j i)) : Derives Γ (progress w B z o n j) := by
  apply Derives.disjE hp
  · exact .disjL (.hyp (Or.inl rfl))
  · let P := prefixAt w B z o n i
    let R := prefixBody w B z o n i
    let Δ := Context.add R (raisedContext 3 (Context.add P Γ))
    apply HornBinderRules.eliminate_many 3 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ P) R
    have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 (add hw P) R)
    have hj3 := of_eq (successor_rename j i (old 3)) (HornBinderRules.under_body 3 (add hj P) R)
    exact of_eq (progress_rename w B z o n j (old 3)).symm
      (from_history hZ3 (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (slot 3 0) (old 3 i) (slot 3 1) (slot 3 2) (old 3 j) hw3 hR hj3)

end PPAC.Migration.Internal.PacketReaderStoppingAdvance
