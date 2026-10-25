import PPAC.Migration.Internal.PacketReaderHistoryPrependRows

/-! Original exact prepend graphs construct a real longer reader history with every internal adjacent step preserved. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryPrepend
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

def extension {m} (w B z o n t d e f : Fin m) : Formula m := .ex
  ((SequencePrependSyntax.graph f.castSucc d.castSucc n.castSucc e.castSucc (Fin.last m)).conj
    (history w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc t.castSucc d.castSucc e.castSucc (Fin.last m)))

theorem extension_rename {m k} (w B z o n t d e f : Fin m) (ρ : Fin m → Fin k) :
    (extension w B z o n t d e f).rename ρ = extension (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ t) (ρ d) (ρ e) (ρ f) := by
  simp only [extension,Formula.rename,SequencePrependSyntax.graph_rename,history_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem links {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d e f g : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o r t l d f))
    (he : Derives Γ (successor e d)) (hg : Derives Γ (SequencePrependSyntax.graph f d n e g))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) : Derives Γ (PacketReaderHistorySyntax.links w B z o d g) := by
  have hd := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hZero := PacketReaderHistoryPrependRows.zero_row hZ w B z o n r t l d e f g hw hh he hg ht
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ M
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw M)
  have hd1 : Derives Δ (.mem d.castSucc w.castSucc) := under hd M
  have hh1 := of_eq (history_rename w B z o r t l d f Fin.castSucc) (under hh M)
  have he1 := of_eq (successor_rename e d Fin.castSucc) (under he M)
  have hg1 := of_eq (SequencePrependSyntax.graph_rename f d n e g Fin.castSucc) (under hg M)
  have hZero1 := of_eq (row_rename w B z o g z Fin.castSucc) (under hZero M)
  have hi : Derives Δ M := .hyp (Or.inl rfl)
  have hiN := StructuralListTraceOrder.member_member hZ1 _ _ _ hw1 hd1 hi
  have hSplit := OmegaStructureAlgebra.decomposition_at w.castSucc (Fin.last m) (OmegaStructureInduction.decomposition w.castSucc (ZFContext.separation hZ1 OmegaStructureSyntax.splitMatrix) hw1) hiN
  apply Derives.disjE hSplit
  · let E := empty (Fin.last m)
    have hEq := OmegaUniversal.empty_unique (Fin.last m) z.castSucc (ZFContext.arithmetic (ZFContext.add hZ1 E)).base.extensionality (.hyp (Or.inl rfl)) (add (zero_at _ _ _ _ _ _ _ _ _ hh1) E)
    exact PacketReaderHistoryRowMap.index_subst _ _ _ _ _ _ _ (eq_symm hEq) (add hZero1 E)
  · let P := OmegaStructureSyntax.predecessor w.castSucc (Fin.last m)
    let R := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))
    let Ξ := Context.add R (Context.image Formula.raise (Context.add P Δ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Ξ R := .hyp (Or.inl rfl)
    have hZ2 := ZFContext.under (ZFContext.add hZ1 P) R
    have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under (add hw1 P) R)
    have hh2 := of_eq (history_rename w.castSucc B.castSucc z.castSucc o.castSucc r.castSucc t.castSucc l.castSucc d.castSucc f.castSucc Fin.castSucc) (under (add hh1 P) R)
    have he2 := of_eq (successor_rename e.castSucc d.castSucc Fin.castSucc) (under (add he1 P) R)
    have hg2 := of_eq (SequencePrependSyntax.graph_rename f.castSucc d.castSucc n.castSucc e.castSucc g.castSucc Fin.castSucc) (under (add hg1 P) R)
    have hi2 : Derives Ξ (.mem (Fin.last m).castSucc d.castSucc.castSucc) := under (add hi P) R
    have hjL := SyntaxIndexLiftOrder.predecessor_member hZ2 _ _ _ _ _ hw2 (length_at _ _ _ _ _ _ _ _ _ hh2) (successor_at _ _ _ _ _ _ _ _ _ hh2) hi2 (.conjR hR)
    have hOldRow := row_at _ _ _ _ _ _ _ _ _ _ hh2 hjL
    have hNew := PacketReaderHistoryPrependRows.successor_row hZ2 w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc e.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (under (add hd1 P) R) he2 (sequence_at _ _ _ _ _ _ _ _ _ hh2) hg2 (.conjR hR) hOldRow
    simpa only [Formula.raise,row_rename] using hNew

theorem from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d e f g : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o r t l d f))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) (he : Derives Γ (successor e d))
    (hg : Derives Γ (SequencePrependSyntax.graph f d n e g)) : Derives Γ (history w B z o n t d e g) := by
  have hd := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hN := Derives.conjL (PacketReaderCodedNormalize.domain hZ _ _ _ _ _ _ hw ht)
  have hSeq := SequencePrependGraph.sequence _ _ _ _ _ _ (sequence_at _ _ _ _ _ _ _ _ _ hh) hN hg
  have hSeed := SequencePrependEdges.zero_edge hZ _ _ _ _ _ _ _ hw hd he hg (zero_at _ _ _ _ _ _ _ _ _ hh)
  have hL := InsertLogic.new_member d l l (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hLast := SequencePrependEdges.forward_edge hZ _ _ _ _ _ _ _ _ _ hw hd he hg hL (successor_at _ _ _ _ _ _ _ _ _ hh) (last_at _ _ _ _ _ _ _ _ _ hh)
  have hLinks := links hZ w B z o n r t l d e f g hw hh he hg ht
  exact .conjI (.conjL (PacketReaderCodedNormalize.carriers _ _ _ _ _ _ ht)) (.conjI (zero_at _ _ _ _ _ _ _ _ _ hh)
    (.conjI hd (.conjI he (.conjI hSeq (.conjI hSeed (.conjI hLast hLinks))))))

theorem exists_extension {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d e f : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o r t l d f))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) (he : Derives Γ (successor e d)) :
    Derives Γ (extension w B z o n t d e f) := by
  have hd := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  let R := SequencePrependSyntax.graph f.castSucc d.castSucc n.castSucc e.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SequencePrependGraph.exists_graph hZ w f d n e hw hd he (sequence_at _ _ _ _ _ _ _ _ _ hh))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 := of_eq (history_rename w B z o r t l d f Fin.castSucc) (under hh R)
  have ht1 := of_eq (PacketReaderCodedSyntax.step_rename w B z o n r Fin.castSucc) (under ht R)
  have he1 := of_eq (successor_rename e d Fin.castSucc) (under he R)
  have hNew := from_graph hZ1 _ _ _ _ _ _ _ _ _ _ _ _ hw1 hh1 ht1 he1 hR
  have hout : Derives Δ (extension w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc t.castSucc d.castSucc e.castSucc f.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [R,Formula.instantiate,Formula.rename,SequencePrependSyntax.graph_rename,history_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hNew)
  simpa only [Formula.raise,extension_rename] using hout

end PPAC.Migration.Internal.PacketReaderHistoryPrepend
