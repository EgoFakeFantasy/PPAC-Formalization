import PPAC.Migration.Internal.PacketReaderHistoryConsumption

/-! Actual Nil and noncanonical-byte boundaries forbid a further coded step; Nil input can occur only at a history's last index. EOF return reversal is still separate. -/
namespace PPAC.Migration.Internal.PacketReaderConsumptionStopping
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderConsumptionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem no_step_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (PacketReaderStateSyntax.code w l v s a n))
    (hn : Derives Γ (PacketReaderInputExistence.admissible w B z o l v s a).neg) :
    Derives Γ (PacketReaderCodedSyntax.step w B z o n r).neg := by
  apply Derives.impI
  let H := PacketReaderCodedSyntax.step w B z o n r
  let Δ := Context.add H Γ
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.add hZ H
  have hrN := Derives.conjR (PacketReaderCodedNormalize.domain hZ1 w B z o n r (add hw H) hH)
  have hex : Derives Δ (PacketReaderCodedSyntax.existsNext w B z o n) := by
    apply Derives.exI r
    exact of_eq (by simp only [H,Formula.instantiate,Formula.rename,PacketReaderCodedSyntax.step_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hrN hH)
  have ha := PacketReaderCodedExistence.domain_at_source hZ1 w B z o n l v s a (add hw H) (add hB H) (add hc H) hex
  exact .impE (add hn H) ha

theorem nil_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (PacketReaderStateSyntax.code w l v s a n))
    (hn : Derives Γ (StructuralListSyntax.nilCode w l)) : Derives Γ (PacketReaderCodedSyntax.step w B z o n r).neg := by
  apply no_step_at_code hZ w B z o n r l v s a hw hB hc
  apply Derives.impI
  exact .impE (.conjL (.conjR (.hyp (Or.inl rfl)))) (add hn _)

theorem blocked_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (PacketReaderStateSyntax.code w l v s a n))
    (hb : Derives Γ (PacketReaderInputSyntax.blocked w B z o l s)) : Derives Γ (PacketReaderCodedSyntax.step w B z o n r).neg := by
  apply no_step_at_code hZ w B z o n r l v s a hw hB hc
  apply Derives.impI
  exact .impE (.conjR (.conjR (.hyp (Or.inl rfl)))) (add hb _)

theorem nil_at_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hi : Derives Γ (input w n l))
    (hn : Derives Γ (StructuralListSyntax.nilCode w l)) : Derives Γ (PacketReaderCodedSyntax.step w B z o n r).neg := by
  let R := inputBody w n l
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hB3 : Derives Δ (.mem (old 3 B) (old 3 w)) := HornBinderRules.under_body 3 hB R
  have hn3 := of_eq (StructuralListSyntax.nilCode_rename w l (old 3)) (HornBinderRules.under_body 3 hn R)
  exact of_eq (by simp only [Formula.rename,Formula.neg,PacketReaderCodedSyntax.step_rename])
    (nil_at_code hZ3 (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 n) (old 3 r) (old 3 l) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3 hR hn3)

theorem nil_before_end {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f))
    (hi : Derives Γ (.mem i l)) (hL : Derives Γ (inputAt w f i L)) (hn : Derives Γ (StructuralListSyntax.nilCode w L)) : Derives Γ .bot := by
  let R := PacketReaderHistorySyntax.rowBody w B z o f i
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ (PacketReaderHistoryLaws.row_at _ _ _ _ _ _ _ _ _ _ hh hi)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hB3 : Derives Δ (.mem (old 3 B) (old 3 w)) := HornBinderRules.under_body 3 hB R
  have hseq := PacketReaderHistoryLaws.sequence_at _ _ _ _ _ _ _ _ _ hh
  have hf3 := of_eq (SequenceSyntax.sequence_rename f d w (old 3)) (HornBinderRules.under_body 3 hseq R)
  have hL3 := of_eq (inputAt_rename w f i L (old 3)) (HornBinderRules.under_body 3 hL R)
  have hn3 := of_eq (StructuralListSyntax.nilCode_rename w L (old 3)) (HornBinderRules.under_body 3 hn R)
  have hin := Derives.impE (.conjL (PacketReaderHistoryInput.at_edge hZ3 _ _ _ _ _ _ hf3 (.conjL (.conjR hR)))) hL3
  exact .impE (nil_at_input hZ3 _ _ _ _ _ _ _ hw3 hB3 hin hn3) (.conjR (.conjR (.conjR hR)))

theorem nil_index_is_last {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i L : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hh : Derives Γ (PacketReaderHistorySyntax.history w B z o n r l d f))
    (hi : Derives Γ (.mem i d)) (hL : Derives Γ (inputAt w f i L)) (hn : Derives Γ (StructuralListSyntax.nilCode w L)) : Derives Γ (.equal i l) := by
  apply Derives.disjE (InsertLogic.member_cases d l l i (PacketReaderHistoryLaws.successor_at _ _ _ _ _ _ _ _ _ hh) hi)
  · exact .botE (nil_before_end (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hh _) (.hyp (Or.inl rfl)) (add hL _) (add hn _))
  · exact .hyp (Or.inl rfl)

end PPAC.Migration.Internal.PacketReaderConsumptionStopping
