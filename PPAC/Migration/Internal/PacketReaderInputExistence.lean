import PPAC.Migration.Internal.PacketReaderInputStep

/-! Full input successor existence after eliminating both actual Cons fields and all four output witnesses. -/
namespace PPAC.Migration.Internal.PacketReaderInputExistence
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a b x : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a)) (hh : Derives Γ (headRest w l b x))
    (hn : Derives Γ (PacketReaderStepSyntax.reject B z o b s).neg) : Derives Γ (existsResult w B z o l v s a) := by
  have ht := PacketReaderInputFields.rest_state _ _ _ _ _ _ _ hi hh
  have hex := PacketReaderStepExistence.exists_of_not_reject hZ w B z o b x v s a hw hB hz ho (.conjL hh) ht hn
  let R := PacketReaderStepExistence.resultBody w B z o b x v s a
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hex
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hi4 := of_eq (PacketReaderStepSyntax.state_rename w l v s a (old 4)) (HornBinderRules.under_body 4 hi R)
  have hh4 := of_eq (headRest_rename w l b x (old 4)) (HornBinderRules.under_body 4 hh R)
  have hA := intro_advance _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi4 hh4 (.conjR hR)
  exact of_eq (existsResult_rename w B z o l v s a (old 4)).symm (intro_result _ _ _ _ _ _ _ _ _ _ _ _ (.conjL hR) hA)

theorem non_nil_non_blocked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a)) (hn : Derives Γ (StructuralListSyntax.nilCode w l).neg)
    (hb : Derives Γ (blocked w B z o l s).neg) : Derives Γ (existsResult w B z o l v s a) := by
  apply Derives.disjE (PacketReaderInputFields.decomposition hZ w l hw (.conjL hi))
  · exact .botE (.impE (add hn _) (.hyp (Or.inl rfl)))
  · let H := hasHead w l
    let R := headBody w l
    let Δ := Context.add R (raisedContext 2 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 2 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ H) R
    have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 (add hw H) R)
    have hB2 : Derives Δ (.mem (old 2 B) (old 2 w)) := HornBinderRules.under_body 2 (add hB H) R
    have hz2 : Derives Δ (.mem (old 2 z) (old 2 w)) := HornBinderRules.under_body 2 (add hz H) R
    have ho2 : Derives Δ (.mem (old 2 o) (old 2 w)) := HornBinderRules.under_body 2 (add ho H) R
    have hi2 := of_eq (PacketReaderStepSyntax.state_rename w l v s a (old 2)) (HornBinderRules.under_body 2 (add hi H) R)
    have hb2 : Derives Δ (blocked (old 2 w) (old 2 B) (old 2 z) (old 2 o) (old 2 l) (old 2 s)).neg :=
      of_eq (by simp only [Formula.rename,Formula.neg,blocked_rename]) (HornBinderRules.under_body 2 (add hb H) R)
    have hnr : Derives Δ (PacketReaderStepSyntax.reject (old 2 B) (old 2 z) (old 2 o) (slot 2 0) (old 2 s)).neg := by
      apply Derives.impI
      exact .impE (add hb2 _) (intro_blocked _ _ _ _ _ _ _ _ (add hR _) (.hyp (Or.inl rfl)))
    exact of_eq (existsResult_rename w B z o l v s a (old 2)).symm (at_cons hZ2 _ _ _ _ _ _ _ _ _ _ hw2 hB2 hz2 ho2 hi2 hR hnr)

def admissible {m} (w B z o l v s a : Fin m) : Formula m :=
  (PacketReaderStepSyntax.state w l v s a).conj ((StructuralListSyntax.nilCode w l).neg.conj (blocked w B z o l s).neg)
theorem admissible_rename {m k} (w B z o l v s a : Fin m) (ρ : Fin m → Fin k) :
    (admissible w B z o l v s a).rename ρ = admissible (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [admissible,Formula.rename,Formula.neg,PacketReaderStepSyntax.state_rename,StructuralListSyntax.nilCode_rename,blocked_rename]

theorem result_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (existsResult w B z o l v s a)) :
    Derives Γ (admissible w B z o l v s a) := by
  let R := resultBody w B z o l v s a
  let Δ := Context.add R (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 R _ hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hA := Derives.conjR hR
  have hZ4 := HornBinderRules.zf_body 4 hZ R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 hB R
  have hn : Derives Δ (StructuralListSyntax.nilCode (old 4 w) (old 4 l)).neg := by
    apply Derives.impI
    exact .impE (PacketReaderInputNormalize.nil_no_advance (ZFContext.add hZ4 _) _ _ _ _ _ _ _ _ _ _ _ _ (add hw4 _) (.hyp (Or.inl rfl))) (add hA _)
  have hb : Derives Δ (blocked (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 l) (old 4 s)).neg := by
    apply Derives.impI
    exact PacketReaderInputStep.blocked_incompatible (ZFContext.add hZ4 _) _ _ _ _ _ _ _ _ _ _ _ _ (add hw4 _) (add hB4 _) (.hyp (Or.inl rfl)) (add hA _)
  exact of_eq (admissible_rename w B z o l v s a (old 4)).symm (.conjI (.conjL hA) (.conjI hn hb))

theorem domain_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) :
    Derives Γ ((existsResult w B z o l v s a).iff (admissible w B z o l v s a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact result_domain (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hH : Derives (Context.add (admissible w B z o l v s a) Γ) (admissible w B z o l v s a) := .hyp (Or.inl rfl)
    exact non_nil_non_blocked (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.conjL hH) (.conjL (.conjR hH)) (.conjR (.conjR hH))

end PPAC.Migration.Internal.PacketReaderInputExistence
