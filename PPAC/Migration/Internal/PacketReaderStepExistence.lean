import PPAC.Migration.Internal.PacketReaderStep

/-! Exact local successor domain for all raw natural head/value/scale fields. No byte<256 or scale>0 assumption. -/
namespace PPAC.Migration.Internal.PacketReaderStepExistence
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStepSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def resultBody {m} (w B z o b x v s a : Fin m) : Formula (m+4) :=
  (state (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).conj
    (step (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 b) (old 4 x) (old 4 v) (old 4 s) (old 4 a)
      (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3))
def existsResult {m} (w B z o b x v s a : Fin m) : Formula m := existsMany 4 (resultBody w B z o b x v s a)
theorem resultBody_lift {m n} (w B z o b x v s a : Fin m) (ρ : Fin m → Fin n) :
    (resultBody w B z o b x v s a).rename (lift 4 ρ) = resultBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ b) (ρ x) (ρ v) (ρ s) (ρ a) := by
  simp only [resultBody,Formula.rename,state_rename,step_rename,lift_old,lift_slot]
theorem existsResult_rename {m n} (w B z o b x v s a : Fin m) (ρ : Fin m → Fin n) :
    (existsResult w B z o b x v s a).rename ρ = existsResult (ρ w) (ρ B) (ρ z) (ρ o) (ρ b) (ρ x) (ρ v) (ρ s) (ρ a) := by
  simp only [existsResult,existsMany_rename,resultBody_lift]

theorem intro_result {m} {Γ : Context m} (w B z o b x v s a r y q c : Fin m)
    (hi : Derives Γ (state w r y q c)) (hh : Derives Γ (step w B z o b x v s a r y q c)) :
    Derives Γ (existsResult w B z o b x v s a) := by
  apply HornBinderRules.intro_many 4 _ (PacketVarintPrefixRecursionSyntax.four r y q c)
  exact of_eq (by simp only [resultBody,Formula.rename,state_rename,step_rename,assign_old,assign_slot]; rfl) (.conjI hi hh)

theorem emit_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) (hb : Derives Γ (.mem b w))
    (hi : Derives Γ (state w x v s a)) (hf : Derives Γ (finish B z o b s)) : Derives Γ (existsResult w B z o b x v s a) := by
  let C := (StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).conj (emission w.castSucc b.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (PacketReaderEmission.exists_emission hZ w b v s a hw hb (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi))) (.conjR (.conjR (.conjR hi))))
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hi1 := of_eq (state_rename w x v s a Fin.castSucc) (under hi C)
  have hf1 := of_eq (finish_rename B z o b s Fin.castSucc) (under hf C)
  have hvld : Derives Δ (state w.castSucc x.castSucc z.castSucc o.castSucc (Fin.last m)) := .conjI (.conjL hi1) (.conjI (under hz C) (.conjI (under ho C) (.conjL hC)))
  have he : Derives Δ (emitCase w.castSucc B.castSucc z.castSucc o.castSucc b.castSucc x.castSucc v.castSucc s.castSucc a.castSucc x.castSucc z.castSucc o.castSucc (Fin.last m)) :=
    .conjI hf1 (.conjI (.eqRefl _) (.conjI (.eqRefl _) (.conjI (.eqRefl _) (.conjR hC))))
  simpa only [Formula.raise,existsResult_rename] using intro_result _ _ _ _ _ _ _ _ _ _ _ _ _ hvld (.disjL he)

theorem continue_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hb : Derives Γ (.mem b w))
    (hi : Derives Γ (state w x v s a)) (hm : Derives Γ (more B b)) : Derives Γ (existsResult w B z o b x v s a) := by
  let R := PacketReaderContinuation.resultBody w B b v s
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ (PacketReaderContinuation.exists_update hZ w B b v s hw hB hb (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi))) hm)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hi2 := of_eq (state_rename w x v s a (old 2)) (HornBinderRules.under_body 2 hi R)
  have hm2 := of_eq (more_rename B b (old 2)) (HornBinderRules.under_body 2 hm R)
  have hvld : Derives Δ (state (old 2 w) (old 2 x) (slot 2 0) (slot 2 1) (old 2 a)) :=
    .conjI (.conjL hi2) (.conjI (.conjL hR) (.conjI (.conjL (.conjR hR)) (.conjR (.conjR (.conjR hi2)))))
  have hc : Derives Δ (continueCase (old 2 w) (old 2 B) (old 2 b) (old 2 x) (old 2 v) (old 2 s) (old 2 a) (old 2 x) (slot 2 0) (slot 2 1) (old 2 a)) :=
    .conjI hm2 (.conjI (.eqRefl _) (.conjI (.eqRefl _) (.conjR (.conjR hR))))
  exact of_eq (existsResult_rename w B z o b x v s a (old 2)).symm (intro_result _ _ _ _ _ _ _ _ _ _ _ _ _ hvld (.disjR hc))

theorem exists_of_not_reject {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) (hb : Derives Γ (.mem b w))
    (hi : Derives Γ (state w x v s a)) (hn : Derives Γ (reject B z o b s).neg) : Derives Γ (existsResult w B z o b x v s a) := by
  apply Derives.disjE (PacketReaderGuards.partition hZ w B z o b s hw hB hb)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact emit_exists (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ _ _ _ _ (add (add hw _) _) (add (add hz _) _) (add (add ho _) _) (add (add hb _) _) (add (add hi _) _) (.hyp (Or.inl rfl))
    · exact .botE (.impE (add (add hn _) _) (.hyp (Or.inl rfl)))
  · exact continue_exists (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hb _) (add hi _) (.hyp (Or.inl rfl))

theorem reject_no_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hr : Derives Γ (reject B z o b s)) :
    Derives Γ (existsResult w B z o b x v s a).neg := by
  apply Derives.impI
  let R := resultBody w B z o b x v s a
  let Δ := Context.add R (raisedContext 4 (Context.add (existsResult w B z o b x v s a) Γ))
  apply HornBinderRules.eliminate_many 4 R _ (.hyp (Or.inl rfl))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ (existsResult w B z o b x v s a)) R
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw (existsResult w B z o b x v s a)) R)
  have hB4 : Derives Δ (.mem (old 4 B) (old 4 w)) := HornBinderRules.under_body 4 (add hB _) R
  have hr4 := of_eq (reject_rename B z o b s (old 4)) (HornBinderRules.under_body 4 (add hr (existsResult w B z o b x v s a)) R)
  exact .impE (PacketReaderGuards.reject_no_step hZ4 _ _ _ _ _ _ _ _ _ _ _ _ _ hw4 hB4 hr4) (.conjR hR)

theorem domain_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) (hb : Derives Γ (.mem b w))
    (hi : Derives Γ (state w x v s a)) : Derives Γ ((existsResult w B z o b x v s a).iff (reject B z o b s).neg) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    exact .impE (reject_no_result (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ _ _ _ _ (add (add hw _) _) (add (add hB _) _) (.hyp (Or.inl rfl))) (.hyp (Or.inr (Or.inl rfl)))
  · apply Derives.impI
    exact exists_of_not_reject (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (add hb _) (add hi _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderStepExistence
