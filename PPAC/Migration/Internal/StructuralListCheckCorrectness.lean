import PPAC.Migration.Internal.StructuralListCheckInvariant

/-! 真实首次终端检查接受恰为原Valid，拒绝恰为其否定；覆盖全部内部自然码。 -/
namespace PPAC.Migration.Internal.StructuralListCheckCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListCheckSyntax
open StructuralListTraceSyntax (valid valid_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem terminal_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (terminal w b)) : Derives Γ ((valid w b).iff (nilCode w b)) := by
  apply Derives.disjE ht
  · let E := empty b
    let Δ := Context.add E Γ
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hv := StructuralListDecode.zero_rejected (ZFContext.add hZ E) _ _ (add hw E) hE
    apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (add hv _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .botE (.impE (StructuralListDecode.nil_positive _ _ (.hyp (Or.inl rfl))) (add hE _))
  · apply Derives.conjI
    · apply Derives.impI
      exact .hyp (Or.inr (Or.inl rfl))
    · apply Derives.impI
      exact StructuralListTraceBase.valid_nil (ZFContext.add (ZFContext.add hZ _) _) _ _ (add (add hw _) _) (.hyp (Or.inl rfl))

theorem terminal_of_check {m} {Γ : Context m} (w n b : Fin m) (hc : Derives Γ (checkValue w n b)) : Derives Γ (terminal w b) := by
  let R := checkedAt w.castSucc n.castSucc (Fin.last m) b.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE (p := R) hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise, terminal_rename] using Derives.conjR (.conjL hR)

theorem correct_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r b : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (checkedAt w n r b)) : Derives Γ ((valid w n).iff (nilCode w b)) := by
  have hi := StructuralListCheckInvariant.at_index hZ w n r hw (.conjL (.conjL (.conjL hc)))
  have hp := StructuralListCheckInvariantSyntax.at_value _ _ _ _ hi (.conjR hc) (.conjR (.conjL (.conjL hc)))
  exact StructuralListSuffixArithmetic.iff_trans hp (terminal_iff hZ w b hw (.conjR (.conjL hc)))

theorem correct_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (checkValue w n b)) : Derives Γ ((valid w n).iff (nilCode w b)) := by
  let R := checkedAt w.castSucc n.castSucc (Fin.last m) b.castSucc
  let Δ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hc
  apply Derives.exE (p := R) hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hout := correct_at (ZFContext.under hZ R) _ _ _ _ hw1 (.hyp (Or.inl rfl))
  simpa only [Formula.raise, Formula.rename, Formula.iff, valid_rename, nilCode_rename] using hout

theorem reject_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (checkValue w n b)) : Derives Γ ((empty b).iff (valid w n).neg) := by
  have hiff := correct_value hZ w n b hw hc
  have ht := terminal_of_check w n b hc
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.impI
    have hn : Derives (Context.add (valid w n) (Context.add (empty b) Γ)) (nilCode w b) :=
      Derives.impE (add (add (.conjL hiff) _) _) (.hyp (Or.inl rfl))
    exact .impE (StructuralListDecode.nil_positive _ _ hn) (.hyp (Or.inr (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.disjE (add ht _)
    · exact .hyp (Or.inl rfl)
    · exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.impE (add (add (.conjR hiff) _) _) (.hyp (Or.inl rfl))))

theorem intro_accepts {m} {Γ : Context m} (w n b : Fin m) (hc : Derives Γ (checkValue w n b)) (hn : Derives Γ (nilCode w b)) : Derives Γ (accepts w n) := by
  apply Derives.exI b
  simpa only [Formula.instantiate, Formula.rename, checkValue_rename, nilCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hc hn

theorem intro_rejects {m} {Γ : Context m} (w n b : Fin m) (hc : Derives Γ (checkValue w n b)) (he : Derives Γ (empty b)) : Derives Γ (rejects w n) := by
  apply Derives.exI b
  simpa only [Formula.instantiate, Formula.rename, checkValue_rename, empty_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hc he

theorem accepted_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepts w n)) : Derives Γ (valid w n) := by
  let B := (checkValue w.castSucc n.castSucc (Fin.last m)).conj (nilCode w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at ha
  apply Derives.exE (p := B) ha
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := Derives.impE (.conjR (correct_value (ZFContext.under hZ B) _ _ _ hw1 (.conjL hB))) (.conjR hB)
  simpa only [Formula.raise, valid_rename] using hout

theorem rejected_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (rejects w n)) : Derives Γ (valid w n).neg := by
  let B := (checkValue w.castSucc n.castSucc (Fin.last m)).conj (empty (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at ha
  apply Derives.exE (p := B) ha
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := Derives.impE (.conjL (reject_value (ZFContext.under hZ B) _ _ _ hw1 (.conjL hB))) (.conjR hB)
  simpa only [Formula.raise, Formula.rename, Formula.neg, valid_rename] using hout

theorem accepts_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hv : Derives Γ (valid w n)) : Derives Γ (accepts w n) := by
  have hc := StructuralListCheckMinimal.exists_check hZ w n hw hn
  let B := checkValue w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hc
  apply Derives.exE (p := B) hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hv1 : Derives Δ (valid w.castSucc n.castSucc) := by simpa only [Formula.raise, valid_rename] using under hv B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hnil := Derives.impE (.conjL (correct_value (ZFContext.under hZ B) _ _ _ hw1 hB)) hv1
  have hout := intro_accepts _ _ _ hB hnil
  simpa only [Formula.raise, accepts_rename] using hout

theorem rejects_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hv : Derives Γ (valid w n).neg) : Derives Γ (rejects w n) := by
  have hc := StructuralListCheckMinimal.exists_check hZ w n hw hn
  let B := checkValue w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hc
  apply Derives.exE (p := B) hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hv1 : Derives Δ (valid w.castSucc n.castSucc).neg := by simpa only [Formula.raise, Formula.rename, Formula.neg, valid_rename] using under hv B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := Derives.impE (.conjR (reject_value (ZFContext.under hZ B) _ _ _ hw1 hB)) hv1
  have hout := intro_rejects _ _ _ hB he
  simpa only [Formula.raise, rejects_rename] using hout

theorem accepts_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((valid w n).iff (accepts w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact accepts_complete (ZFContext.add hZ _) _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact accepted_input (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))

theorem rejects_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((valid w n).neg.iff (rejects w n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact rejects_complete (ZFContext.add hZ _) _ _ (add hw _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact rejected_input (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))

theorem exclusive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepts w n)) (hr : Derives Γ (rejects w n)) : Derives Γ .bot :=
  .impE (rejected_input hZ w n hw hr) (accepted_input hZ w n hw ha)

theorem decode_accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepts w n)) : Derives Γ (StructuralListFieldGraphSyntax.decoded w n) :=
  StructuralListFieldDecode.exists_decoded hZ w n hw (accepted_input hZ w n hw ha)
theorem nil_accepts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) : Derives Γ (accepts w n) := by
  have hv := StructuralListTraceBase.valid_nil hZ w n hw hn
  exact accepts_complete hZ w n hw (StructuralListValidity.range w n hv) hv

theorem zero_rejects {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (rejects w z) :=
  rejects_complete hZ w z hw (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (StructuralListDecode.zero_rejected hZ w z hw hz)

theorem classify_value {m} {Γ : Context m} (w n b : Fin m) (hc : Derives Γ (checkValue w n b)) : Derives Γ ((accepts w n).disj (rejects w n)) := by
  apply Derives.disjE (terminal_of_check w n b hc)
  · exact .disjR (intro_rejects _ _ _ (add hc _) (.hyp (Or.inl rfl)))
  · exact .disjL (intro_accepts _ _ _ (add hc _) (.hyp (Or.inl rfl)))

theorem classification {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) : Derives Γ ((accepts w n).disj (rejects w n)) := by
  have hc := StructuralListCheckMinimal.exists_check hZ w n hw hn
  let B := checkValue w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hc
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := classify_value _ _ _ hB
  simpa only [Formula.raise, Formula.rename, accepts_rename, rejects_rename] using hout
end PPAC.Migration.Internal.StructuralListCheckCorrectness
