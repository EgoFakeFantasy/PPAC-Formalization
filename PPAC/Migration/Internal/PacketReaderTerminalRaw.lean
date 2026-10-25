import PPAC.Migration.Internal.PacketReaderTerminalSyntax

/-! The three original observations are mutually exclusive and exactly characterize no coded successor at every actual state code. -/
namespace PPAC.Migration.Internal.PacketReaderTerminalRaw
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderTerminalSyntax PacketReaderInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem no_next_of_raw {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n))
    (hr : Derives Γ (raw w B z o L v s a)) : Derives Γ (PacketReaderCodedSyntax.existsNext w B z o n).neg := by
  apply Derives.impI
  let H := PacketReaderCodedSyntax.existsNext w B z o n
  have hA := PacketReaderCodedExistence.domain_at_source (ZFContext.add hZ H) w B z o n L v s a (add hw H) (add hB H) (add hc H) (.hyp (Or.inl rfl))
  apply Derives.disjE (add hr H)
  · exact .impE (add (.conjL (.conjR hA)) _) (.conjL (.conjR (.hyp (Or.inl rfl))))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .impE (add (add (.conjL (.conjR hA)) _) _) (.conjL (.conjR (.hyp (Or.inl rfl))))
    · exact .impE (add (add (.conjR (.conjR hA)) _) _) (.conjR (.hyp (Or.inl rfl)))

theorem raw_of_no_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) (hn : Derives Γ (PacketReaderCodedSyntax.existsNext w B z o n).neg) :
    Derives Γ (raw w B z o L v s a) := by
  have hO := PacketReaderInputOutcomes.classify hZ w B z o L v s a hw hB hz ho (.conjL hc)
  apply Derives.disjE hO
  · exact .disjL (.hyp (Or.inl rfl))
  · let P := (eofFailure w z o L v s a).disj (((PacketReaderStepSyntax.state w L v s a).conj (blocked w B z o L s)).disj (existsResult w B z o L v s a))
    apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add P Γ) P)
    · exact .disjR (.disjL (.hyp (Or.inl rfl)))
    · let Q := ((PacketReaderStepSyntax.state w L v s a).conj (blocked w B z o L s)).disj (existsResult w B z o L v s a)
      apply Derives.disjE (.hyp (Or.inl rfl) : Derives (Context.add Q (Context.add P Γ)) Q)
      · exact .disjR (.disjR (.hyp (Or.inl rfl)))
      · let R := existsResult w B z o L v s a
        let Δ := Context.add R (Context.add Q (Context.add P Γ))
        have hZ3 := ZFContext.add (ZFContext.add (ZFContext.add hZ P) Q) R
        have lift3 {p : Formula m} (hp : Derives Γ p) : Derives Δ p := add (add (add hp P) Q) R
        have hAd := PacketReaderInputExistence.result_domain hZ3 w B z o L v s a (lift3 hw) (lift3 hB) (.hyp (Or.inl rfl))
        have hNext := PacketReaderCodedExistence.exists_next hZ3 w B z o n L v s a (lift3 hw) (lift3 hB) (lift3 hz) (lift3 ho) (lift3 hc) hAd
        exact .botE (.impE (lift3 hn) hNext)

theorem at_actual_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hc : Derives Γ (PacketReaderStateSyntax.code w L v s a n)) :
    Derives Γ ((raw w B z o L v s a).iff (PacketReaderCodedSyntax.existsNext w B z o n).neg) := by
  apply Derives.conjI
  · apply Derives.impI
    exact no_next_of_raw (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact raw_of_no_next (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (add hc _) (.hyp (Or.inl rfl))

theorem success_failure_disjoint {m} {Γ : Context m} (w z o L v s a : Fin m)
    (hs : Derives Γ (eofSuccess w z o L v s a)) (hf : Derives Γ (eofFailure w z o L v s a)) : Derives Γ .bot :=
  PacketReaderInputOutcomes.eof_incompatible _ _ _ _ _ _ _ hs hf

theorem success_reject_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (eofSuccess w z o L v s a)) (hr : Derives Γ (blocked w B z o L s)) : Derives Γ .bot :=
  .impE (PacketReaderInputNormalize.nil_no_blocked hZ w B z o L s hw (.conjL (.conjR hs))) hr

theorem failure_reject_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L v s a : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (eofFailure w z o L v s a)) (hr : Derives Γ (blocked w B z o L s)) : Derives Γ .bot :=
  .impE (PacketReaderInputNormalize.nil_no_blocked hZ w B z o L s hw (.conjL (.conjR hf))) hr

end PPAC.Migration.Internal.PacketReaderTerminalRaw
