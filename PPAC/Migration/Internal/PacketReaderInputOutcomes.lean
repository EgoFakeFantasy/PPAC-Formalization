import PPAC.Migration.Internal.PacketReaderInputExistence

/-! Exact four-way dispatch of every raw reader state. EOF observations retain the source guard but do not claim the accumulator reverse has been computed. -/
namespace PPAC.Migration.Internal.PacketReaderInputOutcomes
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def outcome {m} (w B z o l v s a : Fin m) : Formula m :=
  (eofSuccess w z o l v s a).disj ((eofFailure w z o l v s a).disj
    (((PacketReaderStepSyntax.state w l v s a).conj (blocked w B z o l s)).disj (existsResult w B z o l v s a)))
theorem outcome_rename {m k} (w B z o l v s a : Fin m) (ρ : Fin m → Fin k) :
    (outcome w B z o l v s a).rename ρ = outcome (ρ w) (ρ B) (ρ z) (ρ o) (ρ l) (ρ v) (ρ s) (ρ a) := by
  simp only [outcome,Formula.rename,eofSuccess_rename,eofFailure_rename,PacketReaderStepSyntax.state_rename,blocked_rename,existsResult_rename]

theorem classify {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a)) : Derives Γ (outcome w B z o l v s a) := by
  apply SourcePropositional.by_cases (StructuralListSyntax.nilCode w l)
  · apply Derives.disjE (PacketReaderGuards.eof_partition z o v s)
    · exact .disjL (.conjI (add (add hi _) _) (.conjI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))))
    · exact .disjR (.disjL (.conjI (add (add hi _) _) (.conjI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))))
  · apply SourcePropositional.by_cases (blocked w B z o l s)
    · exact .disjR (.disjR (.disjL (.conjI (add (add hi _) _) (.hyp (Or.inl rfl)))))
    · exact .disjR (.disjR (.disjR (PacketReaderInputExistence.non_nil_non_blocked (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ _ _ _
        (add (add hw _) _) (add (add hB _) _) (add (add hz _) _) (add (add ho _) _) (add (add hi _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))))

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hc : Derives Γ (outcome w B z o l v s a)) :
    Derives Γ (PacketReaderStepSyntax.state w l v s a) := by
  apply Derives.disjE hc
  · exact .conjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .conjL (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .conjL (.hyp (Or.inl rfl))
      · exact .conjL (PacketReaderInputExistence.result_domain (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _ _ _ _ _ _ _ _
          (add (add (add hw _) _) _) (add (add (add hB _) _) _) (.hyp (Or.inl rfl)))

theorem outcome_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w)) :
    Derives Γ ((outcome w B z o l v s a).iff (PacketReaderStepSyntax.state w l v s a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact domain (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hB _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact classify (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl))

theorem eof_incompatible {m} {Γ : Context m} (w z o l v s a : Fin m)
    (hs : Derives Γ (eofSuccess w z o l v s a)) (hf : Derives Γ (eofFailure w z o l v s a)) : Derives Γ .bot :=
  .impE (.conjR (.conjR hf)) (.conjR (.conjR hs))

theorem nil_no_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hn : Derives Γ (StructuralListSyntax.nilCode w l)) :
    Derives Γ (existsResult w B z o l v s a).neg := by
  apply Derives.impI
  have hd := PacketReaderInputExistence.result_domain (ZFContext.add hZ (existsResult w B z o l v s a)) w B z o l v s a (add hw _) (add hB _) (.hyp (Or.inl rfl))
  exact .impE (.conjL (.conjR hd)) (add hn _)

theorem blocked_no_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o l v s a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hb : Derives Γ (blocked w B z o l s)) :
    Derives Γ (existsResult w B z o l v s a).neg := by
  apply Derives.impI
  have hd := PacketReaderInputExistence.result_domain (ZFContext.add hZ (existsResult w B z o l v s a)) w B z o l v s a (add hw _) (add hB _) (.hyp (Or.inl rfl))
  exact .impE (.conjR (.conjR hd)) (add hb _)

end PPAC.Migration.Internal.PacketReaderInputOutcomes
