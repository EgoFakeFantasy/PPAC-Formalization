import PPAC.Migration.Internal.PacketReaderStepSyntax

/-! Object guard partition, including the original noncanonical terminal-zero rejection. -/
namespace PPAC.Migration.Internal.PacketReaderGuards
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStepSyntax

theorem finish_reject_disjoint {m} {Γ : Context m} (B z o b s : Fin m)
    (hf : Derives Γ (finish B z o b s)) (hr : Derives Γ (reject B z o b s)) : Derives Γ .bot := by
  apply Derives.disjE (.conjR hf)
  · exact .impE (add (.conjL (.conjR hr)) _) (.hyp (Or.inl rfl))
  · exact .impE (.hyp (Or.inl rfl)) (add (.conjR (.conjR hr)) _)

theorem low_partition {m} {Γ : Context m} (B z o b s : Fin m) (hb : Derives Γ (.mem b B)) :
    Derives Γ ((finish B z o b s).disj (reject B z o b s)) := by
  apply SourcePropositional.by_cases (Formula.equal s o)
  · exact .disjL (.conjI (add hb _) (.disjL (.hyp (Or.inl rfl))))
  · apply SourcePropositional.by_cases (Formula.equal b z)
    · exact .disjR (.conjI (add (add hb _) _) (.conjI (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))))
    · exact .disjL (.conjI (add (add hb _) _) (.disjR (.hyp (Or.inl rfl))))

theorem partition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ (((finish B z o b s).disj (reject B z o b s)).disj (more B b)) := by
  apply Derives.disjE (NaturalOrderBasic.compare hZ w B b hw hB hb)
  · exact .disjR (.disjL (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.disjR (.hyp (Or.inl rfl)))
    · exact .disjL (low_partition B z o b s (.hyp (Or.inl rfl)))

theorem low_more_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B b : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hl : Derives Γ (.mem b B)) (hm : Derives Γ (more B b)) : Derives Γ .bot :=
  NaturalOrderBasic.below_not_reverse hZ w B b hw hB hm hl

theorem reject_no_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hr : Derives Γ (reject B z o b s)) : Derives Γ (step w B z o b x v s a r y q c).neg := by
  apply Derives.impI
  apply Derives.disjE (.hyp (Or.inl rfl))
  · exact finish_reject_disjoint B z o b s (.conjL (.hyp (Or.inl rfl))) (add (add hr _) _)
  · exact low_more_disjoint (ZFContext.add (ZFContext.add hZ _) _) w B b
      (add (add hw _) _) (add (add hB _) _) (add (add (.conjL hr) _) _) (.conjL (.hyp (Or.inl rfl)))

theorem eof_partition {m} {Γ : Context m} (z o v s : Fin m) : Derives Γ ((eof z o v s).disj (eof z o v s).neg) := by
  apply SourcePropositional.by_cases (eof z o v s)
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderGuards
