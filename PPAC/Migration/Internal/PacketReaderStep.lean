import PPAC.Migration.Internal.PacketReaderEmission

/-! Typed local readTokens steps for a given actual head and rest: deterministic value, scale, remainder and reversed accumulator. -/
namespace PPAC.Migration.Internal.PacketReaderStep
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStepSyntax
open StructuralListTraceSyntax (valid valid_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem valid_subst {m} {Γ : Context m} (w a c : Fin m) (he : Derives Γ (.equal a c))
    (ha : Derives Γ (valid w a)) : Derives Γ (valid w c) := by
  let P := valid w.castSucc (Fin.last m)
  have h0 : P.instantiate a = valid w a := by simp only [P,Formula.instantiate,valid_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate c = valid w c := by simp only [P,Formula.instantiate,valid_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm ha))

theorem emit_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (state w x v s a)) (he : Derives Γ (emitCase w B z o b x v s a r y q c)) :
    Derives Γ (state w r y q c) := by
  have hr := valid_subst w x r (eq_symm (.conjL (.conjR he))) (.conjL hi)
  have hy := mem_subst (eq_symm (.conjL (.conjR (.conjR he)))) hz
  have hq := mem_subst (eq_symm (.conjL (.conjR (.conjR (.conjR he))))) ho
  have hc := PacketReaderEmission.domain hZ w b v s a c hw (.conjL (.conjR hi)) (.conjR (.conjR (.conjR hi))) (.conjR (.conjR (.conjR (.conjR he))))
  exact .conjI hr (.conjI hy (.conjI hq hc))

theorem continue_domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B b x v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hi : Derives Γ (state w x v s a)) (hc : Derives Γ (continueCase w B b x v s a r y q c)) :
    Derives Γ (state w r y q c) := by
  have hr := valid_subst w x r (eq_symm (.conjL (.conjR hc))) (.conjL hi)
  have ha := valid_subst w a c (eq_symm (.conjL (.conjR (.conjR hc)))) (.conjR (.conjR (.conjR hi)))
  have hn := PacketReaderContinuation.domain hZ w B b v s y q hw hB (.conjL (.conjR hi)) (.conjR (.conjR (.conjR hc)))
  exact .conjI hr (.conjI (.conjL (.conjR hn)) (.conjI (.conjR (.conjR hn)) ha))

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a r y q c : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (.mem z w)) (ho : Derives Γ (.mem o w))
    (hi : Derives Γ (state w x v s a)) (hh : Derives Γ (step w B z o b x v s a r y q c)) :
    Derives Γ (state w r y q c) := by
  apply Derives.disjE hh
  · exact emit_domain (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ _ _ _ (add hw _) (add hz _) (add ho _) (add hi _) (.hyp (Or.inl rfl))
  · exact continue_domain (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hi _) (.hyp (Or.inl rfl))

def same {m} (r y q c t j k d : Fin m) : Formula m :=
  (Formula.equal r t).conj ((Formula.equal y j).conj ((Formula.equal q k).conj (.equal c d)))
theorem same_rename {m n} (r y q c t j k d : Fin m) (ρ : Fin m → Fin n) :
    (same r y q c t j k d).rename ρ = same (ρ r) (ρ y) (ρ q) (ρ c) (ρ t) (ρ j) (ρ k) (ρ d) := rfl

theorem emit_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a r y q c t j k d : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hi : Derives Γ (state w x v s a))
    (hc : Derives Γ (emitCase w B z o b x v s a r y q c)) (hd : Derives Γ (emitCase w B z o b x v s a t j k d)) :
    Derives Γ (same r y q c t j k d) := by
  have hr := eq_trans (.conjL (.conjR hc)) (eq_symm (.conjL (.conjR hd)))
  have hy := eq_trans (.conjL (.conjR (.conjR hc))) (eq_symm (.conjL (.conjR (.conjR hd))))
  have hq := eq_trans (.conjL (.conjR (.conjR (.conjR hc)))) (eq_symm (.conjL (.conjR (.conjR (.conjR hd)))))
  have ha := StructuralListValidity.range w a (.conjR (.conjR (.conjR hi)))
  have he := PacketReaderEmission.unique hZ w b v s a c d hw hb (.conjL (.conjR hi)) (.conjL (.conjR (.conjR hi))) ha
    (.conjR (.conjR (.conjR (.conjR hc)))) (.conjR (.conjR (.conjR (.conjR hd))))
  exact .conjI hr (.conjI hy (.conjI hq he))

theorem continue_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B b x v s a r y q c t j k d : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hs : Derives Γ (.mem s w))
    (hc : Derives Γ (continueCase w B b x v s a r y q c)) (hd : Derives Γ (continueCase w B b x v s a t j k d)) :
    Derives Γ (same r y q c t j k d) := by
  have hr := eq_trans (.conjL (.conjR hc)) (eq_symm (.conjL (.conjR hd)))
  have ha := eq_trans (.conjL (.conjR (.conjR hc))) (eq_symm (.conjL (.conjR (.conjR hd))))
  have he := PacketReaderContinuation.unique hZ w B b v s y q j k hw hB hs (.conjR (.conjR (.conjR hc))) (.conjR (.conjR (.conjR hd)))
  exact .conjI hr (.conjI (.conjL he) (.conjI (.conjR he) ha))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o b x v s a r y q c t j k d : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hb : Derives Γ (.mem b w))
    (hi : Derives Γ (state w x v s a)) (hc : Derives Γ (step w B z o b x v s a r y q c))
    (hd : Derives Γ (step w B z o b x v s a t j k d)) : Derives Γ (same r y q c t j k d) := by
  apply Derives.disjE hc
  · have hE : Derives (Context.add (emitCase w B z o b x v s a r y q c) Γ) (emitCase w B z o b x v s a r y q c) := .hyp (Or.inl rfl)
    apply Derives.disjE (add hd _)
    · exact emit_unique (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (add (add hw _) _) (add (add hb _) _) (add (add hi _) _) (add hE _) (.hyp (Or.inl rfl))
    · exact .botE (PacketReaderGuards.low_more_disjoint (ZFContext.add (ZFContext.add hZ _) _) w B b
        (add (add hw _) _) (add (add hB _) _) (add (.conjL (.conjL hE)) _) (.conjL (.hyp (Or.inl rfl))))
  · have hC : Derives (Context.add (continueCase w B b x v s a r y q c) Γ) (continueCase w B b x v s a r y q c) := .hyp (Or.inl rfl)
    apply Derives.disjE (add hd _)
    · exact .botE (PacketReaderGuards.low_more_disjoint (ZFContext.add (ZFContext.add hZ _) _) w B b
        (add (add hw _) _) (add (add hB _) _) (.conjL (.conjL (.hyp (Or.inl rfl)))) (add (.conjL hC) _))
    · exact continue_unique (ZFContext.add (ZFContext.add hZ _) _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (add (add hw _) _) (add (add hB _) _) (add (add (.conjL (.conjR (.conjR hi))) _) _) (add hC _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderStep
