import PPAC.Migration.Internal.PacketReaderRunPrepend

/-! The actual complete reader run satisfies the original recursive one-step equation on all internal candidate outputs. -/
namespace PPAC.Migration.Internal.PacketReaderRunStep
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderReturnCodedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem output_subst {m} {Γ : Context m} (w B z o n p q : Fin m) (he : Derives Γ (.equal p q))
    (hp : Derives Γ (run w B z o n p)) : Derives Γ (run w B z o n q) := by
  let P := run w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc (Fin.last m)
  have h0 : P.instantiate p = run w B z o n p := by simp only [P,Formula.instantiate,run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = run w B z o n q := by simp only [P,Formula.instantiate,run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hp))

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) (hr : Derives Γ (run w B z o n q)) : Derives Γ (run w B z o r q) := by
  have hC := Derives.conjR (PacketReaderCodedNormalize.carriers _ _ _ _ _ _ ht)
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (run w.castSucc B.castSucc z.castSucc o.castSucc r.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderReturnRunExistence.exists_run hZ w B z o r hw hB hz ho hC)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have ht1 := of_eq (PacketReaderCodedSyntax.step_rename w B z o n r Fin.castSucc) (under ht R)
  have hr1 := of_eq (run_rename w B z o n q Fin.castSucc) (under hr R)
  have hnRet := PacketReaderRunPrepend.backward hZ1 w.castSucc B.castSucc z.castSucc o.castSucc n.castSucc r.castSucc (Fin.last m) hw1 ht1 (.conjR hR)
  have heq := PacketReaderReturnRunUnique.unique hZ1 _ _ _ _ _ _ _ hw1 (under hB R) hnRet hr1
  simpa only [Formula.raise,run_rename] using output_subst _ _ _ _ _ _ _ heq (.conjR hR)

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) :
    Derives Γ ((run w B z o n q).iff (run w B z o r q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hB _) (add hz _) (add ho _) (add ht _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact PacketReaderRunPrepend.backward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add ht _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderRunStep
