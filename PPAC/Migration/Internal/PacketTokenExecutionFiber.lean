import PPAC.Migration.Internal.PacketTokenExecutionSyntax

/-! Typed actual output fibers exist uniquely for arbitrary internal natural inputs and tails. -/
namespace PPAC.Migration.Internal.PacketTokenExecutionFiber
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenAcceptedSyntax PacketTokenExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem unique_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (uniqueAt w n t a) := by
  apply Derives.allI
  apply Derives.impI
  let H := accepted w.castSucc n.castSucc t.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB H)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC H)
  have ha1 := of_eq (accepted_rename w n t a Fin.castSucc) (under ha H)
  exact PacketTokenUniqueInduction.unique (ZFContext.under hZ H) w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc
    (Fin.last m) a.castSucc hw1 hB1 hC1 (.hyp (Or.inl rfl)) ha1

theorem exists_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hn : Derives Γ (.mem n w)) (ht : Derives Γ (.mem t w)) : Derives Γ (fiber w n t) := by
  have he := PacketTokenExistenceInduction.exists_output hZ w B C n t hw hB hC hn ht
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (accepted w.castSucc n.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hC1 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C Fin.castSucc) (under hC R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hu := unique_at hZ1 w.castSucc B.castSucc C.castSucc n.castSucc t.castSucc (Fin.last m) hw1 hB1 hC1 (.conjR hR)
  exact of_eq (fiber_rename w n t Fin.castSucc).symm (intro_fiber w.castSucc n.castSucc t.castSucc (Fin.last m) (.conjL hR) (.conjR hR) hu)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (fiber w n t)) : Derives Γ ((Formula.mem n w).conj (.mem t w)) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj ((accepted w.castSucc n.castSucc t.castSucc (Fin.last m)).conj
    (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m)))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hf
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := PacketTokenAcceptedNatural.accepted_environment (ZFContext.under hZ R) w.castSucc n.castSucc t.castSucc (Fin.last m) hw1 (.conjL (.conjR hR))
  exact .conjI (HornExprSyntax.environmentNat_at w.castSucc (SyntaxAtomSyntax.three n.castSucc t.castSucc (Fin.last m)) he 0)
    (HornExprSyntax.environmentNat_at w.castSucc (SyntaxAtomSyntax.three n.castSucc t.castSucc (Fin.last m)) he 1)

theorem fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ ((fiber w n t).iff ((Formula.mem n w).conj (.mem t w))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact range (ZFContext.add hZ _) w n t (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hi : Derives (Context.add ((Formula.mem n w).conj (.mem t w)) Γ) ((Formula.mem n w).conj (.mem t w)) := .hyp (Or.inl rfl)
    exact exists_fiber (ZFContext.add hZ _) w B C n t (add hw _) (add hB _) (add hC _) (.conjL hi) (.conjR hi)

end PPAC.Migration.Internal.PacketTokenExecutionFiber
