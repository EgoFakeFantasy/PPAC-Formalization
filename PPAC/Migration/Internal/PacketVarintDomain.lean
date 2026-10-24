import PPAC.Migration.Internal.PacketVarintSyntax

/-! Actual graph domains, radix alignment and empty-list rejection hold for arbitrary internal candidates. -/
namespace PPAC.Migration.Internal.PacketVarintDomain
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_domain {m} {Γ : Context m} (w B n s : Fin m) (hc : Derives Γ (canonicalAt w B n s)) :
    Derives Γ ((Formula.mem n w).conj ((StructuralListTraceSyntax.valid w s).conj (StructuralListSyntax.nilCode w s).neg)) := by
  let R := (empty (Fin.last m)).conj ((PacketVarintTraceSyntax.foldAt w.castSucc B.castSucc s.castSucc (Fin.last m) n.castSucc).conj
    (StructuralListSyntax.nilCode w.castSucc s.castSucc).neg)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hd := PacketVarintTraceBase.domain w.castSucc B.castSucc s.castSucc (Fin.last m) n.castSucc (.conjL (.conjR hR))
  have hout := Derives.conjI (.conjR (.conjR hd)) (.conjI (.conjL hd) (.conjR (.conjR hR)))
  simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListTraceSyntax.valid_rename,StructuralListSyntax.nilCode_rename] using hout

theorem domain {m} {Γ : Context m} (w n s : Fin m) (hc : Derives Γ (canonical w n s)) :
    Derives Γ ((Formula.mem n w).conj ((StructuralListTraceSyntax.valid w s).conj (StructuralListSyntax.nilCode w s).neg)) := by
  let R := (SyntaxNumeralSyntax.numeral 128 (Fin.last m)).conj (canonicalAt w.castSucc (Fin.last m) n.castSucc s.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,Formula.neg,Formula.rename,StructuralListTraceSyntax.valid_rename,StructuralListSyntax.nilCode_rename] using at_domain w.castSucc (Fin.last m) n.castSucc s.castSucc (.conjR hR)

theorem radix_subst {m} {Γ : Context m} (w B n s C : Fin m) (he : Derives Γ (.equal B C))
    (hc : Derives Γ (canonicalAt w B n s)) : Derives Γ (canonicalAt w C n s) := by
  let P := canonicalAt w.castSucc (Fin.last m) n.castSucc s.castSucc
  have h0 : P.instantiate B = canonicalAt w B n s := by simp only [P,Formula.instantiate,canonicalAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate C = canonicalAt w C n s := by simp only [P,Formula.instantiate,canonicalAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem at_radix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m)
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hc : Derives Γ (canonical w n s)) : Derives Γ (canonicalAt w B n s) := by
  let R := (SyntaxNumeralSyntax.numeral 128 (Fin.last m)).conj (canonicalAt w.castSucc (Fin.last m) n.castSucc s.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hc
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := SyntaxNumerals.unique (ZFContext.under hZ R) 128 (Fin.last m) B.castSucc (.conjL hR) hB1
  simpa only [Formula.raise,canonicalAt_rename] using radix_subst _ _ _ _ _ he (.conjR hR)

theorem actual_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B n s : Fin m) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) :
    Derives Γ ((canonical w n s).iff (canonicalAt w B n s)) :=
  .conjI (.impI (at_radix (ZFContext.add hZ _) w B n s (add hB _) (.hyp (Or.inl rfl))))
    (.impI (intro_actual w B n s (add hB _) (.hyp (Or.inl rfl))))

theorem reject_nil {m} {Γ : Context m} (w n s : Fin m) (hs : Derives Γ (StructuralListSyntax.nilCode w s)) : Derives Γ (canonical w n s).neg := by
  apply Derives.impI
  exact .impE (.conjR (.conjR (domain w n s (.hyp (Or.inl rfl))))) (add hs _)

end PPAC.Migration.Internal.PacketVarintDomain
