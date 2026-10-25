import PPAC.Migration.Internal.PacketReaderInitSeeded

/-! Align actual numeral and zero/one witnesses by original object equality; the fixed reader relation has no external literal parameters. -/
namespace PPAC.Migration.Internal.PacketReaderInitLiterals
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketReaderInitSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem seeded_B {m} {Γ : Context m} (w B z o L q C : Fin m) (he : Derives Γ (.equal B C))
    (hr : Derives Γ (seeded w B z o L q)) : Derives Γ (seeded w C z o L q) := by
  let P := seeded w.castSucc (Fin.last m) z.castSucc o.castSucc L.castSucc q.castSucc
  have h0 : P.instantiate B = seeded w B z o L q := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate C = seeded w C z o L q := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem seeded_z {m} {Γ : Context m} (w B z o L q t : Fin m) (he : Derives Γ (.equal z t))
    (hr : Derives Γ (seeded w B z o L q)) : Derives Γ (seeded w B t o L q) := by
  let P := seeded w.castSucc B.castSucc (Fin.last m) o.castSucc L.castSucc q.castSucc
  have h0 : P.instantiate z = seeded w B z o L q := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate t = seeded w B t o L q := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem seeded_o {m} {Γ : Context m} (w B z o L q e : Fin m) (he : Derives Γ (.equal o e))
    (hr : Derives Γ (seeded w B z o L q)) : Derives Γ (seeded w B z e L q) := by
  let P := seeded w.castSucc B.castSucc z.castSucc (Fin.last m) L.castSucc q.castSucc
  have h0 : P.instantiate o = seeded w B z o L q := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate e = seeded w B z e L q := by simp only [P,Formula.instantiate,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hr))

theorem at_literals {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L q : Fin m)
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z)) :
    Derives Γ ((parse w L q).iff (seeded w B z o L q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := parse w L q
    let R := parseBody w L q
    let Δ := Context.add R (raisedContext 3 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 3 R _ (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ3 := HornBinderRules.zf_body 3 (ZFContext.add hZ H) R
    have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_body 3 (add hB H) R)
    have hz3 := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 (add hz H) R)
    have ho3 := of_eq (successor_rename o z (old 3)) (HornBinderRules.under_body 3 (add ho H) R)
    have hBE := SyntaxNumerals.unique hZ3 128 (slot 3 0) (old 3 B) (.conjL hR) hB3
    have hZE := OmegaUniversal.empty_unique (slot 3 1) (old 3 z) (ZFContext.arithmetic hZ3).base.extensionality (.conjL (.conjR hR)) hz3
    have hOE := StructuralListUnits.unique hZ3 (slot 3 1) (slot 3 2) (old 3 z) (old 3 o) (.conjL (.conjR hR)) (.conjL (.conjR (.conjR hR))) hz3 ho3
    have h1 := seeded_B _ _ _ _ _ _ _ hBE (.conjR (.conjR (.conjR hR)))
    have h2 := seeded_z _ _ _ _ _ _ _ hZE h1
    exact of_eq (seeded_rename w B z o L q (old 3)).symm (seeded_o _ _ _ _ _ _ _ hOE h2)
  · apply Derives.impI
    exact intro_parse w L q B z o (add hB _) (add hz _) (add ho _) (.hyp (Or.inl rfl))

theorem from_seeded_exists {m} {Γ : Context m} (w B z o L : Fin m)
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hr : Derives Γ (existsSeeded w B z o L)) : Derives Γ (existsParse w L) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (seeded w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B Fin.castSucc) (under hB R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have ho1 := of_eq (successor_rename o z Fin.castSucc) (under ho R)
  have hp := intro_parse _ _ _ _ _ _ hB1 hz1 ho1 (.conjR hR)
  have hout : Derives Δ (existsParse w.castSucc L.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,parse_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjL hR) hp)
  simpa only [Formula.raise,existsParse_rename] using hout

end PPAC.Migration.Internal.PacketReaderInitLiterals
