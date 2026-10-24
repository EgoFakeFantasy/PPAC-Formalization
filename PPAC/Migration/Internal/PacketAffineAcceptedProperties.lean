import PPAC.Migration.Internal.PacketAffineAccepted

/-! The actual relational affine run has a unique output on its full internal domain and rejects invalid data. -/
namespace PPAC.Migration.Internal.PacketAffineAcceptedProperties
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

def existsValue {m} (wide : Bool) (w d t : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (accepted wide w.castSucc d.castSucc t.castSucc (Fin.last m)))

theorem existsValue_rename {m j} (wide : Bool) (w d t : Fin m) (ρ : Fin m → Fin j) :
    (existsValue wide w d t).rename ρ = existsValue wide (ρ w) (ρ d) (ρ t) := by
  simp only [existsValue, Formula.rename, accepted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hd : Derives Γ (.mem d B)) (ht : Derives Γ (.mem t w)) : Derives Γ (existsValue wide w d t) := by
  have hBN := SyntaxNumerals.range hZ (PacketAffineRuleData.radix wide) w B hw hB
  have he := PacketAffineCore.exists_value hZ w B d t hw hBN hd ht
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (PacketAffineSyntax.affine w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ha := Derives.impE (.conjR (PacketAffineAccepted.accepted_iff (ZFContext.under hZ P) wide w.castSucc B.castSucc d.castSucc t.castSucc (Fin.last m) hw1 hB1)) (.conjR hP)
  have ho : Derives Δ (existsValue wide w.castSucc d.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, accepted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hP) ha)
  exact of_eq (existsValue_rename wide w d t Fin.castSucc).symm ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n a : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hn : Derives Γ (accepted wide w d t n)) (ha : Derives Γ (accepted wide w d t a)) : Derives Γ (.equal n a) :=
  PacketAffineCore.unique hZ w B d t n a hw
    (.impE (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d t n hw hB)) hn)
    (.impE (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d t a hw hB)) ha)

theorem reject_digit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hd : Derives Γ ((Formula.mem d B).neg)) : Derives Γ ((accepted wide w d t n).neg) := by
  apply Derives.impI
  have ha := Derives.impE (add (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d t n hw hB)) _) (.hyp (Or.inl rfl))
  exact .impE (add hd _) (PacketAffineCore.digit_guard w B d t n ha)

theorem reject_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ht : Derives Γ ((Formula.mem t w).neg)) : Derives Γ ((accepted wide w d t n).neg) := by
  apply Derives.impI
  have ha := Derives.impE (add (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d t n hw hB)) _) (.hyp (Or.inl rfl))
  exact .impE (add ht _) (PacketAffineCore.tail_guard w B d t n ha)

theorem reject_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hn : Derives Γ ((Formula.mem n w).neg)) : Derives Γ ((accepted wide w d t n).neg) := by
  apply Derives.impI
  have ha := Derives.impE (add (.conjL (PacketAffineAccepted.accepted_iff hZ wide w B d t n hw hB)) _) (.hyp (Or.inl rfl))
  exact .impE (add hn _) (PacketAffineCore.output_guard w B d t n ha)

end PPAC.Migration.Internal.PacketAffineAcceptedProperties
