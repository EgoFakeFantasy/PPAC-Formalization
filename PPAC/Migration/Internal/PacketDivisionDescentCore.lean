import PPAC.Migration.Internal.PacketDivisionDescentOrder

/-! Exact quotient descent and radix stopping conditions for all internal affine witnesses. -/
namespace PPAC.Migration.Internal.PacketDivisionDescentCore
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem quotient_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (affine w B d q n)) : Derives Γ ((below q n).conj ((empty q).neg.imp (.mem q n))) := by
  let P := equationBody w B d q n
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (equation_of_affine w B d q n ha)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB P)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hpq := PacketDivisionDescentOrder.product_bounds hZ1 wide w.castSucc B.castSucc q.castSucc (Fin.last m)
    hw1 hB1 (tail_guard _ _ _ _ _ ha1) (.conjL hP)
  have hpn := PacketDivisionBand.lower hZ1 w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc (Fin.last m) hw1 ha1 (.conjL hP)
  have hb := NaturalOrderBasic.transitive hZ1 w.castSucc q.castSucc (Fin.last m) n.castSucc hw1 (output_guard _ _ _ _ _ ha1) (.conjL hpq) hpn
  have hs : Derives Δ ((empty q.castSucc).neg.imp (.mem q.castSucc n.castSucc)) := by
    apply Derives.impI
    exact PacketDivisionDescentOrder.member_below (ZFContext.add hZ1 _) w.castSucc q.castSucc (Fin.last m) n.castSucc
      (add hw1 _) (add (output_guard _ _ _ _ _ ha1) _) (.impE (add (.conjR hpq) _) (.hyp (Or.inl rfl))) (add hpn _)
  exact of_eq (by simp only [Formula.raise, Formula.rename, Formula.neg, below_rename, empty_rename]) (.conjI hb hs)

theorem quotient_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (affine w B d q n)) : Derives Γ (below q n) := .conjL (quotient_bounds hZ wide w B d q n hw hB ha)

theorem quotient_strict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (affine w B d q n)) (hn : Derives Γ (empty n).neg) : Derives Γ (.mem q n) := by
  have hb := quotient_bounds hZ wide w B d q n hw hB ha
  apply SourcePropositional.by_cases (empty q) (.mem q n)
  · apply Derives.disjE (add (.conjL hb) _)
    · have he : Derives (Context.add (Formula.equal q n) (Context.add (empty q) Γ)) (.equal q n) := .hyp (Or.inl rfl)
      have hz := NaturalMultiplicationLaws.empty_subst q n he (Derives.hyp (Γ := Context.add (Formula.equal q n) (Context.add (empty q) Γ)) (Or.inr (Or.inl rfl)))
      exact .botE (.impE (add (add hn _) _) hz)
    · exact .hyp (Or.inl rfl)
  · exact .impE (add (.conjR hb) _) (.hyp (Or.inl rfl))

theorem terminal_digit {m} {Γ : Context m} (w B d q n : Fin m)
    (ha : Derives Γ (affine w B d q n)) (hq : Derives Γ (empty q)) : Derives Γ (.equal n d) :=
  PacketAffineZero.equation_zero w B d q n hq (equation_of_affine w B d q n ha)

theorem terminal_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) : Derives Γ ((empty q).iff (.mem n B)) := by
  apply Derives.conjI
  · apply Derives.impI
    have he := terminal_digit w B d q n (add ha _) (.hyp (Or.inl rfl))
    exact mem_subst (eq_symm he) (add (digit_guard _ _ _ _ _ ha) _)
  · apply Derives.impI
    let H := Formula.mem n B
    let ΓH := Context.add H Γ
    let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Δ := Context.add Z (Context.image Formula.raise ΓH)
    apply Derives.exE (p := Z) (add (SyntaxNumerals.exists_numeral hZ 0 w hw) H)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) Z
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) Z)
    have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under (add ha H) Z)
    have hV : Derives Δ Z := .hyp (Or.inl rfl)
    have hnB : Derives Δ (.mem n.castSucc B.castSucc) := under (Derives.hyp (Γ := ΓH) (Or.inl rfl)) Z
    have hA := Derives.impE (.conjR (PacketAffineZero.zero_iff hZ1 w.castSucc B.castSucc n.castSucc (Fin.last m) n.castSucc
      hw1 (radix_guard _ _ _ _ _ ha1) (.conjR hV))) (.conjI hnB (.eqRefl _))
    have he := Derives.conjR (PacketDivisionUnique.unique hZ1 w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc (Fin.last m) n.castSucc hw1 ha1 hA)
    exact of_eq (empty_rename q Fin.castSucc).symm (NaturalMultiplicationLaws.empty_subst (Fin.last m) q.castSucc (eq_symm he) (.conjR hV))

theorem zero_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (ha : Derives Γ (affine w B d q n)) : Derives Γ ((empty n).iff ((empty d).conj (empty q))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hq := NaturalAdditionOrderLaws.empty_below q n (add (quotient_below hZ wide w B d q n hw hB ha) _) (.hyp (Or.inl rfl))
    have he := terminal_digit w B d q n (add ha _) hq
    exact .conjI (NaturalMultiplicationLaws.empty_subst n d he (.hyp (Or.inl rfl))) hq
  · apply Derives.impI
    have hc : Derives (Context.add ((empty d).conj (empty q)) Γ) ((empty d).conj (empty q)) := .hyp (Or.inl rfl)
    have he := terminal_digit w B d q n (add ha _) (.conjR hc)
    exact NaturalMultiplicationLaws.empty_subst d n (eq_symm he) (.conjL hc)

end PPAC.Migration.Internal.PacketDivisionDescentCore
