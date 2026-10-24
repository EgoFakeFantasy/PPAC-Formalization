import PPAC.Migration.Internal.ObjectPacketDivision

/-! Bounds use actual internal unit witnesses and original multiplication order. -/
namespace PPAC.Migration.Internal.PacketDivisionDescentOrder
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem one_product {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a e : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (he : Derives Γ (SyntaxNumeralSyntax.numeral 1 e)) :
    Derives Γ (product w e a a) := by
  let Z := (OmegaSyntax.empty (Fin.last m)).conj (successor e.castSucc (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ 0 e _ he
  have hZ1 := ZFContext.under hZ Z
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hV : Derives Δ Z := .hyp (Or.inl rfl)
  have hzN := OmegaStructureAlgebra.zero_member w.castSucc (Fin.last m) (ZFContext.arithmetic hZ1).base.extensionality hw1 (.conjL hV)
  have heN := OmegaStructureAlgebra.successor_member w.castSucc e.castSucc (Fin.last m)
    (ZFContext.arithmetic hZ1).base.extensionality hw1 hzN (.conjR hV)
  have hu := NaturalMultiplicationAlgebraLaws.right_unit hZ1 w.castSucc a.castSucc (Fin.last m) e.castSucc hw1 (under ha Z) (.conjL hV) (.conjR hV)
  exact of_eq (product_rename w e a a Fin.castSucc).symm
    (NaturalMultiplicationCommutative.commute hZ1 w.castSucc a.castSucc e.castSucc a.castSucc hw1 (under ha Z) heN hu)

theorem member_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w)) (hab : Derives Γ (.mem a b))
    (hbc : Derives Γ (below b c)) : Derives Γ (.mem a c) := by
  apply Derives.disjE hbc
  · exact UnorderedPairLogic.mem_container_subst b c a (.hyp (Or.inl rfl)) (add hab _)
  · let H := Formula.mem b c
    let Δ := Context.add H Γ
    have ho : Derives Δ (OrdinalSyntax.ordinal c) := NaturalOrderBasic.ordinal (ZFContext.add hZ H) w c (add hw H) (add hc H)
    have ht := OrdinalSyntax.transitiveSet_at c b a (.conjL ho)
    exact .impE (.impE ht (.hyp (Or.inl rfl))) (add hab _)

theorem product_bounds_at_one {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B q p e : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hq : Derives Γ (.mem q w)) (he : Derives Γ (SyntaxNumeralSyntax.numeral 1 e))
    (hp : Derives Γ (product w B q p)) : Derives Γ ((below q p).conj ((empty q).neg.imp (.mem q p))) := by
  have hEN := SyntaxNumerals.range hZ 1 w e hw he
  have hBN := SyntaxNumerals.range hZ (PacketAffineRuleData.radix wide) w B hw hB
  have hEB := SyntaxNumerals.less hZ 1 (PacketAffineRuleData.radix wide) (by cases wide <;> decide) e B he hB
  have hu := one_product hZ w q e hw hq he
  apply Derives.conjI
  · exact NaturalMultiplicationMonotone.monotone hZ w e B q q p hw hEN hBN hq hu hp (.disjR hEB)
  · apply Derives.impI
    exact NaturalMultiplicationMonotone.strict_monotone (ZFContext.add hZ _) w e B q q p
      (add hw _) (add hEN _) (add hBN _) (add hq _) (.hyp (Or.inl rfl)) (add hu _) (add hp _) (add hEB _)

theorem product_bounds {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B q p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hq : Derives Γ (.mem q w)) (hp : Derives Γ (product w B q p)) :
    Derives Γ ((below q p).conj ((empty q).neg.imp (.mem q p))) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 1 (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxNumerals.exists_numeral hZ 1 w hw)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB E)
  have hp1 := of_eq (product_rename w B q p Fin.castSucc) (under hp E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact of_eq (by simp only [Formula.raise, Formula.rename, below_rename, Formula.neg, empty_rename])
    (product_bounds_at_one (ZFContext.under hZ E) wide w.castSucc B.castSucc q.castSucc p.castSucc (Fin.last m)
      hw1 hB1 (under hq E) (.conjR hE) hp1)

end PPAC.Migration.Internal.PacketDivisionDescentOrder
