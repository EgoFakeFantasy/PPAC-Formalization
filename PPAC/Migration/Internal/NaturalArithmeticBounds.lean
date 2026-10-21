import PPAC.Migration.Internal.NaturalMultiplicationOrderLaws

/-! 内部一、非零乘积的因子下界及平方界，供原配数编码复用。 -/
namespace PPAC.Migration.Internal.NaturalArithmeticBounds
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem add_zero_left {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) : Derives Γ (sum w z n n) := by
  have hall := NaturalAdditionZero.all_left_zero (ZFContext.arithmetic hZ) w z (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionZero.matrix) hw hz
  have hi : Derives Γ ((Formula.mem n w).imp (sum w z n n)) := by
    simpa only [Formula.instantiate, Formula.rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n hall
  exact .impE hi hn

theorem add_one {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z e s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (successor e z)) (hs : Derives Γ (successor s a)) : Derives Γ (sum w a e s) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  exact add_succ_backward hZ w a z e a s hw ha hzW he (add_zero hZ w a z hw ha hz) hs

theorem unit_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (.mem n w)) (hn0 : Derives Γ (empty n).neg) : Derives Γ (below e n) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have heW := OmegaStructureAlgebra.successor_member w e z (ZFContext.arithmetic hZ).base.extensionality hw hzW he
  have hd := OmegaStructureAlgebra.decomposition_at w n
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hn
  have ht := OmegaStructureAlgebra.nonzero_predecessor w n hd hn0
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (successor n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hz1 : Derives Ξ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz T
  have he1 : Derives Ξ (successor e.castSucc z.castSucc) := by simpa only [Formula.raise, successor_rename] using under he T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hze := add_zero_left hZ1 _ _ _ hw1 hz1 (under heW T)
  have htn := add_one hZ1 _ _ _ _ _ hw1 (.conjL hT) hz1 he1 (.conjR hT)
  have hzt := add_zero_left hZ1 _ _ _ hw1 hz1 (.conjL hT)
  have hlo := NaturalAdditionBounds.lower_bound (ZFContext.arithmetic hZ1) _ _ _ _ (ZFContext.recAdd hZ1)
    (ZFContext.separation hZ1 NaturalAdditionBounds.matrix) hw1 (under hzW T) (.conjL hT) hzt
  have hout := NaturalAdditionMonotone.monotone hZ1 _ _ _ _ _ _ hw1 (under hzW T) (.conjL hT) (under heW T) hze htn hlo
  simpa only [Formula.raise, below_rename] using hout

theorem unit_bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hn : Derives Γ (.mem n w)) :
    Derives Γ ((empty n).neg.iff (below e n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact unit_bound (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hz _) (add he _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    apply Derives.impI
    let Δ := Context.add (empty n) (Context.add (below e n) Γ)
    have hl : Derives Δ (below e n) := .hyp (Or.inr (Or.inl rfl))
    have hn0 : Derives Δ (empty n) := .hyp (Or.inl rfl)
    have he0 := NaturalAdditionOrderLaws.empty_below e n hl hn0
    exact .impE (add (add (OmegaStructureAlgebra.successor_not_empty e z he) _) _) he0

theorem factor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p z e : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (hn0 : Derives Γ (empty n).neg)
    (hp : Derives Γ (product w a n p)) : Derives Γ (below a p) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have heW := OmegaStructureAlgebra.successor_member w e z (ZFContext.arithmetic hZ).base.extensionality hw hzW he
  have hle := unit_bound hZ w z e n hw hz he hn hn0
  have hu := NaturalMultiplicationAlgebraLaws.right_unit hZ w a z e hw ha hz he
  exact NaturalMultiplicationOrderLaws.left_monotone hZ w e n a a p hw heW hn ha hu hp hle

theorem factor_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hp : Derives Γ (product w a n p)) : Derives Γ (below a p) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Z
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hZero : Derives Ξ Z := .hyp (Or.inl rfl)
  have he := Derives.impE (step_at w.castSucc (Fin.last m) (.conjL hw1)) (.conjL hZero)
  let E := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add E (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 E
  have hn02 : Derives Δ (empty n.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using under (under hn0 Z) E
  have hp2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc p.castSucc.castSucc) := by
    simpa only [Formula.raise, product_rename] using under (under hp Z) E
  have hZero2 : Derives Δ Z.raise := under hZero E
  have hz2 : Derives Δ (empty (Fin.last m).castSucc) := by
    simpa only [Z, Formula.raise, Formula.rename, empty_rename] using Derives.conjR hZero2
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout := factor_point hZ2 _ _ _ _ _ _ hw2 (under (under ha Z) E) (under (under hn Z) E) hz2 (.conjR hE) hn02 hp2
  simpa only [Formula.raise, below_rename] using hout

theorem other_factor_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (ha0 : Derives Γ (empty a).neg) (hp : Derives Γ (product w a n p)) : Derives Γ (below n p) :=
  factor_bound hZ w n a p hw hn ha ha0 (NaturalMultiplicationCommutative.commute hZ w a n p hw ha hn hp)

theorem square_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hp : Derives Γ (product w a a p)) : Derives Γ (below a p) := by
  apply SourcePropositional.by_cases (empty a) (below a p)
  · let E := empty a
    let Δ := Context.add E Γ
    have hZ1 : ZFContext.Evidence Δ := ZFContext.add hZ E
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hp0 := NaturalMultiplicationLaws.zero_forward w a a p hE (add hp E)
    exact .disjL (OmegaUniversal.empty_unique a p (ZFContext.arithmetic hZ1).base.extensionality hE hp0)
  · exact factor_bound (ZFContext.add hZ _) _ _ _ _ (add hw _) (add ha _) (add ha _) (.hyp (Or.inl rfl)) (add hp _)

theorem below_mem_trans {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w)) (hab : Derives Γ (below a b)) (hbc : Derives Γ (.mem b c)) :
    Derives Γ (.mem a c) := by
  have ht := OrdinalSyntax.transitiveSet_at c b a (.conjL (NaturalOrderBasic.ordinal hZ w c hw hc))
  apply Derives.disjE hab
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (add hbc _)
  · exact .impE (.impE (add ht _) (add hbc _)) (.hyp (Or.inl rfl))

theorem square_strict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (product w a a p)) (hq : Derives Γ (product w b b q)) (hab : Derives Γ (.mem a b)) : Derives Γ (.mem p q) := by
  have hr := mul_exists hZ w a b hw ha hb
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc b.castSucc (Fin.last m))
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hr
  apply Derives.exE (p := R) hr
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hp1 : Derives Ξ (product w.castSucc a.castSucc a.castSucc p.castSucc) := by simpa only [Formula.raise, product_rename] using under hp R
  have hq1 : Derives Ξ (product w.castSucc b.castSucc b.castSucc q.castSucc) := by simpa only [Formula.raise, product_rename] using under hq R
  have hab1 : Derives Ξ (.mem a.castSucc b.castSucc) := under hab R
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hpr := NaturalMultiplicationOrderLaws.left_monotone hZ1 _ _ _ _ _ _ hw1 (under ha R) (under hb R) (under ha R) hp1 (.conjR hR) (.disjR hab1)
  have hb0 : Derives Ξ (empty b.castSucc).neg := by
    apply Derives.impI
    exact .impE (empty_at b.castSucc a.castSucc (.hyp (Or.inl rfl))) (add hab1 _)
  have hrq := NaturalMultiplicationMonotone.strict_monotone hZ1 _ _ _ _ _ _ hw1 (under ha R) (under hb R) (under hb R) hb0 (.conjR hR) hq1 hab1
  have hqW := mul_range hZ1 _ _ _ _ hw1 hq1
  exact below_mem_trans hZ1 _ _ _ _ hw1 hqW hpr hrq

theorem square_injective {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (product w a a p)) (hq : Derives Γ (product w b b p)) : Derives Γ (.equal a b) := by
  apply Derives.disjE (NaturalOrderBasic.compare hZ w a b hw ha hb)
  · exact .hyp (Or.inl rfl)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · let C := (Formula.mem a b).disj (.mem b a)
      let Δ := Context.add (Formula.mem a b) (Context.add C Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ C) _
      have hbad := square_strict hZ2 w a b p p (add (add hw C) _) (add (add ha C) _) (add (add hb C) _) (add (add hp C) _) (add (add hq C) _) (.hyp (Or.inl rfl))
      exact .botE (.impE (NaturalOrderBasic.nonself hZ2 p) hbad)
    · let C := (Formula.mem a b).disj (.mem b a)
      let Δ := Context.add (Formula.mem b a) (Context.add C Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ C) _
      have hbad := square_strict hZ2 w b a p p (add (add hw C) _) (add (add hb C) _) (add (add ha C) _) (add (add hq C) _) (add (add hp C) _) (.hyp (Or.inl rfl))
      exact .botE (.impE (NaturalOrderBasic.nonself hZ2 p) hbad)
end PPAC.Migration.Internal.NaturalArithmeticBounds
