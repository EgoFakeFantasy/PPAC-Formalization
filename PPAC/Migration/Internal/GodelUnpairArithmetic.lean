import PPAC.Migration.Internal.GodelUnpairSyntax

/-! 实际后继的替换与平方向前构造；全部输入均留在原对象算术关系。 -/
namespace PPAC.Migration.Internal.GodelUnpairArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairArithmetic
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z a : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ha : Derives Γ (.mem a w)) : Derives Γ (below z a) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  apply Derives.disjE (NaturalOrderBasic.compare hZ w z a hw hzW ha)
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (empty_at z a (add (add hz _) _)) (.hyp (Or.inl rfl)))

theorem not_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hab : Derives Γ (below a b)) : Derives Γ (Formula.mem b a).neg := by
  apply Derives.impI
  exact NaturalOrderBasic.below_not_reverse (ZFContext.add hZ _) w a b (add hw _) (add ha _) (add hab _) (.hyp (Or.inl rfl))

theorem successor_base_subst {m} {Γ : Context m} (s a b : Fin m) (he : Derives Γ (.equal a b))
    (hs : Derives Γ (successor s a)) : Derives Γ (successor s b) := by
  have hi : Derives Γ ((successor s.castSucc (Fin.last m)).instantiate a) := by
    simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hs
  have ho := Derives.eqSubst (successor s.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem upper_right_subst {m} {Γ : Context m} (w a b d p : Fin m) (he : Derives Γ (.equal b d))
    (hp : Derives Γ (GodelPairSyntax.upper w a b p)) : Derives Γ (GodelPairSyntax.upper w a d p) := by
  have hi : Derives Γ ((GodelPairSyntax.upper w.castSucc a.castSucc (Fin.last m) p.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, GodelPairSyntax.upper_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have ho := Derives.eqSubst (GodelPairSyntax.upper w.castSucc a.castSucc (Fin.last m) p.castSucc) he hi
  simpa only [Formula.instantiate, GodelPairSyntax.upper_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem square_advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a s q t p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hs : Derives Γ (successor s a))
    (hq : Derives Γ (product w a a q)) (ht : Derives Γ (sum w q a t)) (hp : Derives Γ (sum w t a p))
    (hr : Derives Γ (successor r p)) : Derives Γ (product w s s r) := by
  have hsW := OmegaStructureAlgebra.successor_member w s a (ZFContext.arithmetic hZ).base.extensionality hw ha hs
  have hqW := mul_range hZ _ _ _ _ hw hq
  have htW := add_range hZ _ _ _ _ hw hqW ht
  have hsa := NaturalMultiplicationShift.shift_at hZ w a s a q t hw ha hs ha hq ht
  have hts := add_succ_backward hZ w t a s p r hw htW ha hs hp hr
  exact mul_succ_backward hZ w s a s t r hw hsW ha hs hsa hts
end PPAC.Migration.Internal.GodelUnpairArithmetic
