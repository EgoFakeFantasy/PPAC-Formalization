import PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra

/-! 内部自然顺序始终为原相等/成员析取，不使用宿主Nat比较。 -/
namespace PPAC.Migration.Internal.NaturalOrderBasic
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionBounds (below below_rename)

theorem ordinal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (OrdinalSyntax.ordinal a) :=
  OmegaOrdinals.at_member w a (OmegaOrdinals.elements w (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.arithmetic hZ).ordinalSeparation hw) ha

theorem nonself {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a : Fin m) : Derives Γ (Formula.mem a a).neg :=
  ObjectIrreflexivity.no_self_member a (ZFContext.arithmetic hZ).base.foundation (ZFContext.arithmetic hZ).base.pairing

theorem below_subst_left {m} {Γ : Context m} (a b c : Fin m) (he : Derives Γ (.equal a b))
    (hl : Derives Γ (below a c)) : Derives Γ (below b c) := by
  have hi : Derives Γ ((below (Fin.last m) c.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, below_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hl
  have ho := Derives.eqSubst (below (Fin.last m) c.castSucc) he hi
  simpa only [Formula.instantiate, below_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem below_subst_right {m} {Γ : Context m} (a b c : Fin m) (he : Derives Γ (.equal b c))
    (hl : Derives Γ (below a b)) : Derives Γ (below a c) := by
  have hi : Derives Γ ((below a.castSucc (Fin.last m)).instantiate b) := by
    simpa only [Formula.instantiate, below_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hl
  have ho := Derives.eqSubst (below a.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, below_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem member_successor {m} {Γ : Context m} (a b s : Fin m) (hs : Derives Γ (successor s b))
    (ha : Derives Γ (.mem a s)) : Derives Γ (below a b) := by
  have hc := InsertLogic.member_cases s b b a hs ha
  apply Derives.disjE hc
  · exact .disjR (.hyp (Or.inl rfl))
  · exact .disjL (.hyp (Or.inl rfl))

theorem below_successor {m} {Γ : Context m} (a b s : Fin m) (hs : Derives Γ (successor s b))
    (ha : Derives Γ (below a b)) : Derives Γ (.mem a s) := by
  apply Derives.disjE ha
  · exact mem_subst (eq_symm (.hyp (Or.inl rfl))) (InsertLogic.new_member s b b (add hs _))
  · exact InsertLogic.old_member s b b a (add hs _) (.hyp (Or.inl rfl))

theorem successor_iff {m} {Γ : Context m} (a b s : Fin m) (hs : Derives Γ (successor s b)) :
    Derives Γ ((Formula.mem a s).iff (below a b)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact member_successor a b s (add hs _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact below_successor a b s (add hs _) (.hyp (Or.inl rfl))

theorem below_not_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hl : Derives Γ (below a b))
    (hr : Derives Γ (.mem b a)) : Derives Γ .bot := by
  have ho := ordinal hZ w a hw ha
  have hno := nonself hZ a
  apply Derives.disjE hl
  · exact .impE (add hno _) (mem_subst (eq_symm (.hyp (Or.inl rfl))) (add hr _))
  · exact .impE (OrdinalComparison.asymmetric a b (add ho _) (.hyp (Or.inl rfl))) (add hr _)

theorem antisymmetric {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hl : Derives Γ (below a b))
    (hr : Derives Γ (below b a)) : Derives Γ (.equal a b) := by
  apply Derives.disjE hr
  · exact eq_symm (.hyp (Or.inl rfl))
  · exact .botE (below_not_reverse (ZFContext.add hZ _) w a b (add hw _) (add ha _) (add hl _) (.hyp (Or.inl rfl)))

theorem transitive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (.mem c w)) (hab : Derives Γ (below a b))
    (hbc : Derives Γ (below b c)) : Derives Γ (below a c) := by
  have ho := ordinal hZ w c hw hc
  apply Derives.disjE hab
  · exact below_subst_left b a c (eq_symm (.hyp (Or.inl rfl))) (add hbc _)
  · apply Derives.disjE (add hbc _)
    · exact .disjR (UnorderedPairLogic.mem_container_subst b c a (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl))))
    · let Δ := Context.add (Formula.mem b c) (Context.add (Formula.mem a b) Γ)
      have ho' : Derives Δ (OrdinalSyntax.ordinal c) := add (add ho _) _
      have ht := OrdinalSyntax.transitiveSet_at c b a (Derives.conjL ho')
      exact .disjR (.impE (.impE ht (.hyp (Or.inl rfl))) (.hyp (Or.inr (Or.inl rfl))))

theorem compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ (OrdinalComparison.comparison a b) :=
  OrdinalComparison.compare a b (ZFContext.arithmetic hZ).base.extensionality (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.separation hZ OrdinalDifference.outsideMatrix) (ordinal hZ w a hw ha) (ordinal hZ w b hw hb)

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ ((below a b).disj (below b a)) := by
  apply Derives.disjE (compare hZ w a b hw ha hb)
  · exact .disjL (.disjL (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.disjR (.hyp (Or.inl rfl)))
    · exact .disjR (.disjR (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.NaturalOrderBasic
