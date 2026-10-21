import PPAC.Migration.OmegaSyntax

/-! 空元与后继在每个归纳集合中；全部存在见证保留在对象推导内。 -/
namespace PPAC.Migration.OmegaUniversal
open Source SourceAlgebra SourceLogic PairSyntax OmegaSyntax

theorem empty_unique {m} {Γ : Context m} (z t : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (ht : Derives Γ (empty t)) : Derives Γ (.equal z t) := by
  apply Derives.impE (extensionality_instance z t he)
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  have ht' : Derives (Context.image Formula.raise Γ) (empty t.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc ht
  apply Derives.conjI
  · apply Derives.impI
    exact .botE (.impE (add (empty_at z.castSucc (Fin.last m) hz') _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .botE (.impE (add (empty_at t.castSucc (Fin.last m) ht') _) (.hyp (Or.inl rfl)))

theorem successor_unique {m} {Γ : Context m} (s t x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ (successor s x)) (ht : Derives Γ (successor t x)) : Derives Γ (.equal s t) :=
  InsertLogic.unique s t x x he hs ht

theorem empty_member {m} {Γ : Context m} (z i : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hi : Derives Γ (isInductive i)) : Derives Γ (.mem z i) := by
  have hzero := Derives.conjL hi
  let Z := (Formula.mem (Fin.last m) i.castSucc).conj (empty (Fin.last m))
  let Γz := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hzero
  apply Derives.exE (p := Z) hzero
  have heZ : Derives Γz (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Z
  have hzZ : Derives Γz (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hz Z
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  exact mem_subst (eq_symm (empty_unique z.castSucc (Fin.last m) heZ hzZ (.conjR hZ))) (.conjL hZ)

theorem empty_universal {m} {Γ : Context m} (z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hz : Derives Γ (empty z)) :
    Derives Γ (universal z) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact empty_member z.castSucc (Fin.last m) (add he' _) (add hz' _) (.hyp (Or.inl rfl))

theorem successor_member {m} {Γ : Context m} (s x i : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ (successor s x)) (hi : Derives Γ (isInductive i)) (hx : Derives Γ (.mem x i)) :
    Derives Γ (.mem s i) := by
  have hstep := Derives.impE (step_at i x hi) hx
  let T := (Formula.mem (Fin.last m) i.castSucc).conj (successor (Fin.last m) x.castSucc)
  let Γt := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hstep
  apply Derives.exE (p := T) hstep
  have heT : Derives Γt (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he T
  have hsT : Derives Γt (successor s.castSucc x.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs T
  have hT : Derives Γt T := .hyp (Or.inl rfl)
  exact mem_subst (eq_symm (successor_unique s.castSucc (Fin.last m) x.castSucc heT hsT (.conjR hT))) (.conjL hT)

theorem successor_universal {m} {Γ : Context m} (s x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ (successor s x)) (hx : Derives Γ (universal x)) : Derives Γ (universal s) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hs' : Derives (Context.image Formula.raise Γ) (successor s.castSucc x.castSucc) := by
    simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hs
  have hx' : Derives (Context.image Formula.raise Γ) (universal x.castSucc) := by
    simpa only [Formula.raise, universal_rename] using Derives.rename Fin.castSucc hx
  apply Derives.impI
  let I := isInductive (Fin.last m)
  exact successor_member s.castSucc x.castSucc (Fin.last m) (add he' I) (add hs' I) (.hyp (Or.inl rfl))
    (.impE (universal_at x.castSucc (Fin.last m) (add hx' I)) (.hyp (Or.inl rfl)))
end PPAC.Migration.OmegaUniversal
