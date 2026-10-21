import PPAC.Migration.OmegaStructureInduction
import PPAC.Migration.ObjectIrreflexivity

/-! 对象后继的非空、消去与ω成员闭包；不存在宿主Nat索引。 -/
namespace PPAC.Migration.OmegaStructureAlgebra
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax RestrictionSyntax

theorem zero_member {m} {Γ : Context m} (w z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (.mem z w) :=
  OmegaUniversal.empty_member z w he hz (.conjL hw)

theorem successor_member {m} {Γ : Context m} (w s x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hs : Derives Γ (successor s x)) :
    Derives Γ (.mem s w) := OmegaUniversal.successor_member s x w he hs (.conjL hw) hx

theorem successor_not_empty {m} {Γ : Context m} (s x : Fin m) (hs : Derives Γ (successor s x)) :
    Derives Γ (empty s).neg := by
  apply Derives.impI
  exact .impE (empty_at s x (.hyp (Or.inl rfl))) (InsertLogic.new_member s x x (add hs _))

theorem decomposition_at {m} {Γ : Context m} (w x : Fin m)
    (hd : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (split w.castSucc (Fin.last m)))))
    (hx : Derives Γ (.mem x w)) : Derives Γ (split w x) := by
  have hi := Derives.allE x hd
  have hr : Derives Γ ((Formula.mem x w).imp (split w x)) := by
    simpa only [Formula.instantiate, Formula.rename, split_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE hr hx

theorem nonzero_predecessor {m} {Γ : Context m} (w x : Fin m)
    (hd : Derives Γ (split w x)) (hn : Derives Γ (empty x).neg) : Derives Γ (predecessor w x) := by
  apply Derives.disjE hd
  · exact .botE (.impE (add hn _) (.hyp (Or.inl rfl)))
  · exact .hyp (Or.inl rfl)

theorem element_transitive_at {m} {Γ : Context m} (w x : Fin m)
    (ht : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (transitive (Fin.last m)))))
    (hx : Derives Γ (.mem x w)) : Derives Γ (transitive x) := by
  have hi := Derives.allE x ht
  have hr : Derives Γ ((Formula.mem x w).imp (transitive x)) := by
    simpa only [Formula.instantiate, Formula.rename, transitive_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE hr hx

/-- 同一后继的前驱在传递/不自属条件下可消去，完全在对象成员推导中。 -/
theorem successor_injective {m} {Γ : Context m} (s x y : Fin m)
    (hx : Derives Γ (transitive x)) (hn : Derives Γ (Formula.mem x x).neg)
    (hs : Derives Γ (successor s x)) (ht : Derives Γ (successor s y)) : Derives Γ (.equal x y) := by
  have hc := InsertLogic.member_cases s y y x ht (InsertLogic.new_member s x x hs)
  apply Derives.disjE hc
  · have hc' := InsertLogic.member_cases s x x y (add hs (.mem x y)) (InsertLogic.new_member s y y (add ht (.mem x y)))
    apply Derives.disjE hc'
    · have hb : Derives (Context.add (.mem y x) (Context.add (.mem x y) Γ)) (subset y x) :=
        .impE (add (add (transitive_at x y hx) _) _) (.hyp (Or.inl rfl))
      have hxx : Derives (Context.add (.mem y x) (Context.add (.mem x y) Γ)) (.mem x x) :=
        .impE (subset_at y x x hb) (.hyp (Or.inr (Or.inl rfl)))
      exact .botE (.impE (add (add hn _) _) hxx)
    · exact eq_symm (.hyp (Or.inl rfl))
  · exact .hyp (Or.inl rfl)
end PPAC.Migration.OmegaStructureAlgebra
