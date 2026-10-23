import PPAC.Migration.Internal.PureSyntaxTraceRules
import PPAC.Migration.InsertExistence

/-! 对象Pairing／Union构造二元并集；不抽取宿主集合或选择函数。 -/
namespace PPAC.Migration.Internal.BinaryUnionSyntax
open Source SourceAlgebra SourceLogic PairSyntax InsertSyntax
open SyntaxRenameQuerySyntax (of_eq)

def joined {m} (U R S : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) U.castSucc).iff
    ((Formula.mem (Fin.last m) R.castSucc).disj (.mem (Fin.last m) S.castSucc)))

def exists_join {m} (R S : Fin m) : Formula m := .ex (joined (Fin.last m) R.castSucc S.castSucc)

theorem joined_rename {m n} (U R S : Fin m) (ρ : Fin m → Fin n) :
    (joined U R S).rename ρ = joined (ρ U) (ρ R) (ρ S) := by
  simp only [joined, Formula.iff, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem exists_join_rename {m n} (R S : Fin m) (ρ : Fin m → Fin n) :
    (exists_join R S).rename ρ = exists_join (ρ R) (ρ S) := by
  simp only [exists_join, Formula.rename, joined_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem at_point {m} {Γ : Context m} (U R S z : Fin m) (hu : Derives Γ (joined U R S)) :
    Derives Γ ((Formula.mem z U).iff ((Formula.mem z R).disj (.mem z S))) := by
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE z hu)

theorem member_cases {m} {Γ : Context m} (U R S z : Fin m)
    (hu : Derives Γ (joined U R S)) (hz : Derives Γ (.mem z U)) :
    Derives Γ ((Formula.mem z R).disj (.mem z S)) := .impE (.conjL (at_point U R S z hu)) hz

theorem member_left {m} {Γ : Context m} (U R S z : Fin m)
    (hu : Derives Γ (joined U R S)) (hz : Derives Γ (.mem z R)) : Derives Γ (.mem z U) :=
  .impE (.conjR (at_point U R S z hu)) (.disjL hz)

theorem member_right {m} {Γ : Context m} (U R S z : Fin m)
    (hu : Derives Γ (joined U R S)) (hz : Derives Γ (.mem z S)) : Derives Γ (.mem z U) :=
  .impE (.conjR (at_point U R S z hu)) (.disjR hz)

theorem includes_left {m} {Γ : Context m} (U R S : Fin m) (hu : Derives Γ (joined U R S)) :
    Derives Γ (RestrictionSyntax.subset R U) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  have hu1 : Derives (Context.add M (Context.image Formula.raise Γ)) (joined U.castSucc R.castSucc S.castSucc) :=
    of_eq (joined_rename U R S Fin.castSucc) (under hu M)
  exact member_left _ _ _ _ hu1 (.hyp (Or.inl rfl))

theorem includes_right {m} {Γ : Context m} (U R S : Fin m) (hu : Derives Γ (joined U R S)) :
    Derives Γ (RestrictionSyntax.subset S U) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) S.castSucc
  have hu1 : Derives (Context.add M (Context.image Formula.raise Γ)) (joined U.castSucc R.castSucc S.castSucc) :=
    of_eq (joined_rename U R S Fin.castSucc) (under hu M)
  exact member_right _ _ _ _ hu1 (.hyp (Or.inl rfl))

theorem subset {m} {Γ : Context m} (w U R S : Fin m)
    (hu : Derives Γ (joined U R S)) (hr : Derives Γ (RestrictionSyntax.subset R w))
    (hs : Derives Γ (RestrictionSyntax.subset S w)) : Derives Γ (RestrictionSyntax.subset U w) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) U.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hu1 : Derives Δ (joined U.castSucc R.castSucc S.castSucc) := of_eq (joined_rename U R S Fin.castSucc) (under hu M)
  have hr1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hr M)
  have hs1 : Derives Δ (RestrictionSyntax.subset S.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename S w Fin.castSucc) (under hs M)
  apply Derives.disjE (member_cases _ _ _ _ hu1 (.hyp (Or.inl rfl)))
  · exact .impE (add (RestrictionSyntax.subset_at _ _ _ hr1) _) (.hyp (Or.inl rfl))
  · exact .impE (add (RestrictionSyntax.subset_at _ _ _ hs1) _) (.hyp (Or.inl rfl))

theorem from_union_forward {m} {Γ : Context m} (U R S P z : Fin m)
    (hp : Derives Γ (pair P R S)) (hu : Derives Γ (unionOf U P)) (hz : Derives Γ (.mem z U)) :
    Derives Γ ((Formula.mem z R).disj (.mem z S)) := by
  let B := (Formula.mem (Fin.last m) P.castSucc).conj (.mem z.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.impE (.conjL (union_at U P z hu)) hz)
  have hp1 : Derives Δ (pair P.castSucc R.castSucc S.castSucc) := of_eq (pair_rename P R S Fin.castSucc) (under hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  apply Derives.disjE (UnorderedPairLogic.member_cases _ _ _ _ hp1 (.conjL hB))
  · exact .disjL (UnorderedPairLogic.mem_container_subst _ _ _ (.hyp (Or.inl rfl)) (add (.conjR hB) _))
  · exact .disjR (UnorderedPairLogic.mem_container_subst _ _ _ (.hyp (Or.inl rfl)) (add (.conjR hB) _))

theorem from_pair_union {m} {Γ : Context m} (U R S P : Fin m)
    (hp : Derives Γ (pair P R S)) (hu : Derives Γ (unionOf U P)) : Derives Γ (joined U R S) := by
  apply Derives.allI
  have hp1 : Derives (Context.image Formula.raise Γ) (pair P.castSucc R.castSucc S.castSucc) := of_eq (pair_rename P R S Fin.castSucc) (Derives.rename Fin.castSucc hp)
  have hu1 : Derives (Context.image Formula.raise Γ) (unionOf U.castSucc P.castSucc) := of_eq (unionOf_rename U P Fin.castSucc) (Derives.rename Fin.castSucc hu)
  apply Derives.conjI
  · apply Derives.impI
    exact from_union_forward _ _ _ _ _ (add hp1 _) (add hu1 _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .impE (.conjR (add (add (union_at _ _ (Fin.last m) hu1) _) _))
        (InsertLogic.fiber_intro _ _ R.castSucc (UnorderedPairLogic.member_left _ _ _ (add (add hp1 _) _)) (.hyp (Or.inl rfl)))
    · exact .impE (.conjR (add (add (union_at _ _ (Fin.last m) hu1) _) _))
        (InsertLogic.fiber_intro _ _ S.castSucc (UnorderedPairLogic.member_right _ _ _ (add (add hp1 _) _)) (.hyp (Or.inl rfl)))

theorem exists_joined {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R S : Fin m) : Derives Γ (exists_join R S) := by
  let P := pair (Fin.last m) R.castSucc S.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (pairing_instance R S (ZFContext.arithmetic hZ).base.pairing)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  let U := unionOf (Fin.last (m+1)) (Fin.last m).castSucc
  let Ξ := Context.add U (Context.image Formula.raise Δ)
  apply Derives.exE (p := U) (union_instance (Fin.last m) (ZFContext.arithmetic (ZFContext.under hZ P)).base.union)
  have hp1 : Derives Ξ (pair (Fin.last m).castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (pair_rename _ _ _ Fin.castSucc) (under hP U)
  have hu : Derives Ξ U := .hyp (Or.inl rfl)
  have hj := from_pair_union (Fin.last (m+1)) R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc hp1 hu
  have he : Derives Ξ (exists_join R.castSucc.castSucc S.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, joined_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hj
  exact of_eq (by simp only [Formula.raise, exists_join_rename]) he

end PPAC.Migration.Internal.BinaryUnionSyntax
