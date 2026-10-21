import PPAC.Migration.PairSyntax

/-! 无序对的成员、外延唯一性及消去律，均只用原19源规则。 -/
namespace PPAC.Migration.UnorderedPairLogic
open Source SourceLogic PairSyntax

theorem member_iff {m} {Γ : Context m} (p x y z : Fin m) (h : Derives Γ (pair p x y)) :
    Derives Γ ((Formula.mem z p).iff ((Formula.equal z x).disj (.equal z y))) := by
  have hi := Derives.allE z h
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem member_left {m} {Γ : Context m} (p x y : Fin m) (h : Derives Γ (pair p x y)) :
    Derives Γ (.mem x p) := .impE (.conjR (member_iff p x y x h)) (.disjL (.eqRefl x))

theorem member_right {m} {Γ : Context m} (p x y : Fin m) (h : Derives Γ (pair p x y)) :
    Derives Γ (.mem y p) := .impE (.conjR (member_iff p x y y h)) (.disjR (.eqRefl y))

theorem member_cases {m} {Γ : Context m} (p x y z : Fin m)
    (h : Derives Γ (pair p x y)) (hz : Derives Γ (.mem z p)) :
    Derives Γ ((Formula.equal z x).disj (.equal z y)) := .impE (.conjL (member_iff p x y z h)) hz

theorem mem_container_subst {m} {Γ : Context m} (p q x : Fin m)
    (he : Derives Γ (.equal p q)) (hx : Derives Γ (.mem x p)) : Derives Γ (.mem x q) := by
  have hi : Derives Γ ((Formula.mem x.castSucc (Fin.last m)).instantiate p) := by
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx
  have h := Derives.eqSubst (Formula.mem x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem subst_object {m} {Γ : Context m} (p x y z : Fin m)
    (he : Derives Γ (.equal p z)) (hp : Derives Γ (pair p x y)) :
    Derives Γ (pair z x y) := by
  have hi : Derives Γ ((pair (Fin.last m) x.castSucc y.castSucc).instantiate p) := by
    simpa only [Formula.instantiate, pair_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have h := Derives.eqSubst (pair (Fin.last m) x.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, pair_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem subst_left {m} {Γ : Context m} (p x y z : Fin m)
    (he : Derives Γ (.equal x z)) (hp : Derives Γ (pair p x y)) :
    Derives Γ (pair p z y) := by
  have hi : Derives Γ ((pair p.castSucc (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, pair_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have h := Derives.eqSubst (pair p.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, pair_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem subst_right {m} {Γ : Context m} (p x y z : Fin m)
    (he : Derives Γ (.equal y z)) (hp : Derives Γ (pair p x y)) :
    Derives Γ (pair p x z) := by
  have hi : Derives Γ ((pair p.castSucc x.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, pair_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have h := Derives.eqSubst (pair p.castSucc x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, pair_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem same_members {m} {Γ : Context m} (p q x y : Fin m)
    (hp : Derives Γ (pair p x y)) (hq : Derives Γ (pair q x y)) : Derives Γ (sameMembers p q) := by
  apply Derives.allI
  have hp' : Derives (Context.image Formula.raise Γ) (pair p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hp
  have hq' : Derives (Context.image Formula.raise Γ) (pair q.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hq
  have hpm := member_iff p.castSucc x.castSucc y.castSucc (Fin.last m) hp'
  have hqm := member_iff q.castSucc x.castSucc y.castSucc (Fin.last m) hq'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hqm _)) (.impE (.conjL (add hpm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hpm _)) (.impE (.conjL (add hqm _)) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (p q x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (pair p x y)) (hq : Derives Γ (pair q x y)) : Derives Γ (.equal p q) :=
  .impE (extensionality_instance p q he) (same_members p q x y hp hq)

/-- 固定一个无序对分量之后，另一个分量可消去；包括重复分量的退化情况。 -/
theorem cancel_right {m} {Γ : Context m} (p a b c : Fin m)
    (hb : Derives Γ (pair p a b)) (hc : Derives Γ (pair p a c)) : Derives Γ (.equal b c) := by
  have hcase := member_cases p a c b hc (member_right p a b hb)
  apply Derives.disjE hcase
  · have hcb := member_cases p a b c (add hb (.equal b a)) (member_right p a c (add hc (.equal b a)))
    apply Derives.disjE hcb
    · exact eq_trans (.hyp (Or.inr (Or.inl rfl))) (eq_symm (.hyp (Or.inl rfl)))
    · exact eq_symm (.hyp (Or.inl rfl))
  · exact .hyp (Or.inl rfl)

theorem singleton_component {m} {Γ : Context m} (p q x y : Fin m)
    (hp : Derives Γ (pair p x x)) (hq : Derives Γ (pair q y y)) (he : Derives Γ (.equal p q)) :
    Derives Γ (.equal x y) := by
  have hcase := member_cases q y y x hq (mem_container_subst p q x he (member_left p x x hp))
  exact .disjE hcase (.hyp (Or.inl rfl)) (.hyp (Or.inl rfl))
end PPAC.Migration.UnorderedPairLogic
