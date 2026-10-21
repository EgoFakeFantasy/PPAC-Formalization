import PPAC.Migration.InsertSyntax

/-! 原Pairing和Union构造插入集的成员推导，无选择或宿主集合构造。 -/
namespace PPAC.Migration.InsertLogic
open Source SourceAlgebra SourceLogic PairSyntax InsertSyntax GraphLogic UnorderedPairLogic

theorem fiber_intro {m} {Γ : Context m} (a z w : Fin m)
    (hw : Derives Γ (.mem w a)) (hz : Derives Γ (.mem z w)) : Derives Γ (unionFiber a z) := by
  apply Derives.exI w
  simpa only [Formula.instantiate, Formula.rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hw hz

theorem forward {m} {Γ : Context m} (b a x s p z : Fin m)
    (hs : Derives Γ (pair s x x)) (hp : Derives Γ (pair p a s)) (hu : Derives Γ (unionOf b p))
    (hz : Derives Γ (.mem z b)) : Derives Γ ((Formula.mem z a).disj (.equal z x)) := by
  have he := Derives.impE (.conjL (union_at b p z hu)) hz
  let W := (Formula.mem (Fin.last m) p.castSucc).conj (.mem z.castSucc (Fin.last m))
  let Γw := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at he
  apply Derives.exE (p := W) he
  have hsW : Derives Γw (pair s.castSucc x.castSucc x.castSucc) := by
    simpa only [Formula.raise, pair_rename] using under hs W
  have hpW : Derives Γw (pair p.castSucc a.castSucc s.castSucc) := by
    simpa only [Formula.raise, pair_rename] using under hp W
  have hW : Derives Γw W := .hyp (Or.inl rfl)
  have hc := member_cases p.castSucc a.castSucc s.castSucc (Fin.last m) hpW (.conjL hW)
  apply Derives.disjE hc
  · exact .disjL (mem_container_subst (Fin.last m) a.castSucc z.castSucc (.hyp (Or.inl rfl)) (add (.conjR hW) _))
  · have hzs := mem_container_subst (Fin.last m) s.castSucc z.castSucc
      (.hyp (Or.inl rfl)) (add (.conjR hW) (.equal (Fin.last m) s.castSucc))
    exact .disjR (singleton_member s.castSucc x.castSucc z.castSucc (add hsW _) hzs)

theorem backward {m} {Γ : Context m} (b a x s p z : Fin m)
    (hs : Derives Γ (pair s x x)) (hp : Derives Γ (pair p a s)) (hu : Derives Γ (unionOf b p))
    (hz : Derives Γ ((Formula.mem z a).disj (.equal z x))) : Derives Γ (.mem z b) := by
  apply Derives.disjE hz
  · exact .impE (.conjR (add (union_at b p z hu) _))
      (fiber_intro p z a (member_left p a s (add hp _)) (.hyp (Or.inl rfl)))
  · have hzs : Derives (Context.add (.equal z x) Γ) (.mem z s) :=
      .impE (.conjR (member_iff s x x z (add hs _))) (.disjL (.hyp (Or.inl rfl)))
    exact .impE (.conjR (add (union_at b p z hu) _)) (fiber_intro p z s (member_right p a s (add hp _)) hzs)

theorem from_union {m} {Γ : Context m} (b a x s p : Fin m)
    (hs : Derives Γ (pair s x x)) (hp : Derives Γ (pair p a s)) (hu : Derives Γ (unionOf b p)) :
    Derives Γ (insert b a x) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (pair s.castSucc x.castSucc x.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hs
  have hp' : Derives (Context.image Formula.raise Γ) (pair p.castSucc a.castSucc s.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hp
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf b.castSucc p.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  apply Derives.conjI
  · apply Derives.impI
    exact forward b.castSucc a.castSucc x.castSucc s.castSucc p.castSucc (Fin.last m)
      (add hs' _) (add hp' _) (add hu' _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact backward b.castSucc a.castSucc x.castSucc s.castSucc p.castSucc (Fin.last m)
      (add hs' _) (add hp' _) (add hu' _) (.hyp (Or.inl rfl))

theorem old_member {m} {Γ : Context m} (b a x z : Fin m)
    (hi : Derives Γ (insert b a x)) (hz : Derives Γ (.mem z a)) : Derives Γ (.mem z b) :=
  .impE (.conjR (insert_at b a x z hi)) (.disjL hz)

theorem new_member {m} {Γ : Context m} (b a x : Fin m)
    (hi : Derives Γ (insert b a x)) : Derives Γ (.mem x b) :=
  .impE (.conjR (insert_at b a x x hi)) (.disjR (.eqRefl x))

theorem member_cases {m} {Γ : Context m} (b a x z : Fin m)
    (hi : Derives Γ (insert b a x)) (hz : Derives Γ (.mem z b)) :
    Derives Γ ((Formula.mem z a).disj (.equal z x)) := .impE (.conjL (insert_at b a x z hi)) hz

theorem same_members {m} {Γ : Context m} (b c a x : Fin m)
    (hb : Derives Γ (insert b a x)) (hc : Derives Γ (insert c a x)) : Derives Γ (PairSyntax.sameMembers b c) := by
  apply Derives.allI
  have hb' : Derives (Context.image Formula.raise Γ) (insert b.castSucc a.castSucc x.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hb
  have hc' : Derives (Context.image Formula.raise Γ) (insert c.castSucc a.castSucc x.castSucc) := by
    simpa only [Formula.raise, insert_rename] using Derives.rename Fin.castSucc hc
  have hbm := insert_at b.castSucc a.castSucc x.castSucc (Fin.last m) hb'
  have hcm := insert_at c.castSucc a.castSucc x.castSucc (Fin.last m) hc'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hcm _)) (.impE (.conjL (add hbm _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hbm _)) (.impE (.conjL (add hcm _)) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (b c a x : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hb : Derives Γ (insert b a x)) (hc : Derives Γ (insert c a x)) : Derives Γ (.equal b c) :=
  .impE (extensionality_instance b c he) (same_members b c a x hb hc)

theorem subst_point {m} {Γ : Context m} (b a x z : Fin m)
    (he : Derives Γ (.equal x z)) (hb : Derives Γ (insert b a x)) : Derives Γ (insert b a z) := by
  have hi : Derives Γ ((insert b.castSucc a.castSucc (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, insert_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hb
  have h := Derives.eqSubst (insert b.castSucc a.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, insert_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h
end PPAC.Migration.InsertLogic
