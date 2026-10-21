import PPAC.Migration.OrdinalEmpty

/-! 原序数的实际后继保持原严格线性和内部良序定义。 -/
namespace PPAC.Migration.OrdinalSuccessor
open Source SourceAlgebra SourceLogic OrdinalSyntax

theorem irreflexive_successor {m} {Γ : Context m} (s a : Fin m)
    (hs : Derives Γ (OmegaSyntax.successor s a)) (hl : Derives Γ (linear a)) : Derives Γ (irreflexive s) := by
  apply Derives.allI
  have hs' : Derives (Context.image Formula.raise Γ) (OmegaSyntax.successor s.castSucc a.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using Derives.rename Fin.castSucc hs
  have hl' : Derives (Context.image Formula.raise Γ) (linear a.castSucc) := by
    simpa only [Formula.raise, linear_rename] using Derives.rename Fin.castSucc hl
  apply Derives.impI
  have hc := InsertLogic.member_cases s.castSucc a.castSucc a.castSucc (Fin.last m) (add hs' _) (.hyp (Or.inl rfl))
  apply Derives.disjE hc
  · exact .impE (add (add (irreflexive_at a.castSucc (Fin.last m) (.conjL hl')) _) _) (.hyp (Or.inl rfl))
  · exact OrdinalEmpty.no_self_of_eq (Fin.last m) a.castSucc (.hyp (Or.inl rfl)) (add (add (OrdinalEmpty.no_self a.castSucc hl') _) _)

theorem chain_successor {m} {Γ : Context m} (s a : Fin m)
    (hs : Derives Γ (OmegaSyntax.successor s a)) (ha : Derives Γ (ordinal a)) : Derives Γ (membershipTransitive s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hs' : Derives Δ (OmegaSyntax.successor s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using OrdinalRestriction.raise_three hs
  have ha' : Derives Δ (ordinal a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrdinalRestriction.raise_three ha
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let K := (Formula.mem (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
    (.mem (Fin.last (m+1)).castSucc (Fin.last (m+2)))
  let Γq := Context.add K (Context.add (.mem (Fin.last (m+2)) s.castSucc.castSucc.castSucc)
    (Context.add (.mem (Fin.last (m+1)).castSucc s.castSucc.castSucc.castSucc)
      (Context.add (.mem (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc) Δ)))
  have hc : Derives Γq ((Formula.mem (Fin.last (m+2)) a.castSucc.castSucc.castSucc).disj
      (.equal (Fin.last (m+2)) a.castSucc.castSucc.castSucc)) :=
    InsertLogic.member_cases s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc
      (Fin.last (m+2)) (add (add (add (add hs' _) _) _) _) (.hyp (Or.inr (Or.inl rfl)))
  apply Derives.disjE hc
  · have ht : Derives (Context.add (.mem (Fin.last (m+2)) a.castSucc.castSucc.castSucc) Γq)
        (transitiveSet (Fin.last (m+2))) := OrdinalTransitivity.member_transitive a.castSucc.castSucc.castSucc (Fin.last (m+2))
      (add (add (add (add (add ha' _) _) _) _) _) (.hyp (Or.inl rfl))
    exact .impE (.impE (transitiveSet_at (Fin.last (m+2)) (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc ht)
      (.conjR (.hyp (Or.inr (Or.inl rfl))))) (.conjL (.hyp (Or.inr (Or.inl rfl))))
  · let Γe := Context.add (.equal (Fin.last (m+2)) a.castSucc.castSucc.castSucc) Γq
    have hK : Derives Γe K := .hyp (Or.inr (Or.inl rfl))
    have hya := UnorderedPairLogic.mem_container_subst (Fin.last (m+2)) a.castSucc.castSucc.castSucc
      (Fin.last (m+1)).castSucc (Derives.hyp (Γ := Γe) (Or.inl rfl)) (.conjR hK)
    have hxa := Derives.impE (Derives.impE
      (add (add (add (add (add (transitiveSet_at a.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
        (Fin.last m).castSucc.castSucc (.conjL ha')) _) _) _) _) _) hya) (.conjL hK)
    exact UnorderedPairLogic.mem_container_subst a.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last m).castSucc.castSucc
      (eq_symm (.hyp (Or.inl rfl))) hxa

theorem comparable_successor {m} {Γ : Context m} (s a : Fin m)
    (hs : Derives Γ (OmegaSyntax.successor s a)) (hc : Derives Γ (comparable a)) : Derives Γ (comparable s) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hs' : Derives Δ (OmegaSyntax.successor s.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hs)
  have hc' : Derives Δ (comparable a.castSucc.castSucc) := by
    simpa only [Formula.raise, comparable_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  apply Derives.impI
  apply Derives.impI
  let Γq := Context.add (.mem (Fin.last (m+1)) s.castSucc.castSucc)
    (Context.add (.mem (Fin.last m).castSucc s.castSucc.castSucc) Δ)
  have hx : Derives Γq ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).disj
      (.equal (Fin.last m).castSucc a.castSucc.castSucc)) :=
    InsertLogic.member_cases s.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc
      (add (add hs' _) _) (.hyp (Or.inr (Or.inl rfl)))
  have hy : Derives Γq ((Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).disj
      (.equal (Fin.last (m+1)) a.castSucc.castSucc)) :=
    InsertLogic.member_cases s.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))
      (add (add hs' _) _) (.hyp (Or.inl rfl))
  apply Derives.disjE hx
  · apply Derives.disjE (add hy _)
    · exact .impE (.impE (add (add (add (add (comparable_at a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hc') _) _) _) _)
        (.hyp (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl))
    · exact .disjR (.disjL (UnorderedPairLogic.mem_container_subst a.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
        (eq_symm (.hyp (Or.inl rfl))) (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hy _)
    · exact .disjR (.disjR (UnorderedPairLogic.mem_container_subst a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
        (eq_symm (.hyp (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl))))
    · exact .disjL (eq_trans (.hyp (Or.inr (Or.inl rfl))) (eq_symm (.hyp (Or.inl rfl))))

theorem ordinal {m} {Γ : Context m} (s a : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ (OmegaSyntax.successor s a)) (ha : Derives Γ (OrdinalSyntax.ordinal a)) : Derives Γ (OrdinalSyntax.ordinal s) := by
  have ht := OrdinalTransitivity.from_canonical s
    (OmegaElementary.successor_transitive s a hs (OrdinalTransitivity.to_canonical a (.conjL ha)))
  have hl := Derives.conjL (Derives.conjR ha)
  exact .conjI ht (.conjI
    (.conjI (irreflexive_successor s a hs hl) (.conjI (chain_successor s a hs ha) (comparable_successor s a hs (.conjR (.conjR hl)))))
    (OrdinalFoundation.wellFounded s hf))
end PPAC.Migration.OrdinalSuccessor
