import PPAC.Migration.FiniteIterationSyntax
import PPAC.Migration.SingletonMap

/-! 空集位置的实际单点轨迹，完整递推规律由空集性排除任何后继边。 -/
namespace PPAC.Migration.IterationBase
open Source SourceAlgebra SourceLogic PairSyntax OmegaSyntax GraphSyntax IterationSyntax

theorem singleton_successor {m} {Γ : Context m} (d z : Fin m)
    (hz : Derives Γ (empty z)) (hd : Derives Γ (pair d z z)) : Derives Γ (successor d z) := by
  apply Derives.allI
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  have hd' : Derives (Context.image Formula.raise Γ) (pair d.castSucc z.castSucc z.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc hd
  apply Derives.conjI
  · apply Derives.impI
    have hx := GraphLogic.singleton_member d.castSucc z.castSucc (Fin.last m) (add hd' _) (.hyp (Or.inl rfl))
    exact .disjR hx
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (.impE (add (add (empty_at z.castSucc (Fin.last m) hz') _) _) (.hyp (Or.inl rfl)))
    · exact .impE (.conjR (UnorderedPairLogic.member_iff d.castSucc z.castSucc z.castSucc (Fin.last m) (add (add hd' _) _)))
        (.disjL (.hyp (Or.inl rfl)))

theorem no_singleton_step {m} {Γ : Context m} (f p z a j k u v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hf : Derives Γ (pair f p p)) (hp : Derives Γ (ordered p z a))
    (hs : Derives Γ (successor k j)) (hu : Derives Γ (edge f j u)) (hv : Derives Γ (edge f k v)) : Derives Γ .bot := by
  have hjz := Derives.conjL (SingletonGraphLogic.edge_output f p z a j u he hf hp hu)
  have hkz := Derives.conjL (SingletonGraphLogic.edge_output f p z a k v he hf hp hv)
  have hjk := InsertLogic.new_member k j j hs
  have hzk := mem_subst hjz hjk
  have hzz := UnorderedPairLogic.mem_container_subst k z z hkz hzk
  exact .impE (empty_at z z hz) hzz

theorem singleton_next {m} {Γ : Context m} (f p z a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hf : Derives Γ (pair f p p)) (hp : Derives Γ (ordered p z a)) : Derives Γ (next f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc
      (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)))
  have hz' : Derives Δ (empty z.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc
      (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hz)))
  have hf' : Derives Δ (pair f.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, pair_rename] using Derives.rename Fin.castSucc
      (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)))
  have hp' : Derives Δ (ordered p.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using Derives.rename Fin.castSucc
      (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)))
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact .botE (no_singleton_step f.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc
    z.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    (add (add (add he' _) _) _) (add (add (add hz' _) _) _) (add (add (add hf' _) _) _) (add (add (add hp' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl)))

theorem from_singleton {m} {Γ : Context m} (f d p z a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hw : Derives Γ (SingletonMap.witness f d p z a)) :
    Derives Γ (FiniteIterationSyntax.witness f d z z a) := by
  have hd := Derives.conjL hw
  have hf := Derives.conjL (Derives.conjR hw)
  have hp := Derives.conjL (Derives.conjR (Derives.conjR hw))
  have hfun := Derives.conjR (Derives.conjR (Derives.conjR hw))
  exact .conjI (singleton_successor d z hz hd) (.conjI hfun
    (.conjI (Derives.conjL (SingletonGraphLogic.singleton_value f p z a he hf hp)) (singleton_next f p z a he hz hf hp)))
end PPAC.Migration.IterationBase
