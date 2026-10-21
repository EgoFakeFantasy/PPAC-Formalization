import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
/-! 原Hilbert证书有限公理支撑；无限理论不会成为无限证明对象。 -/
namespace PPAC.Migration.FiniteSupport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
def listed {σ : Signature.{u,v,w}} (xs : List (Sentence σ)) : Theory σ :=
  fun p => p ∈ xs

theorem certificate {σ : Signature.{u,v,w}} {T : Theory σ}
    {free : SortContext σ} {p : OpenFormula σ free} (d : HilbertDerivation T free p) :
    ∃ xs : List (Sentence σ), (∀ q ∈ xs, T q) ∧
      Nonempty (HilbertDerivation (listed xs) free p) := by
  induction d with
  | logical_axiom h =>
      exact ⟨[], by simp, ⟨.logical_axiom h⟩⟩
  | @theory_axiom free s hs =>
      exact ⟨[s], by intro q hq; simpa using (List.mem_singleton.mp hq ▸ hs),
        ⟨.theory_axiom (List.mem_singleton_self s)⟩⟩
  | modus_ponens dp dpq ihp ihpq =>
      obtain ⟨xs, hxs, ⟨p⟩⟩ := ihp
      obtain ⟨ys, hys, ⟨pq⟩⟩ := ihpq
      refine ⟨xs ++ ys, ?_, ⟨.modus_ponens
        (p.theoryWeakening (fun h => List.mem_append.mpr (Or.inl h)))
        (pq.theoryWeakening (fun h => List.mem_append.mpr (Or.inr h)))⟩⟩
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hxs q hq
      · exact hys q hq
  | forall_generalization d ih =>
      obtain ⟨xs, hxs, ⟨d⟩⟩ := ih
      exact ⟨xs, hxs, ⟨.forall_generalization d⟩⟩
  | free_strengthening d ih =>
      obtain ⟨xs, hxs, ⟨d⟩⟩ := ih
      exact ⟨xs, hxs, ⟨.free_strengthening d⟩⟩
  | free_substitution s d ih =>
      obtain ⟨xs, hxs, ⟨d⟩⟩ := ih
      exact ⟨xs, hxs, ⟨.free_substitution s d⟩⟩

/-- 任意原核Derives（任意有限局部上下文）都只使用有限多个理论公理。 -/
theorem derives {σ : Signature.{u,v,w}} {T : Theory σ}
    {free : SortContext σ} {Δ : Context σ free} {p : OpenFormula σ free}
    (d : FirstOrder.Derives T Δ p) :
    ∃ xs : List (Sentence σ), (∀ q ∈ xs, T q) ∧ FirstOrder.Derives (listed xs) Δ p := by
  obtain ⟨d⟩ := d
  exact certificate d
end PPAC.Migration.FiniteSupport
