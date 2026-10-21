import PPAC.Migration.DerivationTransport
import PPAC.Migration.FiniteSupport
import PPAC.Migration.Contract

/-! 任意源闭句理论的实际原核传输；尚不声称两个ZF呈现等价或内部Con主句。 -/
namespace PPAC.Migration.TheoryTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory Syntax
attribute [local implicit_reducible] SetTheory.signature

def theory (T : Source.Theory) : FirstOrder.Theory ℒ :=
  fun p => ∃ q, T q ∧ p = Translation.sentence q

theorem derives_at {T : Source.Theory} {n} {p : Source.Formula n}
    (d : Source.Derives (T.at n) p) {free : Ctx} (ρ : Fin n → Tm [] free) :
    FirstOrder.Derives (theory T) [] (formula ρ p) := by
  apply Compile.derives d ρ []
  rintro q ⟨s, hs, rfl⟩
  rw [Syntax.rename, closed_fromSentence]
  exact FirstOrder.Derives.theory_axiom ⟨s, hs, rfl⟩

/-- 输入源闭句的证明，输出同一闭句原生像的原Hilbert核证书。 -/
theorem sentence {T : Source.Theory} {p : Source.Sentence}
    (d : Source.Derives (T.at 0) p) :
    FirstOrder.Derives (theory T) [] (Translation.sentence p) := by
  simpa only [empty_formula] using derives_at d (Fin.elim0 : Fin 0 → Tm [] [])

theorem finite_support {T : Source.Theory} {p : Source.Sentence}
    (d : Source.Derives (T.at 0) p) :
    ∃ xs : List (FirstOrder.Sentence ℒ), (∀ q ∈ xs, theory T q) ∧
      FirstOrder.Derives (FiniteSupport.listed xs) [] (Translation.sentence p) :=
  FiniteSupport.derives (sentence d)

/-- 只删去未使用的free变量；不选取对象元素或增加常元。 -/
theorem clear_falsum {σ : Signature.{u,v,w}} {T : FirstOrder.Theory σ}
    (free : FirstOrder.SortContext σ) :
    FirstOrder.Derives T ([] : FirstOrder.Context σ free) .falsum →
      FirstOrder.Derives T ([] : FirstOrder.Context σ []) .falsum := by
  induction free with
  | nil => exact id
  | cons sort rest ih =>
      intro h
      exact ih (FirstOrder.Derives.free_strengthening (sort := sort) (Γ := []) h)

/-- 源闭句在任意有限free上下文中的像可逐层删除未用变量。 -/
theorem clear_closed {T : FirstOrder.Theory ℒ} (p : Source.Sentence) (free : Ctx) :
    FirstOrder.Derives T ([] : FirstOrder.Context ℒ free)
      (formula (Fin.elim0 : Fin 0 → Tm [] free) p) →
    FirstOrder.Derives T [] (Translation.sentence p) := by
  induction free with
  | nil =>
      intro h
      simpa only [empty_formula] using h
  | cons head tail ih =>
      cases head
      intro h
      apply ih
      apply FirstOrder.Derives.free_strengthening (sort := SetSort.set) (Γ := [])
      have hw := Syntax.weaken_free (Fin.elim0 : Fin 0 → Tm [] tail) p
      have he : (fun i : Fin 0 => (Fin.elim0 i : Tm [] tail).weakenFree SetSort.set) =
          (Fin.elim0 : Fin 0 → Tm [] (SetSort.set :: tail)) := by
        funext i
        exact Fin.elim0 i
      rw [he] at hw
      exact hw.symm ▸ h

/-- 源允许在任意n个变量环境证明闭句；编译结果仍在原核空free上下文。 -/
theorem closed_at {T : Source.Theory} {n} {p : Source.Sentence}
    (d : Source.Derives (T.at n) (Source.Formula.rename Fin.elim0 p)) :
    FirstOrder.Derives (theory T) [] (Translation.sentence p) := by
  have hd := derives_at d (@variables n)
  rw [Syntax.rename] at hd
  have he : (fun i : Fin 0 => (@variables n) (Fin.elim0 i)) =
      (Fin.elim0 : Fin 0 → Tm [] (List.replicate n SetSort.set)) := by
    funext i
    exact Fin.elim0 i
  rw [he] at hd
  exact clear_closed p _ hd

/-- 正向编译给出的外部一致性方向；不是内部Con蕴含，也不是目标主定理。 -/
theorem consistent_source_of_native {T : Source.Theory}
    (h : FirstOrder.Derives.Consistent (theory T) ([] : FirstOrder.Context ℒ [])) :
    Source.Consistent T := by
  intro n d
  exact h (clear_falsum _ (derives_at d (@variables n)))
end PPAC.Migration.TheoryTransport
