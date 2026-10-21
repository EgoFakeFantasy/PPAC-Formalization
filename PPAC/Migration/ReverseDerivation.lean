import PPAC.Migration.ReverseLogicalAxioms
import PPAC.Migration.Presentation

/-!
原核6类推导构造回放到原19规则。default仅为回译的外部变量编号；
它处理free_strengthening，不是对象常元、非空公理或选择函数。
-/
namespace PPAC.Migration.ReverseCompile
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open ReverseSubstitution
attribute [local implicit_reducible] SetTheory.signature

theorem certificate {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx} {p : Syntax.Fm [] free}
    (d : HilbertDerivation T free p) {n} (default : Fin n) (f : Reverse.Vars free n) :
    Source.Derives ((Presentation.source T).at n) (Reverse.formula empty f p) := by
  induction d generalizing n with
  | logical_axiom h => exact ReverseLogicalAxioms.replay h f
  | theory_axiom h =>
      rw [fromSentence]
      exact .hyp ⟨_, ⟨_, h, rfl⟩, rfl⟩
  | modus_ponens hp hpq ihp ihpq =>
      exact .impE (ihpq default f) (ihp default f)
  | @forall_generalization free sort p d ih =>
      cases sort
      rw [forall_top]
      apply Source.Derives.allI
      rw [SourceAlgebra.theory_at_raise]
      exact ih default.castSucc (Reverse.lift f)
  | @free_strengthening free sort p d ih =>
      cases sort
      have h := ih default (fill f default)
      rw [strengthen] at h
      exact h
  | free_substitution substitution d ih =>
      rw [substitute_free]
      exact ih default (fun v => Reverse.term empty f (substitution v))

/-- 原核的有限局部假设逐个在原源演算中应用。 -/
theorem eliminate_discharge {free : Syntax.Ctx} {n} {Γ : Source.Context n}
    (f : Reverse.Vars free n) (Δ : FirstOrder.Context ℒ free) (p : Syntax.Fm [] free)
    (h : Source.Derives Γ (Reverse.formula empty f (FirstOrder.Context.discharge Δ p)))
    (supply : ∀ q ∈ Δ, Source.Derives Γ (Reverse.formula empty f q)) :
    Source.Derives Γ (Reverse.formula empty f p) := by
  induction Δ generalizing p with
  | nil => exact h
  | cons q Δ ih =>
      have hi := ih (.imp q p) h (fun r hr => supply r (List.mem_cons_of_mem q hr))
      exact .impE hi (supply q List.mem_cons_self)

/-- 任意有限原核假设列表回译；源上下文恰由回译理论公理和回译局部假设组成。 -/
def context (T : FirstOrder.Theory ℒ) {free : Syntax.Ctx} {n} (f : Reverse.Vars free n)
    (Δ : FirstOrder.Context ℒ free) : Source.Context n :=
  fun q => (Presentation.source T).at n q ∨ ∃ r ∈ Δ, q = Reverse.formula empty f r

theorem derives {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    {Δ : FirstOrder.Context ℒ free} {p : Syntax.Fm [] free}
    (d : FirstOrder.Derives T Δ p) {n} (default : Fin n) (f : Reverse.Vars free n) :
    Source.Derives (context T f Δ) (Reverse.formula empty f p) := by
  rcases d with ⟨d⟩
  apply eliminate_discharge f Δ p
    (Source.Derives.weaken (fun _ h => Or.inl h) (certificate d default f))
  intro q hq
  exact .hyp (Or.inr ⟨q, hq, rfl⟩)

/-- 闭句回放使用一个未用的源变量；源一致性本来就量化所有有限变量环境。 -/
theorem sentence {T : FirstOrder.Theory ℒ} {p : FirstOrder.Sentence ℒ}
    (d : FirstOrder.Derives T [] p) :
    Source.Derives ((Presentation.source T).at 1)
      ((Reverse.sentence p).rename Fin.elim0) := by
  rcases d with ⟨d⟩
  rw [rename_sentence]
  exact certificate d 0 empty

/-- 仅为外部一致性方向；不表示内部Con公式或内部编译器正确性。 -/
theorem consistent_native_of_source {T : FirstOrder.Theory ℒ}
    (h : Source.Consistent (Presentation.source T)) :
    FirstOrder.Derives.Consistent T ([] : FirstOrder.Context ℒ []) := by
  intro d
  exact h 1 (sentence d)

/-- 源理论先正向编码再回译，闭公理集合精确恢复；不比较Collection与Replacement。 -/
theorem source_theory_roundtrip (T : Source.Theory) :
    Presentation.source (TheoryTransport.theory T) = T := by
  funext q
  apply propext
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    simpa only [Reverse.source_sentence_roundtrip] using hp
  · intro hq
    exact ⟨Translation.sentence q, ⟨q, hq, rfl⟩, (Reverse.source_sentence_roundtrip q).symm⟩

/-- 正向理论像上的任意原核闭句证明反向返回原源理论，精确恢复原闭句。 -/
theorem source_sentence {T : Source.Theory} {p : Source.Sentence}
    (d : FirstOrder.Derives (TheoryTransport.theory T) [] (Translation.sentence p)) :
    Source.Derives (T.at 1) (p.rename Fin.elim0) := by
  have h := sentence d
  rw [source_theory_roundtrip, Reverse.source_sentence_roundtrip] at h
  exact h

/-- 任意源闭句，两个实际演算之间往返；源端允许一个未用变量。 -/
theorem source_sentence_iff {T : Source.Theory} {p : Source.Sentence} :
    FirstOrder.Derives (TheoryTransport.theory T) [] (Translation.sentence p) ↔
      Source.Derives (T.at 1) (p.rename Fin.elim0) :=
  ⟨source_sentence, TheoryTransport.closed_at⟩

/-- 全变量范围的外部一致性等价；仍不是对象内部Con蕴含。 -/
theorem source_consistent_iff (T : Source.Theory) :
    FirstOrder.Derives.Consistent (TheoryTransport.theory T) ([] : FirstOrder.Context ℒ []) ↔
      Source.Consistent T := by
  constructor
  · exact TheoryTransport.consistent_source_of_native
  · intro h
    have hs : Source.Consistent (Presentation.source (TheoryTransport.theory T)) := by
      rw [source_theory_roundtrip]
      exact h
    exact consistent_native_of_source hs
end PPAC.Migration.ReverseCompile
