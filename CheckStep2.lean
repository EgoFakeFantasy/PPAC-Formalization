import PPAC.Migration.TheoryTransport

/-! 实际原核回放和捕获敏感的语法检查。所有结论都使用原Derives。 -/
namespace PPAC.Migration.Step2Checks
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
abbrev emptySource : Source.Theory := fun _ => False
abbrev emptyContext (n : Nat) : Source.Context n := fun _ => False

def allIdentity : Source.Sentence :=
  .all (.imp (.mem 0 0) (.mem 0 0))

theorem source_all_identity : Source.Derives (emptySource.at 0) allIdentity :=
  .allI (.impI (.hyp (Or.inl rfl)))

/-- 对象核中全称闭合的恒等蕴含，不依赖ZF、模型或Con假设。 -/
theorem replay_all_identity :
    FirstOrder.Derives (FirstOrder.Theory.empty : FirstOrder.Theory ℒ) []
      (Translation.sentence allIdentity) :=
  (TheoryTransport.sentence source_all_identity).theory_weaken (by
    rintro s ⟨q, hq, _⟩
    exact False.elim hq)

def existsEq : Source.Sentence := .ex (.equal 0 0)

theorem source_exists_elimination :
    Source.Derives (emptySource.at 0) (.imp existsEq existsEq) :=
  .impI (.exE (.hyp (Or.inl rfl)) (.exI 0 (.hyp (Or.inl rfl))))

theorem replay_exists_elimination :
    FirstOrder.Derives (FirstOrder.Theory.empty : FirstOrder.Theory ℒ) []
      (Translation.sentence (.imp existsEq existsEq)) :=
  (TheoryTransport.sentence source_exists_elimination).theory_weaken (by
    rintro s ⟨q, hq, _⟩
    exact False.elim hq)

/-- 源在一个额外变量环境中的闭句推导，输出仍为空free上下文。 -/
theorem source_nonempty_at_one :
    Source.Derives (emptySource.at 1) (Source.Formula.rename Fin.elim0 existsEq) :=
  .exI 0 (.eqRefl 0)

theorem replay_nonempty_closed :
    FirstOrder.Derives (FirstOrder.Theory.empty : FirstOrder.Theory ℒ) []
      (Translation.sentence existsEq) :=
  (TheoryTransport.closed_at source_nonempty_at_one).theory_weaken (by
    rintro s ⟨q, hq, _⟩
    exact False.elim hq)

theorem source_eq_substitution :
    Source.Derives (fun q : Source.Formula 2 =>
      q = .equal 0 1 ∨ q = .mem 0 0) (.mem 1 0) :=
  .eqSubst (.mem 2 0) (.hyp (Or.inl rfl)) (.hyp (Or.inr rfl))

theorem replay_eq_substitution {free : Syntax.Ctx} (ρ : Fin 2 → Syntax.Tm [] free) :
    FirstOrder.Derives (FirstOrder.Theory.empty : FirstOrder.Theory ℒ)
      [Syntax.formula ρ (.equal 0 1), Syntax.formula ρ (.mem 0 0)]
      (Syntax.formula ρ (.mem 1 0)) := by
  apply Compile.derives source_eq_substitution ρ _
  intro q hq
  rcases hq with rfl | rfl
  · exact FirstOrder.Derives.assumption List.mem_cons_self
  · exact FirstOrder.Derives.assumption (List.mem_cons_of_mem _ List.mem_cons_self)

theorem source_classical {n} (Γ : Source.Context n) (p : Source.Formula n) :
    Source.Derives Γ (.disj p p.neg) :=
  .classical (.impE (.hyp (Or.inl rfl))
    (.disjR (.impI (.impE (.hyp (Or.inr (Or.inl rfl)))
      (.disjL (.hyp (Or.inl rfl)))))))

theorem replay_classical :
    FirstOrder.Derives (FirstOrder.Theory.empty : FirstOrder.Theory ℒ) []
      (Translation.sentence (.all (.disj (.mem 0 0) (Source.Formula.mem (n := 1) 0 0).neg))) := by
  have d : Source.Derives (emptySource.at 0)
      (.all (.disj (.mem 0 0) (Source.Formula.mem (n := 1) 0 0).neg)) :=
    .allI (source_classical _ _)
  exact (TheoryTransport.sentence d).theory_weaken (by
    rintro s ⟨q, hq, _⟩
    exact False.elim hq)

/-- 合并两个旧变量时，量词绑定的末变量不会被误合并。 -/
example :
    Source.Formula.rename (fun _ : Fin 2 => (0 : Fin 1))
      (.all (.mem 0 2) : Source.Formula 2) = .all (.mem 0 1) := by
  rfl

/-- 替换外层自由槽时，内层量词变量保持绑定。 -/
example :
    ((.all (.mem 1 2) : Source.Formula 2).instantiate (0 : Fin 1)) =
      (.all (.mem 0 1) : Source.Formula 1) := by
  rfl

/-- 全量参数化的重命名交换合同，可非单射。 -/
example {n m} {bound free : Syntax.Ctx} (ρ : Fin m → Syntax.Tm bound free)
    (r : Fin n → Fin m) (p : Source.Formula n) :
    Syntax.formula ρ (Source.Formula.rename r p) =
      Syntax.formula (fun i => ρ (r i)) p := Syntax.rename ρ r p

/-- 全量参数化的替换交换合同，而非固定深度测试。 -/
example {n} {bound free : Syntax.Ctx} (ρ : Fin n → Syntax.Tm bound free)
    (p : Source.Formula (n+1)) (t : Fin n) :
    Syntax.formula ρ (p.instantiate t) =
      (Syntax.formula (Syntax.lift ρ) p).instantiateTop (ρ t) :=
  Syntax.instantiate ρ p t

/-- 对任意源19规则证明直接得到原核Derives，不传入任何模型。 -/
example {n} {Γ : Source.Context n} {p : Source.Formula n}
    (d : Source.Derives Γ p) {T : FirstOrder.Theory ℒ} {free : Syntax.Ctx}
    (ρ : Fin n → Syntax.Tm [] free) (Δ : FirstOrder.Context ℒ free)
    (hΓ : ∀ q, Γ q → FirstOrder.Derives T Δ (Syntax.formula ρ q)) :
    FirstOrder.Derives T Δ (Syntax.formula ρ p) := Compile.derives d ρ Δ hΓ

end PPAC.Migration.Step2Checks
