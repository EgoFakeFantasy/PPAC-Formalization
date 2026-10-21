import PPAC.Migration.Normalization

/-! 原生纯成员全语法回译到源8构造器语法。只作句法与原核等价，不宣称反向推导传输。 -/
namespace PPAC.Migration.Reverse
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
abbrev Vars (scope : Syntax.Ctx) (n : Nat) := {s : SetSort} → Variable scope s → Fin n

def lift {scope : Syntax.Ctx} {n} (v : Vars scope n) : Vars (SetSort.set :: scope) (n+1)
  | _, .here => Fin.last n
  | _, .there i => (v i).castSucc

def term {bound free : Syntax.Ctx} {n} (b : Vars bound n) (f : Vars free n) :
    {s : SetSort} → FirstOrder.Term ℒ bound free s → Fin n
  | _, .bvar v => b v
  | _, .fvar v => f v
  | _, .app symbol _ => nomatch symbol

def formula {bound free : Syntax.Ctx} {n} (b : Vars bound n) (f : Vars free n) :
    Syntax.Fm bound free → Source.Formula n
  | .falsum => .bot
  | .truth => .imp .bot .bot
  | .rel .membership (.cons s (.cons t .nil)) => .mem (term b f s) (term b f t)
  | .equal s t => .equal (term b f s) (term b f t)
  | .neg p => (formula b f p).neg
  | .conj p q => .conj (formula b f p) (formula b f q)
  | .disj p q => .disj (formula b f p) (formula b f q)
  | .imp p q => .imp (formula b f p) (formula b f q)
  | .iff p q => (formula b f p).iff (formula b f q)
  | .forallE .set p => .all (formula (lift b) (fun i => (f i).castSucc) p)
  | .existsE .set p => .ex (formula (lift b) (fun i => (f i).castSucc) p)

def empty : Vars [] 0 := fun v => nomatch v

def sentence (p : FirstOrder.Sentence ℒ) : Source.Sentence := formula empty empty p

/-- 回译项后再翻译，恢复原项；条件明确保留bound/free的区别。 -/
theorem term_roundtrip {bound free : Syntax.Ctx} {n}
    (b : Vars bound n) (f : Vars free n) (ρ : Fin n → Syntax.Tm bound free)
    (hb : ∀ v, ρ (b v) = .bvar v) (hf : ∀ v, ρ (f v) = .fvar v)
    (t : Syntax.Tm bound free) : ρ (term b f t) = t := by
  match t with
  | .bvar v => exact hb v
  | .fvar v => exact hf v
  | .app symbol _ => exact nomatch symbol

/-- 原生全语法往返恰好是连接词展开；任意绑定深度、任意有限变量环境。 -/
theorem native_roundtrip {bound free : Syntax.Ctx} {n}
    (b : Vars bound n) (f : Vars free n) (ρ : Fin n → Syntax.Tm bound free)
    (hb : ∀ v, ρ (b v) = .bvar v) (hf : ∀ v, ρ (f v) = .fvar v)
    (p : Syntax.Fm bound free) :
    Syntax.formula ρ (formula b f p) = Normalization.formula p := by
  induction p generalizing n with
  | falsum | truth => rfl
  | rel r ts =>
      cases r
      match ts with
      | .cons s (.cons t .nil) =>
          simp only [formula, Syntax.formula, Normalization.formula,
            term_roundtrip b f ρ hb hf]
  | @equal _ _ sort s t =>
      cases sort
      simp only [formula, Syntax.formula, Normalization.formula,
        term_roundtrip b f ρ hb hf]
  | neg p ih => simp only [formula, Syntax.formula, Normalization.formula, ih b f ρ hb hf]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [formula, Syntax.formula, Normalization.formula, ihp b f ρ hb hf, ihq b f ρ hb hf]
  | forallE s p ih | existsE s p ih =>
      cases s
      have hb' : ∀ (v : Variable (SetSort.set :: _) SetSort.set),
          Syntax.lift ρ (lift b v) = .bvar v := by
        intro v
        cases v with
        | here => simp only [lift, Syntax.lift, Fin.lastCases_last]
        | there v => simp only [lift, Syntax.lift, Fin.lastCases_castSucc, hb,
            Term.weakenBound_bvar]
      have hf' : ∀ (v : Variable _ SetSort.set),
          Syntax.lift ρ ((f v).castSucc) = .fvar v := by
        intro v
        simp only [Syntax.lift, Fin.lastCases_castSucc, hf, Term.weakenBound_fvar]
      simp only [formula, Syntax.formula, Normalization.formula]
      congr 1
      exact ih (lift b) (fun i => (f i).castSucc) (Syntax.lift ρ) hb' hf'
theorem term_lift {bound free : Syntax.Ctx} {n}
    (b : Vars bound n) (f : Vars free n) (t : Syntax.Tm bound free) :
    term (lift b) (fun i => (f i).castSucc) (t.weakenBound SetSort.set) =
      (term b f t).castSucc := by
  match t with
  | .bvar v => rfl
  | .fvar v => rfl
  | .app symbol _ => exact nomatch symbol

theorem lift_decode {bound free : Syntax.Ctx} {n m}
    (b : Vars bound n) (f : Vars free n) (ρ : Fin m → Syntax.Tm bound free) :
    (fun i => term (lift b) (fun v => (f v).castSucc) (Syntax.lift ρ i)) =
      Source.Formula.liftRen (fun i => term b f (ρ i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Syntax.lift, Source.Formula.liftRen, Fin.lastCases_last, term, lift]
  · simpa only [Syntax.lift, Source.Formula.liftRen, Fin.lastCases_castSucc] using
      term_lift b f (ρ j)

/-- 正向再反向严格恢复源语法的变量像，不丢弃任意schema参数。 -/
theorem source_roundtrip {bound free : Syntax.Ctx} {n m}
    (b : Vars bound n) (f : Vars free n) (ρ : Fin m → Syntax.Tm bound free)
    (p : Source.Formula m) :
    formula b f (Syntax.formula ρ p) =
      Source.Formula.rename (fun i => term b f (ρ i)) p := by
  induction p generalizing n bound with
  | bot | mem | equal => rfl
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [Syntax.formula, formula, Source.Formula.rename, ihp, ihq]
  | all p ih | ex p ih =>
      simp only [Syntax.formula, formula, Source.Formula.rename, ih, lift_decode]

theorem source_rename_id {n} (p : Source.Formula n) :
    Source.Formula.rename id p = p := by
  induction p with
  | bot | mem | equal => rfl
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [Source.Formula.rename, ihp, ihq]
  | @all n p ih | @ex n p ih =>
      have e : Source.Formula.liftRen (id : Fin n → Fin n) = id := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp only [Source.Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      simp only [Source.Formula.rename, e, ih]

/-- 全部源闭句严格往返，包括PP、AC、ACwo及任意公理模式实例。 -/
theorem source_sentence_roundtrip (p : Source.Sentence) :
    sentence (Translation.sentence p) = p := by
  rw [sentence, ← Syntax.empty_formula, source_roundtrip]
  have e : (fun i : Fin 0 => term empty empty (Fin.elim0 i : Syntax.Tm [] [])) = id := by
    funext i
    exact Fin.elim0 i
  rw [e, source_rename_id]

/-- 全部原生闭句往返是精确的连接词规范形等式。 -/
theorem native_sentence_roundtrip (p : FirstOrder.Sentence ℒ) :
    Translation.sentence (sentence p) = Normalization.formula p := by
  rw [← Syntax.empty_formula]
  exact native_roundtrip empty empty Fin.elim0 (fun v => nomatch v) (fun v => nomatch v) p

/-- 对象层验收：闭句回译往返的等价有原Derives证书，无ZF/AC/Con前提。 -/
theorem sentence_equivalent {T : FirstOrder.Theory ℒ}
    {Γ : FirstOrder.Context ℒ []} (p : FirstOrder.Sentence ℒ) :
    FirstOrder.Derives T Γ (.iff p (Translation.sentence (sentence p))) := by
  rw [native_sentence_roundtrip]
  exact Normalization.equivalent p

/-- 保持同一原核理论的闭句规范化；这不是native→source演绎规则的反向编译。 -/
theorem normalize_derives {T : FirstOrder.Theory ℒ}
    {Γ : FirstOrder.Context ℒ []} {p : FirstOrder.Sentence ℒ}
    (h : FirstOrder.Derives T Γ p) :
    FirstOrder.Derives T Γ (Translation.sentence (sentence p)) :=
  .iff_elim_left (sentence_equivalent p) h

theorem denormalize_derives {T : FirstOrder.Theory ℒ}
    {Γ : FirstOrder.Context ℒ []} {p : FirstOrder.Sentence ℒ}
    (h : FirstOrder.Derives T Γ (Translation.sentence (sentence p))) :
    FirstOrder.Derives T Γ p :=
  .iff_elim_right (sentence_equivalent p) h
end PPAC.Migration.Reverse
