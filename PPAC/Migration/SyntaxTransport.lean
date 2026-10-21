import PPAC.Migration.Translation
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Algebra

/-! 源有限变量语法与原生语法变换的严格AST交换；不使用语义或完备性。 -/
namespace PPAC.Migration.Syntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
abbrev Ctx := FirstOrder.SortContext ℒ
abbrev Fm (bound free : Ctx) := FirstOrder.Formula ℒ bound free
abbrev Tm (bound free : Ctx) := FirstOrder.Term ℒ bound free SetSort.set

def lift {n} {bound free : Ctx} (ρ : Fin n → Tm bound free) :
    Fin (n+1) → Tm (SetSort.set :: bound) free :=
  Fin.lastCases (.bvar .here) (fun i => (ρ i).weakenBound SetSort.set)

def formula {n} {bound free : Ctx} (ρ : Fin n → Tm bound free) :
    Source.Formula n → Fm bound free
  | .bot => .falsum
  | .mem x y => .rel RelationSymbol.membership (.cons (ρ x) (.cons (ρ y) .nil))
  | .equal x y => .equal (ρ x) (ρ y)
  | .imp p q => .imp (formula ρ p) (formula ρ q)
  | .conj p q => .conj (formula ρ p) (formula ρ q)
  | .disj p q => .disj (formula ρ p) (formula ρ q)
  | .all p => .forallE SetSort.set (formula (lift ρ) p)
  | .ex p => .existsE SetSort.set (formula (lift ρ) p)

theorem lift_comp {n m} {bound free : Ctx} (ρ : Fin m → Tm bound free) (r : Fin n → Fin m) :
    (fun i => lift ρ (Source.Formula.liftRen r i)) = lift (fun i => ρ (r i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [lift, Source.Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

/-- 任意源重命名（可非单射）与翻译严格交换。 -/
theorem rename {n m} {bound free : Ctx} (ρ : Fin m → Tm bound free)
    (r : Fin n → Fin m) (p : Source.Formula n) :
    formula ρ (Source.Formula.rename r p) = formula (fun i => ρ (r i)) p := by
  induction p generalizing m bound with
  | bot | mem | equal => rfl
  | imp p q hp hq | conj p q hp hq | disj p q hp hq =>
      simp only [Source.Formula.rename, formula, hp, hq]
  | all p hp | ex p hp =>
      simp only [Source.Formula.rename, formula, hp, lift_comp]

theorem lift_substitute {n} {sb sf tb tf : Ctx} (ρ : Fin n → Tm sb sf)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf) :
    (fun i => (lift ρ i).substituteMapped (VariableSubstitution.liftBound SetSort.set bs)
      (VariableSubstitution.weakenBound SetSort.set fs)) =
    lift (fun i => (ρ i).substituteMapped bs fs) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [lift, Fin.lastCases_last, Term.substituteMapped, VariableSubstitution.liftBound]
  · simpa only [lift, Fin.lastCases_castSucc] using
      Term.substituteMapped_weakenBound SetSort.set bs fs (ρ j)

/-- 原生bound/free统一替换与全部源公式构造子严格交换。 -/
theorem substitute {n} {sb sf tb tf : Ctx} (ρ : Fin n → Tm sb sf)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf)
    (p : Source.Formula n) :
    (formula ρ p).substituteMapped bs fs =
      formula (fun i => (ρ i).substituteMapped bs fs) p := by
  induction p generalizing sb tb with
  | bot | mem | equal => rfl
  | imp p q hp hq | conj p q hp hq | disj p q hp hq =>
      simp only [formula, FirstOrder.Formula.substituteMapped, hp, hq]
  | all p hp | ex p hp =>
      simp only [formula, FirstOrder.Formula.substituteMapped, hp, lift_substitute]

/-- 原生重命名是统一替换的变量项特例。 -/
theorem native_rename {n} {sb sf tb tf : Ctx} (ρ : Fin n → Tm sb sf)
    (br : VariableRenaming sb tb) (fr : VariableRenaming sf tf) (p : Source.Formula n) :
    (formula ρ p).renameMapped br fr = formula (fun i => (ρ i).renameMapped br fr) p := by
  rw [FirstOrder.Formula.renameMapped_eq_substituteMapped, substitute]
  congr 1
  funext i
  exact (Term.renameMapped_eq_substituteMapped br fr (ρ i)).symm

theorem instantiate_lift {n} {bound free : Ctx} (ρ : Fin n → Tm bound free)
    (t : Tm bound free) (p : Source.Formula (n+1)) :
    (formula (lift ρ) p).instantiateTop t = formula (Fin.lastCases t ρ) p := by
  change (formula (lift ρ) p).substituteMapped
    (VariableSubstitution.instantiateTop t) VariableSubstitution.freeId = _
  rw [substitute]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [lift, Fin.lastCases_last, Term.substituteMapped, VariableSubstitution.instantiateTop]
  · simpa only [lift, Fin.lastCases_castSucc, Term.instantiateTop, Term.substitute, Substitution.instantiateTop] using
      Term.instantiateTop_weakenBound t (ρ j)

/-- 源变量项替换与原生instantiateTop严格交换，允许捕获敏感的嵌套量词。 -/
theorem instantiate {n} {bound free : Ctx} (ρ : Fin n → Tm bound free)
    (p : Source.Formula (n+1)) (t : Fin n) :
    formula ρ (p.instantiate t) = (formula (lift ρ) p).instantiateTop (ρ t) := by
  rw [Source.Formula.instantiate, rename, instantiate_lift]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]

def fresh {n} {free : Ctx} (ρ : Fin n → Tm [] free) :
    Fin (n+1) → Tm [] (SetSort.set :: free) :=
  Fin.lastCases (.fvar .here) (fun i => (ρ i).weakenFree SetSort.set)

theorem weaken_free {n} {bound free : Ctx} (ρ : Fin n → Tm bound free)
    (p : Source.Formula n) :
    (formula ρ p).weakenFree SetSort.set =
      formula (fun i => (ρ i).weakenFree SetSort.set) p :=
  native_rename ρ VariableRenaming.id (VariableRenaming.weaken SetSort.set) p

theorem fresh_raise {n} {free : Ctx} (ρ : Fin n → Tm [] free) (p : Source.Formula n) :
    formula (fresh ρ) p.raise = (formula ρ p).weakenFree SetSort.set := by
  rw [Source.Formula.raise, rename, weaken_free]
  congr 1
  funext i
  exact Fin.lastCases_castSucc i

/-- 纯成员语言中的开放项只有free变量，不暗中加入常元。 -/
theorem open_term_abstract {free : Ctx} {sort : SetSort}
    (t : FirstOrder.Term ℒ [] free sort) :
    (t.weakenFree SetSort.set).substituteMapped
      (VariableSubstitution.abstractBound (σ := ℒ) (bound := []) (free := free) SetSort.set) VariableSubstitution.abstractFreeTop =
      t.weakenBound SetSort.set := by
  rw [Term.substituteMapped_weakenFree_tail]
  exact (Term.renameMapped_eq_substituteMapped
    (VariableRenaming.weaken SetSort.set) VariableRenaming.id t).symm

theorem fresh_abstract {n} {free : Ctx} (ρ : Fin n → Tm [] free)
    (p : Source.Formula (n+1)) :
    (formula (fresh ρ) p).abstractFreeTop = formula (lift ρ) p := by
  change (formula (fresh ρ) p).substituteMapped
    (VariableSubstitution.abstractBound (σ := ℒ) (bound := []) (free := free) SetSort.set)
    VariableSubstitution.abstractFreeTop = _
  rw [substitute]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fresh, lift, Fin.lastCases_last, Term.substituteMapped, VariableSubstitution.abstractFreeTop]
  · simpa only [fresh, lift, Fin.lastCases_castSucc] using open_term_abstract (ρ j)

theorem forall_fresh {n} {free : Ctx} (ρ : Fin n → Tm [] free)
    (p : Source.Formula (n+1)) :
    (formula (fresh ρ) p).forallFreeTop SetSort.set = formula ρ (.all p) := by
  simp only [FirstOrder.Formula.forallFreeTop, fresh_abstract, formula]

theorem exists_fresh {n} {free : Ctx} (ρ : Fin n → Tm [] free)
    (p : Source.Formula (n+1)) :
    (formula (fresh ρ) p).existsFreeTop SetSort.set = formula ρ (.ex p) := by
  simp only [FirstOrder.Formula.existsFreeTop, fresh_abstract, formula]
theorem lift_bvars {n} {bound : Ctx} (ρ : Fin n → Variable bound SetSort.set) :
    lift (fun i => (.bvar (ρ i) : Tm bound [])) =
      (fun i => (.bvar (Translation.lift ρ i) : Tm (SetSort.set :: bound) [])) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [lift, Translation.lift, Fin.lastCases_last, Fin.lastCases_castSucc, Term.weakenBound_bvar]

/-- 新的开放项翻译保持第一步闭句及bound-only翻译原样。 -/
theorem old_formula {n} {bound : Ctx} (ρ : Fin n → Variable bound SetSort.set)
    (p : Source.Formula n) :
    formula (fun i => .bvar (ρ i)) p = Translation.formula ρ p := by
  induction p generalizing bound with
  | bot | mem | equal => rfl
  | imp p q hp hq | conj p q hp hq | disj p q hp hq =>
      simp only [formula, Translation.formula, hp, hq]
  | all p hp | ex p hp =>
      simp only [formula, Translation.formula, lift_bvars, hp]

theorem empty_formula (p : Source.Sentence) :
    formula (Fin.elim0 : Fin 0 → Tm [] []) p = Translation.sentence p := by
  have h := old_formula (Fin.elim0 : Fin 0 → Variable ([] : Ctx) SetSort.set) p
  have e : (fun i : Fin 0 => (.bvar (Fin.elim0 i) : Tm [] [])) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [e] at h
  exact h

theorem closed_fromSentence {free : Ctx} (ρ : Fin 0 → Tm [] free) (p : Source.Sentence) :
    formula ρ p = (Translation.sentence p).fromSentence := by
  have h := native_rename (Fin.elim0 : Fin 0 → Tm [] [])
    (VariableRenaming.id : VariableRenaming ([] : Ctx) [])
    (VariableRenaming.empty : VariableRenaming ([] : Ctx) free) p
  have e : (fun i : Fin 0 =>
      (Fin.elim0 i : Tm [] []).renameMapped VariableRenaming.id VariableRenaming.empty) = ρ := by
    funext i
    exact Fin.elim0 i
  rw [e, empty_formula] at h
  cases free with
  | nil =>
      have eρ : ρ = (Fin.elim0 : Fin 0 → Tm [] []) := by
        funext i
        exact Fin.elim0 i
      rw [eρ, empty_formula]
      rfl
  | cons head tail =>
      exact h.symm

def variables : {n : Nat} → Fin n → Tm [] (List.replicate n SetSort.set)
  | 0, i => Fin.elim0 i
  | _+1, i => fresh variables i
end PPAC.Migration.Syntax
