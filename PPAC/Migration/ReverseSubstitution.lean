import PPAC.Migration.ReverseSyntax
import PPAC.Migration.SourceAlgebra

/-! 原核纯成员语法回译与全部替换交换，供六规则反向编译使用。 -/
namespace PPAC.Migration.ReverseSubstitution
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature

def empty {n} : Reverse.Vars [] n := fun v => nomatch v

theorem term_rename_source {bound free : Syntax.Ctx} {n m} (b : Reverse.Vars bound n)
    (f : Reverse.Vars free n) (r : Fin n → Fin m) {s : SetSort} (t : FirstOrder.Term ℒ bound free s) :
    r (Reverse.term b f t) = Reverse.term (fun v => r (b v)) (fun v => r (f v)) t := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app symbol _ => exact nomatch symbol

theorem lift_rename_source {bound : Syntax.Ctx} {n m} (b : Reverse.Vars bound n) (r : Fin n → Fin m) :
    (fun {s} (v : Variable (SetSort.set :: bound) s) => Source.Formula.liftRen r (Reverse.lift b v)) =
      @Reverse.lift bound m (fun v => r (b v)) := by
  funext s v
  cases v with
  | here => simp only [Reverse.lift, Source.Formula.liftRen, Fin.lastCases_last]
  | there v => simp only [Reverse.lift, Source.Formula.liftRen, Fin.lastCases_castSucc]

theorem free_rename_source {free : Syntax.Ctx} {n m} (f : Reverse.Vars free n) (r : Fin n → Fin m) :
    (fun {s} (v : Variable free s) => Source.Formula.liftRen r ((f v).castSucc)) =
      (fun {s} (v : Variable free s) => (r (f v)).castSucc) := by
  funext s v
  exact Fin.lastCases_castSucc (f v)

theorem formula_rename_source {bound free : Syntax.Ctx} {n m} (b : Reverse.Vars bound n)
    (f : Reverse.Vars free n) (r : Fin n → Fin m) (p : Syntax.Fm bound free) :
    Source.Formula.rename r (Reverse.formula b f p) =
      Reverse.formula (fun v => r (b v)) (fun v => r (f v)) p := by
  induction p generalizing n m with
  | falsum | truth => rfl
  | rel s ts =>
      cases s
      match ts with
      | .cons x (.cons y .nil) =>
          simp only [Reverse.formula, Source.Formula.rename, term_rename_source]
  | equal s t => simp only [Reverse.formula, Source.Formula.rename, term_rename_source]
  | neg p ih => simp only [Reverse.formula, Source.Formula.rename, ih]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [Reverse.formula, Source.Formula.rename, ihp, ihq]
  | forallE s p ih | existsE s p ih =>
      cases s
      simp only [Reverse.formula, Source.Formula.rename, ih]
      congr 2
      · exact lift_rename_source b r
      · exact free_rename_source f r

theorem term_substitute {sb sf tb tf : Syntax.Ctx} {n} (b : Reverse.Vars tb n) (f : Reverse.Vars tf n)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf)
    {s : SetSort} (t : FirstOrder.Term ℒ sb sf s) :
    Reverse.term b f (t.substituteMapped bs fs) =
      Reverse.term (fun v => Reverse.term b f (bs v)) (fun v => Reverse.term b f (fs v)) t := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app symbol _ => exact nomatch symbol

theorem term_weaken_bound {bound free : Syntax.Ctx} {n} (b : Reverse.Vars bound n)
    (f : Reverse.Vars free n) {s : SetSort} (t : FirstOrder.Term ℒ bound free s) :
    Reverse.term (Reverse.lift b) (fun v => (f v).castSucc) (t.weakenBound SetSort.set) =
      (Reverse.term b f t).castSucc := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app symbol _ => exact nomatch symbol

theorem lift_substitute {sb tb tf : Syntax.Ctx} {n} (b : Reverse.Vars tb n) (f : Reverse.Vars tf n)
    (bs : VariableSubstitution ℒ sb tb tf) :
    (fun {s} (v : Variable (SetSort.set :: sb) s) => Reverse.term (Reverse.lift b)
      (fun v => (f v).castSucc) (VariableSubstitution.liftBound SetSort.set bs v)) =
    @Reverse.lift sb n (fun v => Reverse.term b f (bs v)) := by
  funext s v
  cases v with
  | here => rfl
  | there v => exact term_weaken_bound b f (bs v)

theorem free_lift_substitute {sf tb tf : Syntax.Ctx} {n} (b : Reverse.Vars tb n) (f : Reverse.Vars tf n)
    (fs : VariableSubstitution ℒ sf tb tf) :
    (fun {s} (v : Variable sf s) => Reverse.term (Reverse.lift b) (fun v => (f v).castSucc)
      (VariableSubstitution.weakenBound SetSort.set fs v)) =
    (fun {s} (v : Variable sf s) => (Reverse.term b f (fs v)).castSucc) := by
  funext s v
  exact term_weaken_bound b f (fs v)

theorem formula_substitute {sb sf tb tf : Syntax.Ctx} {n} (b : Reverse.Vars tb n) (f : Reverse.Vars tf n)
    (bs : VariableSubstitution ℒ sb tb tf) (fs : VariableSubstitution ℒ sf tb tf) (p : Syntax.Fm sb sf) :
    Reverse.formula b f (p.substituteMapped bs fs) =
      Reverse.formula (fun v => Reverse.term b f (bs v)) (fun v => Reverse.term b f (fs v)) p := by
  induction p generalizing tb n with
  | falsum | truth => rfl
  | rel s ts =>
      cases s
      match ts with
      | .cons x (.cons y .nil) =>
          simp only [FirstOrder.Formula.substituteMapped, Arguments.substituteMapped, Reverse.formula, term_substitute]
  | equal s t => simp only [FirstOrder.Formula.substituteMapped, Reverse.formula, term_substitute]
  | neg p ih => simp only [FirstOrder.Formula.substituteMapped, Reverse.formula, ih]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [FirstOrder.Formula.substituteMapped, Reverse.formula, ihp, ihq]
  | forallE s p ih | existsE s p ih =>
      cases s
      simp only [FirstOrder.Formula.substituteMapped, Reverse.formula, ih]
      congr 2
      · exact lift_substitute b f bs
      · exact free_lift_substitute b f fs
theorem formula_rename_native {sb sf tb tf : Syntax.Ctx} {n} (b : Reverse.Vars tb n) (f : Reverse.Vars tf n)
    (br : VariableRenaming sb tb) (fr : VariableRenaming sf tf) (p : Syntax.Fm sb sf) :
    Reverse.formula b f (p.renameMapped br fr) =
      Reverse.formula (fun v => b (br v)) (fun v => f (fr v)) p := by
  rw [FirstOrder.Formula.renameMapped_eq_substituteMapped, formula_substitute]
  rfl

theorem empty_unique {n} (v : Reverse.Vars [] n) : @v = @empty n := by
  funext s i
  exact nomatch i

theorem closed_vars {n} (b f : Reverse.Vars [] n) (p : FirstOrder.Sentence ℒ) :
    Reverse.formula b f p = Reverse.formula empty empty p := by
  rw [empty_unique b, empty_unique f]

theorem rename_sentence {n} (p : FirstOrder.Sentence ℒ) :
    Source.Formula.rename (Fin.elim0 : Fin 0 → Fin n) (Reverse.sentence p) =
      Reverse.formula empty empty p := by
  rw [Reverse.sentence, formula_rename_source]
  exact closed_vars _ _ p

theorem fromSentence {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (p : FirstOrder.Sentence ℒ) :
    Reverse.formula empty f p.fromSentence = (Reverse.sentence p).rename Fin.elim0 := by
  rw [rename_sentence]
  cases free with
  | nil =>
      simpa only [FirstOrder.Formula.fromSentence, Renaming.emptyFree, FirstOrder.Formula.rename_id] using
        closed_vars empty f p
  | cons s free =>
      change Reverse.formula empty f (p.renameMapped VariableRenaming.id VariableRenaming.empty) = _
      rw [formula_rename_native]
      exact closed_vars _ _ p

theorem abstract_top {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (p : Syntax.Fm [] (SetSort.set :: free)) :
    Reverse.formula (Reverse.lift (@empty n)) (fun v => (f v).castSucc) p.abstractFreeTop =
      Reverse.formula empty (Reverse.lift f) p := by
  change Reverse.formula _ _ (p.substituteMapped
    (VariableSubstitution.abstractBound (σ := ℒ) (bound := []) (free := free) SetSort.set)
    VariableSubstitution.abstractFreeTop) = _
  rw [formula_substitute]
  congr 1
  · funext s v
    exact nomatch v
  · funext s v
    cases v <;> rfl

theorem forall_top {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (p : Syntax.Fm [] (SetSort.set :: free)) :
    Reverse.formula empty f (p.forallFreeTop SetSort.set) =
      Source.Formula.all (Reverse.formula empty (Reverse.lift f) p) := by
  exact congrArg Source.Formula.all (abstract_top f p)

theorem exists_top {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (p : Syntax.Fm [] (SetSort.set :: free)) :
    Reverse.formula empty f (p.existsFreeTop SetSort.set) =
      Source.Formula.ex (Reverse.formula empty (Reverse.lift f) p) := by
  exact congrArg Source.Formula.ex (abstract_top f p)

theorem weaken_free {free : Syntax.Ctx} {n} (f : Reverse.Vars (SetSort.set :: free) n)
    (p : Syntax.Fm [] free) :
    Reverse.formula empty f (p.weakenFree SetSort.set) =
      Reverse.formula empty (fun v => f (.there v)) p := by
  rw [FirstOrder.Formula.weakenFree_eq_renameMapped, formula_rename_native]
  rfl

theorem fresh_raise {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (p : Syntax.Fm [] free) :
    Reverse.formula empty (Reverse.lift f) (p.weakenFree SetSort.set) =
      (Reverse.formula empty f p).raise := by
  rw [weaken_free, Source.Formula.raise, formula_rename_source]
  congr 1
  · funext s v
    exact nomatch v

theorem instantiate_top {free : Syntax.Ctx} {n} (f : Reverse.Vars free n)
    (p : Syntax.Fm [SetSort.set] free) (t : Syntax.Tm [] free) :
    Reverse.formula empty f (p.instantiateTop t) =
      (Reverse.formula (Reverse.lift (@empty n)) (fun v => (f v).castSucc) p).instantiate
        (Reverse.term empty f t) := by
  change Reverse.formula _ _ (p.substituteMapped (VariableSubstitution.instantiateTop t)
    VariableSubstitution.freeId) = _
  rw [formula_substitute, Source.Formula.instantiate, formula_rename_source]
  congr 1
  · funext s v
    cases v with
    | here => simp only [VariableSubstitution.instantiateTop, Reverse.lift, Fin.lastCases_last]
    | there v => exact nomatch v
  · funext s v
    simp only [VariableSubstitution.freeId, Reverse.term, Fin.lastCases_castSucc, id_eq]

def fill {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (default : Fin n) :
    Reverse.Vars (SetSort.set :: free) n
  | _, .here => default
  | _, .there v => f v

theorem strengthen {free : Syntax.Ctx} {n} (f : Reverse.Vars free n) (default : Fin n)
    (p : Syntax.Fm [] free) :
    Reverse.formula empty (fill f default) (p.weakenFree SetSort.set) =
      Reverse.formula empty f p := by
  rw [weaken_free]
  rfl

theorem substitute_free {sf tf : Syntax.Ctx} {n} (f : Reverse.Vars tf n)
    (fs : VariableSubstitution ℒ sf [] tf) (p : Syntax.Fm [] sf) :
    Reverse.formula empty f (p.substituteFree fs) =
      Reverse.formula empty (fun v => Reverse.term empty f (fs v)) p := by
  change Reverse.formula _ _ (p.substituteMapped VariableSubstitution.boundId fs) = _
  rw [formula_substitute]
  congr 1
end PPAC.Migration.ReverseSubstitution
