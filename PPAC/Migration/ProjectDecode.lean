import PPAC.Migration.ProjectSyntax
import PPAC.Migration.Normalization

/-! 将任意自由闭合Project公式回译为源语法，显式展开子集原子。 -/
namespace PPAC.Migration.ProjectDecode
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
attribute [local implicit_reducible] SetTheory.signature
namespace P
export SetTheory.Definitional.Project (Formula Term fo_formula fo_term fo_bound_variable)
end P

def lift {depth n} (ρ : Fin depth → Fin n) : Fin (depth+1) → Fin (n+1) :=
  Fin.cases (Fin.last n) (fun i => (ρ i).castSucc)

def term {depth n} (ρ : Fin depth → Fin n) (t : P.Term depth)
    (h : t.freeSupport = []) : Fin n :=
  match t with
  | .bound i => ρ i
  | .free _ => False.elim (by cases h)

def subset {n} (x y : Fin n) : Source.Formula n :=
  .all ((Source.Formula.mem (Fin.last n) x.castSucc).imp (.mem (Fin.last n) y.castSucc))

def formula {depth n} (ρ : Fin depth → Fin n) (p : P.Formula 1 depth)
    (h : p.FreeClosed) : Source.Formula n :=
  match p with
  | .falsum => .bot
  | .truth => .imp .bot .bot
  | .mem x y => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .mem (term ρ x h.1) (term ρ y h.2)
  | .atom .extensionalEq _ args => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .equal (term ρ (args 0) (h 0)) (term ρ (args 1) (h 1))
  | .atom .subset _ args => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact subset (term ρ (args 0) (h 0)) (term ρ (args 1) (h 1))
  | .neg p => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact (formula ρ p h).neg
  | .conj p q => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .conj (formula ρ p h.1) (formula ρ q h.2)
  | .disj p q => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .disj (formula ρ p h.1) (formula ρ q h.2)
  | .imp p q => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .imp (formula ρ p h.1) (formula ρ q h.2)
  | .iff p q => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact (formula ρ p h.1).iff (formula ρ q h.2)
  | .forallE p => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .all (formula (lift ρ) p h)
  | .existsE p => by
      simp only [Definitional.Formula.FreeClosed] at h
      exact .ex (formula (lift ρ) p h)

theorem lift_inverse {depth n} (ρ : Fin depth → Fin n)
    (τ : Fin n → Variable (SetTheory.Definitional.Project.fo_bound_context depth) SetSort.set)
    (hρ : ∀ i, τ (ρ i) = P.fo_bound_variable i) :
    ∀ i, Translation.lift τ (lift ρ i) = P.fo_bound_variable i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [lift, Fin.cases_zero, Translation.lift, Fin.lastCases_last, P.fo_bound_variable]
  · simp only [lift, Fin.cases_succ, Translation.lift, Fin.lastCases_castSucc, hρ,
      P.fo_bound_variable]

theorem term_inverse {depth n} (ρ : Fin depth → Fin n)
    (τ : Fin n → Variable (SetTheory.Definitional.Project.fo_bound_context depth) SetSort.set)
    (hρ : ∀ i, τ (ρ i) = P.fo_bound_variable i)
    (t : P.Term depth) (h : t.freeSupport = []) :
    (.bvar (τ (term ρ t h)) : Syntax.Tm _ []) = P.fo_term t h := by
  cases t with
  | bound i => simp only [term, P.fo_term, hρ]
  | free i => cases h

/-- 任意参数及深度上的严格AST往返；独立连接词展开，与原核规范化相符。 -/
theorem fo_formula {depth n} (ρ : Fin depth → Fin n)
    (τ : Fin n → Variable (SetTheory.Definitional.Project.fo_bound_context depth) SetSort.set)
    (hρ : ∀ i, τ (ρ i) = P.fo_bound_variable i)
    (p : P.Formula 1 depth) (h : p.FreeClosed) :
    Translation.formula τ (formula ρ p h) = Normalization.formula (P.fo_formula p h) := by
  induction p generalizing n with
  | falsum | truth => simp only [formula, Translation.formula, Normalization.formula, P.fo_formula]
  | mem x y =>
      simp only [formula, Translation.formula, Normalization.formula, P.fo_formula,
        SetTheory.Definitional.Project.fo_mem, term_inverse ρ τ hρ]
  | atom s hs args =>
      simp only [Definitional.Formula.FreeClosed] at h
      cases s with
      | extensionalEq =>
          simp only [formula, Translation.formula, Normalization.formula, P.fo_formula,
            term_inverse ρ τ hρ]
      | subset =>
          simp only [formula, subset, Translation.formula, Normalization.formula, P.fo_formula,
            SetTheory.Definitional.Project.fo_mem, Translation.lift,
            Fin.lastCases_last, Fin.lastCases_castSucc]
          rw [← term_inverse ρ τ hρ (args 0) (h 0), ← term_inverse ρ τ hρ (args 1) (h 1)]
          simp only [Term.weakenBound_bvar]
  | neg p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, Translation.formula, Normalization.formula, P.fo_formula,
        ih ρ τ hρ h]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, Translation.formula, Normalization.formula, P.fo_formula,
        ihp ρ τ hρ h.1, ihq ρ τ hρ h.2]
  | forallE p ih | existsE p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, Translation.formula, Normalization.formula, P.fo_formula,
        ih (lift ρ) (Translation.lift τ) (lift_inverse ρ τ hρ) h]
theorem term_rename_source {depth n m} (ρ : Fin depth → Fin n) (r : Fin n → Fin m)
    (t : P.Term depth) (h : t.freeSupport = []) :
    r (term ρ t h) = term (fun i => r (ρ i)) t h := by
  cases t with
  | bound i => rfl
  | free i => cases h

theorem lift_comp_source {depth n m} (ρ : Fin depth → Fin n) (r : Fin n → Fin m) :
    (fun i => Source.Formula.liftRen r (lift ρ i)) = lift (fun i => r (ρ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [lift, Fin.cases_zero, Fin.cases_succ, Source.Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rename_source {depth n m} (ρ : Fin depth → Fin n) (r : Fin n → Fin m)
    (p : P.Formula 1 depth) (h : p.FreeClosed) :
    Source.Formula.rename r (formula ρ p h) = formula (fun i => r (ρ i)) p h := by
  induction p generalizing n m with
  | falsum | truth | mem =>
      simp only [formula, Source.Formula.rename, term_rename_source]
  | atom s hs args =>
      simp only [Definitional.Formula.FreeClosed] at h
      cases s <;> simp only [formula, subset, Source.Formula.rename, Source.Formula.liftRen,
        Fin.lastCases_last, Fin.lastCases_castSucc, term_rename_source]
  | neg p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, Source.Formula.rename, ih ρ r h]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, Source.Formula.rename, ihp ρ r h.1, ihq ρ r h.2]
  | forallE p ih | existsE p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      simp only [formula, Source.Formula.rename, ih (lift ρ) (Source.Formula.liftRen r) h,
        lift_comp_source]

theorem term_rename_project {d e n} (ρ : Fin e → Fin n) (r : Fin d → Fin e)
    (t : P.Term d) (h : t.freeSupport = []) (hr : (t.rename r).freeSupport = []) :
    term ρ (t.rename r) hr = term (fun i => ρ (r i)) t h := by
  cases t with
  | bound i => rfl
  | free i => cases h

theorem lift_comp_project {d e n} (ρ : Fin e → Fin n) (r : Fin d → Fin e) :
    (fun i => lift ρ (ProjectSyntax.headLift r i)) = lift (fun i => ρ (r i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [lift, ProjectSyntax.headLift, Fin.cases_zero, Fin.cases_succ]

private theorem congr_two {A B C : Type} (f : A → B → C) {a a' : A} {b b' : B}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by
  cases ha
  cases hb
  rfl

theorem rename_project {d e n} (ρ : Fin e → Fin n) (r : Fin d → Fin e)
    (p : P.Formula 1 d) (h : p.FreeClosed) (hr : (p.rename r).FreeClosed) :
    formula ρ (p.rename r) hr = formula (fun i => ρ (r i)) p h := by
  induction p generalizing e n with
  | falsum | truth => simp only [Definitional.Formula.rename, Definitional.Formula.bind, formula]
  | mem x y =>
      simp only [Definitional.Formula.FreeClosed] at h
      have hx := term_rename_project ρ r x h.1
        ((Definitional.Term.freeSupport_rename r x).trans h.1)
      have hy := term_rename_project ρ r y h.2
        ((Definitional.Term.freeSupport_rename r y).trans h.2)
      simpa only [Definitional.Formula.rename, Definitional.Formula.bind, formula,
        Definitional.Term.rename] using congr_two Source.Formula.mem hx hy
  | atom s hs args =>
      simp only [Definitional.Formula.FreeClosed] at h
      have hx := term_rename_project ρ r (args 0) (h 0)
        ((Definitional.Term.freeSupport_rename r (args 0)).trans (h 0))
      have hy := term_rename_project ρ r (args 1) (h 1)
        ((Definitional.Term.freeSupport_rename r (args 1)).trans (h 1))
      cases s with
      | extensionalEq =>
          simpa only [Definitional.Formula.rename, Definitional.Formula.bind, formula,
            Definitional.TermVector.get_bind, Definitional.Term.rename] using
            congr_two Source.Formula.equal hx hy
      | subset =>
          simpa only [Definitional.Formula.rename, Definitional.Formula.bind, formula,
            Definitional.TermVector.get_bind, Definitional.Term.rename] using congr_two subset hx hy
  | neg p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      have hp := (Definitional.Formula.freeClosed_rename r p).mpr h
      simpa only [Definitional.Formula.rename, Definitional.Formula.bind, formula] using
        congrArg (fun q : Source.Formula n => q.neg) (ih ρ r h hp)
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [Definitional.Formula.FreeClosed] at h
      have hp := (Definitional.Formula.freeClosed_rename r p).mpr h.1
      have hq := (Definitional.Formula.freeClosed_rename r q).mpr h.2
      simp only [Definitional.Formula.rename, Definitional.Formula.bind, formula] at *
      rw [ihp ρ r h.1 hp, ihq ρ r h.2 hq]
  | forallE p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      have hp := (Definitional.Formula.freeClosed_rename (ProjectSyntax.headLift r) p).mpr h
      simp only [ProjectSyntax.rename_forall, formula, ih (lift ρ) (ProjectSyntax.headLift r) h hp,
        lift_comp_project]
  | existsE p ih =>
      simp only [Definitional.Formula.FreeClosed] at h
      have hp := (Definitional.Formula.freeClosed_rename (ProjectSyntax.headLift r) p).mpr h
      simp only [ProjectSyntax.rename_exists, formula, ih (lift ρ) (ProjectSyntax.headLift r) h hp,
        lift_comp_project]

theorem lift_reverse {n} : lift (Fin.rev : Fin n → Fin n) = Fin.rev := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [lift, Fin.cases_zero, Fin.cases_succ, Fin.rev_zero, Fin.rev_succ]

def reverse {depth} (p : P.Formula 1 depth) (h : p.FreeClosed) : Source.Formula depth :=
  formula Fin.rev p h

theorem reverse_forall {depth} (p : P.Formula 1 (depth+1)) (h : p.FreeClosed) :
    reverse (.forallE p) (by simpa only [Definitional.Formula.FreeClosed] using h) = .all (reverse p h) := by
  simp only [reverse, formula, lift_reverse]

theorem close_formula {depth} (p : P.Formula 1 depth) (h : p.FreeClosed)
    (hc : (Definitional.Project.Formula.forallClosure depth p).FreeClosed) :
    reverse (Definitional.Project.Formula.forallClosure depth p) hc = (reverse p h).close := by
  induction depth with
  | zero => rfl
  | succ n ih =>
      have ha : (Definitional.Formula.forallE p).FreeClosed := by
        simpa only [Definitional.Formula.FreeClosed] using h
      have hc' : (Definitional.Project.Formula.forallClosure n (.forallE p)).FreeClosed := by
        simpa only [Definitional.Project.Formula.forallClosure, Definitional.Formula.forallClosure] using hc
      have hi := ih (.forallE p) ha hc'
      simpa only [Definitional.Project.Formula.forallClosure, Definitional.Formula.forallClosure,
        reverse, formula, lift_reverse, Source.Formula.close] using hi

theorem closed_fo (p : Definitional.Project.Sentence) :
    Translation.sentence (reverse p.formula p.freeClosed) =
      Normalization.formula (Definitional.Project.fo_sentence p) := by
  exact fo_formula Fin.rev Fin.elim0 (fun i => Fin.elim0 i) p.formula p.freeClosed
end PPAC.Migration.ProjectDecode
