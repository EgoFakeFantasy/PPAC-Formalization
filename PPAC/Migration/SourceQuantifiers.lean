import PPAC.Migration.SourcePropositional

/-! 原核量词/等词逻辑模式的源19规则证书。 -/
namespace PPAC.Migration.SourceQuantifiers
open Source SourceAlgebra SourceLogic

theorem newest_raise_instance {n} (p : Formula (n+1)) :
    (p.rename (Formula.liftRen (Fin.castSucc : Fin n → Fin (n+1)))).instantiate (Fin.last n) = p := by
  rw [Formula.instantiate, rename_comp]
  have h : (fun i => Fin.lastCases (Fin.last n) id (Formula.liftRen Fin.castSucc i)) =
      (id : Fin (n+1) → Fin (n+1)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  rw [h, Reverse.source_rename_id]

theorem all_newest {n} {Γ : Context (n+1)} {p : Formula (n+1)}
    (h : Derives Γ ((Formula.all p).raise)) : Derives Γ p := by
  have hi := Derives.allE (Fin.last n) h
  simpa only [Formula.raise, Formula.rename, newest_raise_instance] using hi

theorem forall_specialization {n} {Γ : Context n} (p : Formula (n+1)) (t : Fin n) :
    Derives Γ ((Formula.all p).imp (p.instantiate t)) := .impI (.allE t (.hyp (Or.inl rfl)))

theorem forall_distribution {n} {Γ : Context n} (p q : Formula (n+1)) :
    Derives Γ ((Formula.all (p.imp q)).imp ((Formula.all p).imp (.all q))) := by
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (.all p) (Context.add (.all (p.imp q)) Γ)
  have hpq : Derives Δ (.all (p.imp q)) := .hyp (Or.inr (Or.inl rfl))
  have hp : Derives Δ (.all p) := .hyp (Or.inl rfl)
  apply Derives.allI
  exact .impE (all_newest (.rename Fin.castSucc hpq)) (all_newest (.rename Fin.castSucc hp))

theorem vacuous_forall {n} {Γ : Context n} (p : Formula n) :
    Derives Γ (p.imp (.all p.raise)) := .impI (.allI (.rename Fin.castSucc (.hyp (Or.inl rfl))))

theorem exists_introduction {n} {Γ : Context n} (p : Formula (n+1)) (t : Fin n) :
    Derives Γ ((p.instantiate t).imp (.ex p)) := .impI (.exI t (.hyp (Or.inl rfl)))

theorem exists_elimination {n} {Γ : Context n} (p : Formula (n+1)) (q : Formula n) :
    Derives Γ ((Formula.all (p.imp q.raise)).imp ((Formula.ex p).imp q)) := by
  apply Derives.impI
  apply Derives.impI
  let Δ := Context.add (.ex p) (Context.add (.all (p.imp q.raise)) Γ)
  have he : Derives Δ (.ex p) := .hyp (Or.inl rfl)
  have hu : Derives Δ (.all (p.imp q.raise)) := .hyp (Or.inr (Or.inl rfl))
  apply Derives.exE he
  exact .impE (all_newest (under hu p)) (.hyp (Or.inl rfl))

theorem equality_substitution {n} {Γ : Context n} (p : Formula (n+1)) (s t : Fin n) :
    Derives Γ ((Formula.equal s t).imp ((p.instantiate s).imp (p.instantiate t))) :=
  .impI (.impI (.eqSubst p (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))))
end PPAC.Migration.SourceQuantifiers
