import PPAC.Migration.Internal.HornBinderSyntax

/-! 有限存在块由锁定源规则实际引入和消去；见证始终留在对象量词中。 -/
namespace PPAC.Migration.Internal.HornBinderRules
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem under_many {m} {Γ : Context m} {p : Formula m} (n : Nat) (hp : Derives Γ p) :
    Derives (raisedContext n Γ) (p.rename (old n)) := by
  induction n with
  | zero => exact of_eq (Reverse.source_rename_id p).symm hp
  | succ n ih => exact of_eq (raise_old n p) (Derives.rename Fin.castSucc ih)

theorem zf_many {m} {Γ : Context m} (n : Nat) (hZ : ZFContext.Evidence Γ) :
    ZFContext.Evidence (raisedContext n Γ) := by
  induction n with
  | zero => exact hZ
  | succ n ih => exact ZFContext.rename ih Fin.castSucc

theorem under_body {m} {Γ : Context m} {p : Formula m} (n : Nat) (hp : Derives Γ p) (B : Formula (m+n)) :
    Derives (Context.add B (raisedContext n Γ)) (p.rename (old n)) := add (under_many n hp) B

theorem zf_body {m} {Γ : Context m} (n : Nat) (hZ : ZFContext.Evidence Γ) (B : Formula (m+n)) :
    ZFContext.Evidence (Context.add B (raisedContext n Γ)) := ZFContext.add (zf_many n hZ) B

theorem intro_many {m} {Γ : Context m} (n : Nat) (B : Formula (m+n)) (env : Fin n → Fin m)
    (hb : Derives Γ (B.rename (assign n env))) : Derives Γ (existsMany n B) := by
  induction n with
  | zero => exact of_eq (Reverse.source_rename_id B) hb
  | succ n ih =>
    apply ih (.ex B) (fun i => env i.castSucc)
    apply Derives.exI (env (Fin.last n))
    exact of_eq (by
      rw [Formula.instantiate, rename_comp]
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [assign, Formula.liftRen]) hb

theorem eliminate_many {m} {Γ : Context m} (n : Nat) (B : Formula (m+n)) (p : Formula m)
    (he : Derives Γ (existsMany n B))
    (hc : Derives (Context.add B (raisedContext n Γ)) (p.rename (old n))) : Derives Γ p := by
  induction n with
  | zero => exact of_eq (Reverse.source_rename_id p) (.impE (.impI hc) he)
  | succ n ih =>
    apply ih (.ex B) he
    let Ξ := Context.add (.ex B) (raisedContext n Γ)
    apply Derives.exE (Derives.hyp (Γ := Ξ) (Or.inl rfl))
    apply of_eq (raise_old n p).symm
    refine Derives.weaken ?_ hc
    rintro q (hb | ⟨s, hs, hq⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨s, Or.inr hs, hq⟩

end PPAC.Migration.Internal.HornBinderRules
