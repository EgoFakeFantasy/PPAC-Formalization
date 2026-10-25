import PPAC.Migration.SourceQuantifiers
import PPAC.Migration.TheoryTransport

/-!
Constructible-interpretation logical obligation: restrict quantifiers to a
parameter-free pure unary formula D. This is a syntactic, formula-indexed
translation, not an internal truth predicate. The input 19 rules are compiled
to the unchanged original kernel by TheoryTransport.

This module does not define L, prove the interpreted ZF/Choice axioms, or prove
correctness on arbitrary internal proof codes. Those remain separate obligations.
-/
namespace PPAC.Migration.Relativization
open Source SourceAlgebra SourceLogic

def domain {n} (D : Formula 1) (x : Fin n) : Formula n :=
  D.rename (fun _ => x)

def formula (D : Formula 1) : {n : Nat} → Formula n → Formula n
  | _, .bot => .bot
  | _, .mem x y => .mem x y
  | _, .equal x y => .equal x y
  | _, .imp p q => .imp (formula D p) (formula D q)
  | _, .conj p q => .conj (formula D p) (formula D q)
  | _, .disj p q => .disj (formula D p) (formula D q)
  | n, .all p => .all ((domain D (Fin.last n)).imp (formula D p))
  | n, .ex p => .ex ((domain D (Fin.last n)).conj (formula D p))

theorem domain_rename {n m} (D : Formula 1) (x : Fin n) (ρ : Fin n → Fin m) :
    (domain D x).rename ρ = domain D (ρ x) := by
  simp only [domain, rename_comp]

theorem formula_rename {n m} (D : Formula 1) (p : Formula n) (ρ : Fin n → Fin m) :
    formula D (p.rename ρ) = (formula D p).rename ρ := by
  induction p generalizing m with
  | bot | mem | equal => rfl
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [Formula.rename, formula, ihp, ihq]
  | all p ih | ex p ih =>
      simp only [Formula.rename, formula, ih, domain_rename,
        Formula.liftRen, Fin.lastCases_last]

theorem formula_raise {n} (D : Formula 1) (p : Formula n) :
    formula D p.raise = (formula D p).raise := formula_rename D p Fin.castSucc

theorem formula_instantiate {n} (D : Formula 1) (p : Formula (n+1)) (x : Fin n) :
    formula D (p.instantiate x) = (formula D p).instantiate x := by
  unfold Formula.instantiate
  exact formula_rename D p _

/-- All free variables of the input derivation are supplied inside D.
The arbitrary target context supplies proofs of hypotheses, rather than adding
axioms. In particular, eigenvariable domains occur only under their own binders. -/
theorem derives (D : Formula 1) {n} {Γ : Context n} {p : Formula n}
    (d : Derives Γ p) {m} (ρ : Fin n → Fin m) {Δ : Context m}
    (hΓ : ∀ q, Γ q → Derives Δ ((formula D q).rename ρ))
    (hD : ∀ x, Derives Δ (domain D (ρ x))) :
    Derives Δ ((formula D p).rename ρ) := by
  induction d generalizing m with
  | hyp hp => exact hΓ _ hp
  | weaken hsub d ih => exact ih ρ (fun q hq => hΓ q (hsub q hq)) hD
  | @impI n Γ p q d ih =>
      apply Derives.impI
      apply ih ρ
      · intro r hr
        rcases hr with rfl | hr
        · exact .hyp (Or.inl rfl)
        · exact add (hΓ r hr) _
      · intro x; exact add (hD x) _
  | impE dpq dp ihpq ihp => exact .impE (ihpq ρ hΓ hD) (ihp ρ hΓ hD)
  | botE d ih => exact .botE (ih ρ hΓ hD)
  | @classical n Γ p d ih =>
      apply Derives.classical
      apply ih ρ
      · intro q hq
        rcases hq with rfl | hq
        · exact .hyp (Or.inl rfl)
        · exact add (hΓ q hq) _
      · intro x; exact add (hD x) _
  | conjI dp dq ihp ihq => exact .conjI (ihp ρ hΓ hD) (ihq ρ hΓ hD)
  | conjL d ih => exact .conjL (ih ρ hΓ hD)
  | conjR d ih => exact .conjR (ih ρ hΓ hD)
  | disjL d ih => exact .disjL (ih ρ hΓ hD)
  | disjR d ih => exact .disjR (ih ρ hΓ hD)
  | @disjE n Γ p q r dpq dpr dqr ihpq ihpr ihqr =>
      apply Derives.disjE (ihpq ρ hΓ hD)
      · apply ihpr ρ
        · intro s hs
          rcases hs with rfl | hs
          · exact .hyp (Or.inl rfl)
          · exact add (hΓ s hs) _
        · intro x; exact add (hD x) _
      · apply ihqr ρ
        · intro s hs
          rcases hs with rfl | hs
          · exact .hyp (Or.inl rfl)
          · exact add (hΓ s hs) _
        · intro x; exact add (hD x) _
  | @allI n Γ p d ih =>
      simp only [formula, Formula.rename, domain_rename, Formula.liftRen, Fin.lastCases_last]
      apply Derives.allI
      apply Derives.impI
      apply ih (Formula.liftRen ρ)
      · rintro q ⟨r, hr, rfl⟩
        simpa only [formula_raise, rename_raise] using
          under (hΓ r hr) (domain D (Fin.last m))
      · intro x
        refine Fin.lastCases ?_ (fun i => ?_) x
        · simpa only [Formula.liftRen, Fin.lastCases_last] using
            (Derives.hyp (Γ := Context.add (domain D (Fin.last m)) (Context.image Formula.raise Δ)) (Or.inl rfl))
        · simpa only [Formula.liftRen, Fin.lastCases_castSucc, Fin.lastCases_last, domain_rename] using
            under (hD i) (domain D (Fin.last m))
  | @allE n Γ p t d ih =>
      have hall := ih ρ hΓ hD
      have hi := Derives.allE (ρ t) hall
      have hp : Derives Δ ((domain D (ρ t)).imp (((formula D p).rename (Formula.liftRen ρ)).instantiate (ρ t))) := by
        simpa only [formula, Formula.rename, Formula.instantiate, domain_rename,
          Formula.liftRen, Fin.lastCases_last] using hi
      simpa only [formula_instantiate, instantiate_rename] using Derives.impE hp (hD t)
  | @exI n Γ p t d ih =>
      apply Derives.exI (ρ t)
      apply Derives.conjI
      · simpa only [Formula.instantiate, domain_rename, Formula.liftRen, Fin.lastCases_last] using hD t
      · change Derives Δ (((formula D p).rename (Formula.liftRen ρ)).instantiate (ρ t))
        rw [instantiate_rename]
        simpa only [formula_instantiate] using ih ρ hΓ hD
  | @exE n Γ p q dex dcase ihex ihcase =>
      apply Derives.exE (p := ((domain D (Fin.last m)).conj ((formula D p).rename (Formula.liftRen ρ))))
      · simpa only [formula, Formula.rename, domain_rename, Formula.liftRen, Fin.lastCases_last] using ihex ρ hΓ hD
      · have hb := ihcase (Formula.liftRen ρ) (Δ := Context.add
            ((domain D (Fin.last m)).conj ((formula D p).rename (Formula.liftRen ρ)))
            (Context.image Formula.raise Δ)) (by
          intro r hr
          rcases hr with rfl | ⟨s, hs, rfl⟩
          · exact .conjR (.hyp (Or.inl rfl))
          · simpa only [formula_raise, rename_raise] using under (hΓ s hs) _)
          (by
            intro x
            refine Fin.lastCases ?_ (fun i => ?_) x
            · simpa only [Formula.liftRen, Fin.lastCases_last] using
                (Derives.conjL (Derives.hyp (Γ := Context.add
                  ((domain D (Fin.last m)).conj ((formula D p).rename (Formula.liftRen ρ)))
                  (Context.image Formula.raise Δ)) (Or.inl rfl)))
            · simpa only [Formula.liftRen, Fin.lastCases_castSucc, domain_rename] using under (hD i) _)
        simpa only [formula_raise, rename_raise] using hb
  | eqRefl t => exact .eqRefl (ρ t)
  | @eqSubst n Γ s t p deq dp iheq ihp =>
      have hp : Derives Δ (((formula D p).rename (Formula.liftRen ρ)).instantiate (ρ s)) := by
        simpa only [formula_instantiate, instantiate_rename] using ihp ρ hΓ hD
      simpa only [formula_instantiate, instantiate_rename] using
        Derives.eqSubst ((formula D p).rename (Formula.liftRen ρ)) (iheq ρ hΓ hD) hp
  | @rename n k Γ p r d ih =>
      simp only [formula_rename, rename_comp]
      apply ih (fun i => ρ (r i))
      · intro q hq
        simpa only [formula_rename, rename_comp] using hΓ (q.rename r) ⟨q, hq, rfl⟩
      · intro x; exact hD (r x)

/-- The interpreted axiom theory contains each translated input axiom. -/
def theory (D : Formula 1) (T : Theory) : Theory :=
  fun q => ∃ p, T p ∧ q = formula D p

theorem sentence_rename {m} (p : Sentence) (ρ : Fin 0 → Fin m) :
    p.rename ρ = p.rename Fin.elim0 := by
  congr 1
  funext i
  exact Fin.elim0 i

theorem axiom_closed (D : Formula 1) {T : Theory} {p : Sentence} (hp : T p) :
    Derives ((theory D T).at 0) (formula D p) := by
  have h : Derives ((theory D T).at 0) ((formula D p).rename Fin.elim0) :=
    .hyp ⟨formula D p, ⟨p, hp, rfl⟩, rfl⟩
  have he : (Fin.elim0 : Fin 0 → Fin 0) = id := by
    funext i
    exact Fin.elim0 i
  simpa only [he, Reverse.source_rename_id] using h

theorem domain_one (D : Formula 1) : domain D (0 : Fin 1) = D := by
  unfold domain
  have he : (fun _ : Fin 1 => (0 : Fin 1)) = id := by
    funext i
    exact Subsingleton.elim _ _
  rw [he, Reverse.source_rename_id]

/-- Close every externally finite proof, including proofs with unused free
variables. One internal witness in D suffices for all of them; no choice is
used. Nonemptiness remains an explicit object antecedent until the actual
constructible-domain theorem supplies it. -/
theorem source_closed_at (D : Formula 1) {T : Theory} {n} {p : Sentence}
    (d : Derives (T.at n) (p.rename Fin.elim0)) :
    Derives ((theory D T).at 0) ((Formula.ex D).imp (formula D p)) := by
  apply Derives.impI
  apply Derives.exE (p := D) (Derives.hyp (Or.inl rfl))
  have h := derives D d (fun _ => (0 : Fin 1))
    (Δ := Context.add D (Context.image Formula.raise
      (Context.add (.ex D) ((theory D T).at 0)))) (by
        rintro q ⟨a, ha, rfl⟩
        have hs := under (add (axiom_closed D ha) (.ex D)) D
        simpa only [formula_rename, closed_rename, Formula.raise, sentence_rename] using hs)
      (by
        intro x
        rw [domain_one]
        exact .hyp (Or.inl rfl))
  simpa only [formula_rename, closed_rename, Formula.raise, sentence_rename] using h

/-- Actual original-kernel closed derivation, not semantic satisfaction or a
host consistency claim. The interpreted axioms are explicit in the theory. -/
theorem kernel_certificate (D : Formula 1) {T : Theory} {n} {p : Sentence}
    (d : Derives (T.at n) (p.rename Fin.elim0)) :
    YesMetaZFC.Logic.FirstOrder.Derives
      (TheoryTransport.theory (theory D T)) []
      (Translation.sentence ((Formula.ex D).imp (formula D p))) :=
  TheoryTransport.sentence (source_closed_at D d)

end PPAC.Migration.Relativization
