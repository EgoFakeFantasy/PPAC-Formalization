import PPAC.Migration.DerivationTransport

/-! 消去原生 truth/neg/iff 的全语法规范化；结论由原 Hilbert 核证明。 -/
namespace PPAC.Migration.Normalization
open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
universe u v w
variable {σ : Signature.{u, v, w}}

def formula {bound free : SortContext σ} : Formula σ bound free → Formula σ bound free
  | .falsum => .falsum
  | .truth => .imp .falsum .falsum
  | .rel r ts => .rel r ts
  | .equal s t => .equal s t
  | .neg p => .imp (formula p) .falsum
  | .conj p q => .conj (formula p) (formula q)
  | .disj p q => .disj (formula p) (formula q)
  | .imp p q => .imp (formula p) (formula q)
  | .iff p q => .conj (.imp (formula p) (formula q)) (.imp (formula q) (formula p))
  | .forallE s p => .forallE s (formula p)
  | .existsE s p => .existsE s (formula p)

theorem substitute {sb sf tb tf : SortContext σ}
    (p : Formula σ sb sf) (bs : VariableSubstitution σ sb tb tf)
    (fs : VariableSubstitution σ sf tb tf) :
    formula (p.substituteMapped bs fs) = (formula p).substituteMapped bs fs := by
  induction p generalizing tb with
  | falsum | truth | rel | equal => rfl
  | neg p ih => simp only [formula, Formula.substituteMapped, ih]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [formula, Formula.substituteMapped, ihp, ihq]
  | forallE s p ih | existsE s p ih =>
      simp only [formula, Formula.substituteMapped, ih]

theorem idempotent {bound free : SortContext σ} (p : Formula σ bound free) :
    formula (formula p) = formula p := by
  induction p with
  | falsum | truth | rel | equal => rfl
  | neg p ih => simp only [formula, ih]
  | conj p q ihp ihq | disj p q ihp ihq | imp p q ihp ihq | iff p q ihp ihq =>
      simp only [formula, ihp, ihq]
  | forallE s p ih | existsE s p ih => simp only [formula, ih]

variable {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}

theorem iff_refl (p : OpenFormula σ free) : Derives T Γ (.iff p p) :=
  .iff_intro (.assumption List.mem_cons_self) (.assumption List.mem_cons_self)

theorem imp_congr {p p' q q' : OpenFormula σ free}
    (hp : Derives T Γ (.iff p p')) (hq : Derives T Γ (.iff q q')) :
    Derives T Γ (.iff (.imp p q) (.imp p' q')) := by
  apply Derives.iff_intro
  · apply Derives.imp_intro
    exact Derives.iff_elim_left hq.context_weaken_cons.context_weaken_cons
      (Derives.imp_elim (Derives.assumption (by simp))
        (Derives.iff_elim_right hp.context_weaken_cons.context_weaken_cons
          (Derives.assumption List.mem_cons_self)))
  · apply Derives.imp_intro
    exact Derives.iff_elim_right hq.context_weaken_cons.context_weaken_cons
      (Derives.imp_elim (Derives.assumption (by simp))
        (Derives.iff_elim_left hp.context_weaken_cons.context_weaken_cons
          (Derives.assumption List.mem_cons_self)))

theorem conj_congr {p p' q q' : OpenFormula σ free}
    (hp : Derives T Γ (.iff p p')) (hq : Derives T Γ (.iff q q')) :
    Derives T Γ (.iff (.conj p q) (.conj p' q')) := by
  apply Derives.iff_intro
  · exact .conj_intro
      (.iff_elim_left hp.context_weaken_cons (.conj_elim_left (.assumption List.mem_cons_self)))
      (.iff_elim_left hq.context_weaken_cons (.conj_elim_right (.assumption List.mem_cons_self)))
  · exact .conj_intro
      (.iff_elim_right hp.context_weaken_cons (.conj_elim_left (.assumption List.mem_cons_self)))
      (.iff_elim_right hq.context_weaken_cons (.conj_elim_right (.assumption List.mem_cons_self)))

theorem disj_congr {p p' q q' : OpenFormula σ free}
    (hp : Derives T Γ (.iff p p')) (hq : Derives T Γ (.iff q q')) :
    Derives T Γ (.iff (.disj p q) (.disj p' q')) := by
  apply Derives.iff_intro
  · exact .disj_elim (.assumption List.mem_cons_self)
      (.disj_intro_left (.iff_elim_left hp.context_weaken_cons.context_weaken_cons
        (.assumption List.mem_cons_self)))
      (.disj_intro_right (.iff_elim_left hq.context_weaken_cons.context_weaken_cons
        (.assumption List.mem_cons_self)))
  · exact .disj_elim (.assumption List.mem_cons_self)
      (.disj_intro_left (.iff_elim_right hp.context_weaken_cons.context_weaken_cons
        (.assumption List.mem_cons_self)))
      (.disj_intro_right (.iff_elim_right hq.context_weaken_cons.context_weaken_cons
        (.assumption List.mem_cons_self)))

theorem iff_trans {p q r : OpenFormula σ free}
    (hpq : Derives T Γ (.iff p q)) (hqr : Derives T Γ (.iff q r)) :
    Derives T Γ (.iff p r) :=
  .iff_intro
    (.iff_elim_left hqr.context_weaken_cons
      (.iff_elim_left hpq.context_weaken_cons (.assumption List.mem_cons_self)))
    (.iff_elim_right hpq.context_weaken_cons
      (.iff_elim_right hqr.context_weaken_cons (.assumption List.mem_cons_self)))

theorem neg_expansion (p : OpenFormula σ free) :
    Derives T Γ (.iff (.neg p) (.imp p .falsum)) := by
  apply Derives.iff_intro
  · apply Derives.imp_intro
    exact .neg_elim (.assumption List.mem_cons_self) (.assumption (by simp))
  · apply Derives.neg_intro
    exact .imp_elim (.assumption (by simp)) (.assumption List.mem_cons_self)

theorem iff_expansion (p q : OpenFormula σ free) :
    Derives T Γ (.iff (.iff p q) (.conj (.imp p q) (.imp q p))) := by
  apply Derives.iff_intro
  · apply Derives.conj_intro
    · exact .imp_intro (.iff_elim_left (.assumption (by simp)) (.assumption List.mem_cons_self))
    · exact .imp_intro (.iff_elim_right (.assumption (by simp)) (.assumption List.mem_cons_self))
  · apply Derives.iff_intro
    · exact .imp_elim (.conj_elim_left (.assumption (formula := .conj (.imp p q) (.imp q p)) (by simp))) (.assumption List.mem_cons_self)
    · exact .imp_elim (.conj_elim_right (.assumption (formula := .conj (.imp p q) (.imp q p)) (by simp))) (.assumption List.mem_cons_self)

theorem forall_congr {s : σ.SortSymbol} {p q : OpenFormula σ (s :: free)}
    (h : Derives T (FreshVariable.extendContext s Γ) (.iff p q)) :
    Derives T Γ (.iff (p.forallFreeTop s) (q.forallFreeTop s)) := by
  apply Derives.iff_intro
  · apply Derives.forall_intro
    apply Derives.iff_elim_left h.context_weaken_cons
    have ha := Derives.forall_elim (Term.newestFree s)
      (Derives.assumption (T := T) (formula := (p.forallFreeTop s).weakenFree s)
        (Γ := FreshVariable.extendContext s (p.forallFreeTop s :: Γ))
        (by simp [FreshVariable.extendContext]))
    simpa only [Formula.forallFreeTop, Formula.weakenFree, Formula.rename,
      Renaming.weakenFree, Renaming.free, VariableRenaming.lift_id,
      FreshVariable.extendContext, List.map_cons,
      Formula.instantiateTop_renameMapped_abstractFreeTop] using ha
  · apply Derives.forall_intro
    apply Derives.iff_elim_right h.context_weaken_cons
    have ha := Derives.forall_elim (Term.newestFree s)
      (Derives.assumption (T := T) (formula := (q.forallFreeTop s).weakenFree s)
        (Γ := FreshVariable.extendContext s (q.forallFreeTop s :: Γ))
        (by simp [FreshVariable.extendContext]))
    simpa only [Formula.forallFreeTop, Formula.weakenFree, Formula.rename,
      Renaming.weakenFree, Renaming.free, VariableRenaming.lift_id,
      FreshVariable.extendContext, List.map_cons,
      Formula.instantiateTop_renameMapped_abstractFreeTop] using ha

theorem exists_congr {s : σ.SortSymbol} {p q : OpenFormula σ (s :: free)}
    (h : Derives T (FreshVariable.extendContext s Γ) (.iff p q)) :
    Derives T Γ (.iff (p.existsFreeTop s) (q.existsFreeTop s)) := by
  apply Derives.iff_intro
  · apply Derives.exists_elim (.assumption List.mem_cons_self)
    apply Derives.exists_intro (Term.newestFree s)
    rw [VariableRenaming.lift_id, Formula.instantiateTop_renameMapped_abstractFreeTop]
    exact .iff_elim_left h.context_weaken_cons.context_weaken_cons (.assumption List.mem_cons_self)
  · apply Derives.exists_elim (.assumption List.mem_cons_self)
    apply Derives.exists_intro (Term.newestFree s)
    rw [VariableRenaming.lift_id, Formula.instantiateTop_renameMapped_abstractFreeTop]
    exact .iff_elim_right h.context_weaken_cons.context_weaken_cons (.assumption List.mem_cons_self)
theorem iff_symm {p q : OpenFormula σ free} (h : Derives T Γ (.iff p q)) :
    Derives T Γ (.iff q p) :=
  .iff_intro (.iff_elim_right h.context_weaken_cons (.assumption List.mem_cons_self))
    (.iff_elim_left h.context_weaken_cons (.assumption List.mem_cons_self))

/-- 全绑定/自由上下文与任意项替换均覆盖；量词步只用原核新鲜变量规则。 -/
theorem equivalent_substitute {bound sourceFree targetFree : SortContext σ}
    (p : Formula σ bound sourceFree)
    (bs : VariableSubstitution σ bound [] targetFree)
    (fs : VariableSubstitution σ sourceFree [] targetFree)
    (T : Theory σ) (Γ : Context σ targetFree) :
    Derives T Γ (.iff (p.substituteMapped bs fs) ((formula p).substituteMapped bs fs)) := by
  induction p generalizing targetFree with
  | falsum | rel | equal => exact iff_refl _
  | truth =>
      exact .iff_intro (Derives.Propositional.imp_refl .falsum) Derives.truth_intro
  | neg p ih =>
      exact iff_trans (neg_expansion _)
        (imp_congr (ih bs fs Γ) (iff_refl .falsum))
  | conj p q ihp ihq => exact conj_congr (ihp bs fs Γ) (ihq bs fs Γ)
  | disj p q ihp ihq => exact disj_congr (ihp bs fs Γ) (ihq bs fs Γ)
  | imp p q ihp ihq => exact imp_congr (ihp bs fs Γ) (ihq bs fs Γ)
  | iff p q ihp ihq =>
      exact iff_trans (iff_expansion _ _)
        (conj_congr (imp_congr (ihp bs fs Γ) (ihq bs fs Γ))
          (imp_congr (ihq bs fs Γ) (ihp bs fs Γ)))
  | forallE s p ih =>
      have h : Derives T (FreshVariable.extendContext s Γ)
          (.iff ((p.substituteMapped (VariableSubstitution.liftBound s bs)
            (VariableSubstitution.weakenBound s fs)).openBoundTop s)
          (((formula p).substituteMapped (VariableSubstitution.liftBound s bs)
            (VariableSubstitution.weakenBound s fs)).openBoundTop s)) := by
        simp only [Formula.openBoundTop, Formula.substituteMapped_comp]
        apply ih
      simpa only [formula, Formula.substituteMapped, Formula.forallFreeTop, Formula.abstractFreeTop_openBoundTop] using
        forall_congr h
  | existsE s p ih =>
      have h : Derives T (FreshVariable.extendContext s Γ)
          (.iff ((p.substituteMapped (VariableSubstitution.liftBound s bs)
            (VariableSubstitution.weakenBound s fs)).openBoundTop s)
          (((formula p).substituteMapped (VariableSubstitution.liftBound s bs)
            (VariableSubstitution.weakenBound s fs)).openBoundTop s)) := by
        simp only [Formula.openBoundTop, Formula.substituteMapped_comp]
        apply ih
      simpa only [formula, Formula.substituteMapped, Formula.existsFreeTop, Formula.abstractFreeTop_openBoundTop] using
        exists_congr h

/-- 真正的对象推导：任意开放公式与其源连接词规范形逻辑等价。 -/
theorem equivalent (p : OpenFormula σ free) : Derives T Γ (.iff p (formula p)) := by
  simpa only [Formula.substituteMapped_id] using
    equivalent_substitute p VariableSubstitution.boundId VariableSubstitution.freeId T Γ

end PPAC.Migration.Normalization
