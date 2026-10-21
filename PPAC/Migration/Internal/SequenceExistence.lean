import PPAC.Migration.Internal.SequenceAppend

/-! 在对象ω归纳内取得全部内部长度的实际序列；不止外部标准自然数实例。 -/
namespace PPAC.Migration.Internal.SequenceExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SequenceSyntax

def naturalAppendExists {m} (f n y w : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj ((successor (Fin.last m) n.castSucc).conj
    (appendUnique (Fin.last m) f.castSucc n.castSucc y.castSucc w.castSucc)))

theorem naturalAppendExists_rename {m k} (f n y w : Fin m) (r : Fin m → Fin k) :
    (naturalAppendExists f n y w).rename r = naturalAppendExists (r f) (r n) (r y) (r w) := by
  simp only [naturalAppendExists, Formula.rename, successor_rename, appendUnique_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem induction_base {m} {Γ : Context m} (b : Fin m) :
    Derives Γ (OmegaInductionSyntax.base existenceMatrix (fun _ => b)) := by
  simp only [OmegaInductionSyntax.base, existence_pred, ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.impI
  exact intro_exists (Fin.last m) (Fin.last m) b.castSucc
    (SequenceLogic.empty_sequence (Fin.last m) b.castSucc (.hyp (Or.inl rfl)))

theorem induction_step {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (b y w : Fin m)
    (hy : Derives Γ (.mem y b)) : Derives Γ (OmegaInductionSyntax.step existenceMatrix (fun _ => b) w) := by
  simp only [OmegaInductionSyntax.step, existence_pred, ReplacementPredicates.paramsUp]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := SequenceContext.rename (SequenceContext.rename hA Fin.castSucc) Fin.castSucc
  have hy' : Derives Δ (.mem y.castSucc.castSucc b.castSucc.castSucc) := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hy)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact SequenceAppend.step_from_exists (SequenceContext.add (SequenceContext.add (SequenceContext.add hA' _) _) _)
    (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc b.castSucc.castSucc
    (.hyp (Or.inr (Or.inl rfl))) (add (add (add hy' _) _) _) (.hyp (Or.inl rfl))

theorem all_with_value {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (w b y : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation existenceMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hy : Derives Γ (.mem y b)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (existsSequence (Fin.last m) b.castSucc))) := by
  have hh := OmegaInduction.induction_on_omega existenceMatrix (fun _ => b) w hs hw (induction_base b) (induction_step hA b y w hy)
  simpa only [OmegaInductionSyntax.holds, existence_pred, ReplacementPredicates.paramsUp] using hh

theorem all_inhabited {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (w b : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation existenceMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hb : Derives Γ (MinimalPredicates.inhabited b)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (existsSequence (Fin.last m) b.castSucc))) := by
  let Y := Formula.mem (Fin.last m) b.castSucc
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hb
  apply Derives.exE (p := Y) hb
  have hAY := SequenceContext.under hA Y
  have hsY : Derives Ξ ((Source.SetLanguage.separation existenceMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hs Y
  have hwY : Derives Ξ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  simpa only [Formula.raise, Formula.rename, existsSequence_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc] using all_with_value hAY w.castSucc b.castSucc (Fin.last m) hsY hwY hY

theorem omega_inhabited {m} {Γ : Context m} (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (MinimalPredicates.inhabited w) := by
  have hz := Derives.conjL (.conjL hw)
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  have hout : Derives Ξ (MinimalPredicates.inhabited w.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjL hZ
  simpa only [Formula.raise, MinimalPredicates.inhabited_rename] using hout

theorem all_natural {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (w : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation existenceMatrix).rename Fin.elim0)) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (existsSequence (Fin.last m) w.castSucc))) :=
  all_inhabited hA w w hs hw (omega_inhabited w hw)

theorem natural_append {m} {Γ : Context m} (hA : SequenceContext.Evidence Γ) (f n y w : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f n w))
    (hn : Derives Γ (.mem n w)) (hy : Derives Γ (.mem y w)) : Derives Γ (naturalAppendExists f n y w) := by
  have hk := Derives.impE (step_at w n (.conjL hw)) hn
  let K := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) n.castSucc)
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at hk
  apply Derives.exE (p := K) hk
  have hAK := SequenceContext.under hA K
  have hfK : Derives Ξ (sequence f.castSucc n.castSucc w.castSucc) := by
    simpa only [Formula.raise, sequence_rename] using under hf K
  have hyK : Derives Ξ (.mem y.castSucc w.castSucc) := under hy K
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have ha := SequenceAppend.exists_unique hAK (Fin.last m) f.castSucc n.castSucc y.castSucc w.castSucc hfK hyK (.conjR hK)
  have hout : Derives Ξ (naturalAppendExists f.castSucc n.castSucc y.castSucc w.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, successor_rename, appendUnique_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hK) (.conjI (.conjR hK) ha)
  simpa only [Formula.raise, naturalAppendExists_rename] using hout
end PPAC.Migration.Internal.SequenceExistence
