import PPAC.Migration.IterationStep

/-! 四参数公式的实际对象ω归纳：两条轨迹在每个内部共同位置相容。 -/
namespace PPAC.Migration.IterationInduction
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax IterationSyntax OmegaInductionSyntax
open ReplacementPredicates (paramsUp)

theorem agreement_base {m} {Γ : Context m} (f g d e z a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hz : Derives Γ (empty z)) (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a)) :
    Derives Γ (base agreementMatrix (args4 f g d e)) := by
  simp only [base, agreement_pred, paramsUp]
  change Derives Γ (.all ((empty (Fin.last m)).imp
    (commonAt f.castSucc g.castSucc d.castSucc e.castSucc (Fin.last m))))
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  have hf' : Derives (Context.image Formula.raise Γ) (track f.castSucc d.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, track_rename] using Derives.rename Fin.castSucc hf
  have hg' : Derives (Context.image Formula.raise Γ) (track g.castSucc e.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, track_rename] using Derives.rename Fin.castSucc hg
  apply Derives.impI
  have hr : Derives (Context.add (empty (Fin.last m)) (Context.image Formula.raise Γ))
      (agreesAt f.castSucc g.castSucc (Fin.last m)) :=
    IterationValues.zero_agrees f.castSucc g.castSucc d.castSucc e.castSucc z.castSucc a.castSucc (Fin.last m)
      (add he' _) (add hz' _) (.hyp (Or.inl rfl)) (add hf' _) (add hg' _)
  exact .impI (.impI (add (add hr _) _))

theorem agreement_step {m} {Γ : Context m} (f g d e z a w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a))
    (hd : Derives Γ (transitive d)) (hc : Derives Γ (transitive e)) :
    Derives Γ (step agreementMatrix (args4 f g d e) w) := by
  simp only [step, agreement_pred, paramsUp]
  change Derives Γ (.all (.all ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).imp
    ((commonAt f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc).imp
      ((successor (Fin.last (m+1)) (Fin.last m).castSucc).imp
        (commonAt f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1))))))))
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hf' : Derives Δ (track f.castSucc.castSucc d.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, track_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hg' : Derives Δ (track g.castSucc.castSucc e.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, track_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hd' : Derives Δ (transitive d.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hd)
  have hc' : Derives Δ (transitive e.castSucc.castSucc) := by
    simpa only [Formula.raise, transitive_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact IterationStep.successor_common f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc
    z.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add (add (add he' _) _) _) (add (add (add hf' _) _) _) (add (add (add hg' _) _) _)
    (add (add (add hd' _) _) _) (add (add (add hc' _) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_common {m} {Γ : Context m} (f g d e z a w : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hf : Derives Γ (track f d z a)) (hg : Derives Γ (track g e z a))
    (hd : Derives Γ (transitive d)) (hc : Derives Γ (transitive e)) :
    Derives Γ (allCommon f g d e w) := by
  have hi := OmegaInduction.induction_on_omega agreementMatrix (args4 f g d e) w hs hw
    (agreement_base f g d e z a he hz hf hg) (agreement_step f g d e z a w he hf hg hd hc)
  simpa only [allCommon, holds, agreement_pred, paramsUp, args4_0, args4_1, args4_2, args4_3] using hi

theorem common_at {m} {Γ : Context m} (f g d e w x : Fin m)
    (hh : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp
      (commonAt f.castSucc g.castSucc d.castSucc e.castSucc (Fin.last m)))))
    (hx : Derives Γ (.mem x w)) : Derives Γ (commonAt f g d e x) := by
  have hi := Derives.allE x hh
  have hr : Derives Γ ((Formula.mem x w).imp (commonAt f g d e x)) := by
    simpa only [Formula.instantiate, Formula.rename, commonAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact .impE hr hx
end PPAC.Migration.IterationInduction
