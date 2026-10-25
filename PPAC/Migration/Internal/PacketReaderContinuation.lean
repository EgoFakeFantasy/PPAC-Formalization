import PPAC.Migration.Internal.PacketReaderArithmetic

/-! The original high-byte update uses the unbounded natural difference B+d=byte; all witnesses remain internal. -/
namespace PPAC.Migration.Internal.PacketReaderContinuation
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStepSyntax HornBinderSyntax
open PacketAffineSyntax (equation equation_rename)
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open SyntaxRenameQuerySyntax (of_eq)

def resultBody {m} (w B b v s : Fin m) : Formula (m+2) :=
  (Formula.mem (slot 2 0) (old 2 w)).conj ((Formula.mem (slot 2 1) (old 2 w)).conj
    (continuation (old 2 w) (old 2 B) (old 2 b) (old 2 v) (old 2 s) (slot 2 0) (slot 2 1)))
def existsResult {m} (w B b v s : Fin m) : Formula m := existsMany 2 (resultBody w B b v s)

theorem resultBody_lift {m k} (w B b v s : Fin m) (ρ : Fin m → Fin k) :
    (resultBody w B b v s).rename (lift 2 ρ) = resultBody (ρ w) (ρ B) (ρ b) (ρ v) (ρ s) := by
  simp only [resultBody,Formula.rename,continuation_rename,lift_old,lift_slot]
theorem existsResult_rename {m k} (w B b v s : Fin m) (ρ : Fin m → Fin k) :
    (existsResult w B b v s).rename ρ = existsResult (ρ w) (ρ B) (ρ b) (ρ v) (ρ s) := by
  simp only [existsResult,existsMany_rename,resultBody_lift]

theorem intro_continuation {m} {Γ : Context m} (w B b v s y q d : Fin m)
    (hd : Derives Γ (.mem d w)) (hb : Derives Γ (sum w B d b))
    (hy : Derives Γ (equation w d v s y)) (hq : Derives Γ (product w s B q)) :
    Derives Γ (continuation w B b v s y q) := by
  apply Derives.exI d
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,sum_rename,equation_rename,product_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
    (.conjI hd (.conjI hb (.conjI hy hq)))

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B b v s y q : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hv : Derives Γ (.mem v w))
    (hc : Derives Γ (continuation w B b v s y q)) :
    Derives Γ ((more B b).conj ((Formula.mem y w).conj (.mem q w))) := by
  let D := (Formula.mem (Fin.last m) w.castSucc).conj
    ((sum w.castSucc B.castSucc (Fin.last m) b.castSucc).conj
      ((equation w.castSucc (Fin.last m) v.castSucc s.castSucc y.castSucc).conj (product w.castSucc s.castSucc B.castSucc q.castSucc)))
  let Δ := Context.add D (Context.image Formula.raise Γ)
  apply Derives.exE (p := D) hc
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  have hdiff := NaturalDifferenceSyntax.intro_difference _ _ _ _ (.conjL hD) (.conjL (.conjR hD))
  have hl := NaturalDifference.below_of_exists hZ1 _ _ _ hw1 (under hB D) hdiff
  exact .conjI hl (.conjI
    (PacketReaderArithmetic.equation_range hZ1 _ _ _ _ _ hw1 (under hv D) (.conjL (.conjR (.conjR hD))))
    (ZFArithmetic.mul_range hZ1 _ _ _ _ hw1 (.conjR (.conjR (.conjR hD)))))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B b v s y q t u : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hs : Derives Γ (.mem s w))
    (hc : Derives Γ (continuation w B b v s y q)) (ht : Derives Γ (continuation w B b v s t u)) :
    Derives Γ ((Formula.equal y t).conj (.equal q u)) := by
  let D := (Formula.mem (Fin.last m) w.castSucc).conj
    ((sum w.castSucc B.castSucc (Fin.last m) b.castSucc).conj
      ((equation w.castSucc (Fin.last m) v.castSucc s.castSucc y.castSucc).conj (product w.castSucc s.castSucc B.castSucc q.castSucc)))
  let Δ := Context.add D (Context.image Formula.raise Γ)
  apply Derives.exE (p := D) hc
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  have ht1 := of_eq (continuation_rename w B b v s t u Fin.castSucc) (under ht D)
  let E := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    ((sum w.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc).conj
      ((equation w.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc s.castSucc.castSucc t.castSucc.castSucc).conj
        (product w.castSucc.castSucc s.castSucc.castSucc B.castSucc.castSucc u.castSucc.castSucc)))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) ht1
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 E
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E)
  have hB2 : Derives Ξ (.mem B.castSucc.castSucc w.castSucc.castSucc) := under (under hB D) E
  have hs2 : Derives Ξ (.mem s.castSucc.castSucc w.castSucc.castSucc) := under (under hs D) E
  have hd2 : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under (.conjL hD) E
  have hb2 := of_eq (sum_rename w.castSucc B.castSucc (Fin.last m) b.castSucc Fin.castSucc) (under (.conjL (.conjR hD)) E)
  have hy2 := of_eq (equation_rename w.castSucc (Fin.last m) v.castSucc s.castSucc y.castSucc Fin.castSucc) (under (.conjL (.conjR (.conjR hD))) E)
  have hq2 := of_eq (product_rename w.castSucc s.castSucc B.castSucc q.castSucc Fin.castSucc) (under (.conjR (.conjR (.conjR hD))) E)
  have he := NaturalDifference.unique hZ2 _ _ _ _ _ hw2 hB2 hd2 (.conjL hE) hb2 (.conjL (.conjR hE))
  have hEq := PacketReaderArithmetic.equation_digit _ _ _ _ _ _ (eq_symm he) (.conjL (.conjR (.conjR hE)))
  exact .conjI (PacketAffineCore.equation_unique hZ2 _ _ _ _ _ _ hw2 hd2 hs2 hy2 hEq)
    (ZFArithmetic.mul_unique hZ2 _ _ _ _ _ hw2 hs2 hB2 hq2 (.conjR (.conjR (.conjR hE))))

theorem exists_update {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B b v s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hb : Derives Γ (.mem b w))
    (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w)) (hm : Derives Γ (more B b)) :
    Derives Γ (existsResult w B b v s) := by
  let D := NaturalDifferenceSyntax.witness w.castSucc B.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add D (Context.image Formula.raise Γ)
  apply Derives.exE (p := D) (NaturalDifference.exists_of_below hZ w B b hw hB hb hm)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (equation w.castSucc.castSucc (Fin.last m).castSucc v.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add Y (Context.image Formula.raise Δ)
  apply Derives.exE (p := Y) (PacketReaderArithmetic.exists_equation hZ1 _ _ _ _ hw1 (.conjL hD) (under hv D) (under hs D))
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Y
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
  let Q := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (product w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Θ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) (ZFArithmetic.mul_exists hZ2 _ _ _ hw2 (under (under hs D) Y) (under (under hB D) Y))
  have hQ : Derives Θ Q := .hyp (Or.inl rfl)
  have hd3 : Derives Θ (.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc) := under (under (.conjL hD) Y) Q
  have hb2 := of_eq (sum_rename w.castSucc B.castSucc (Fin.last m) b.castSucc Fin.castSucc) (under (.conjR hD) Y)
  have hb3 := of_eq (sum_rename w.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc Fin.castSucc) (under hb2 Q)
  have hy3 := of_eq (equation_rename w.castSucc.castSucc (Fin.last m).castSucc v.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc) (under (.conjR hY) Q)
  have hc := intro_continuation _ _ _ _ _ _ _ _ hd3 hb3 hy3 (.conjR hQ)
  have hyN : Derives Θ (.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc) := under (.conjL hY) Q
  have hout : Derives Θ (existsResult w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (Fin.last (m+1)).castSucc (Fin.last (m+2)))
    exact of_eq (by simp only [resultBody,Formula.rename,continuation_rename,assign_old,assign_slot]; rfl) (.conjI hyN (.conjI (.conjL hQ) hc))
  simpa only [Formula.raise,existsResult_rename] using hout

end PPAC.Migration.Internal.PacketReaderContinuation
