import PPAC.Migration.Internal.ObjectPacketReaderRecursion

/-! Actual continuation arithmetic preserves value + token * scale on all internal naturals. Every product/sum witness is eliminated in the equation-level theorem. -/
namespace PPAC.Migration.Internal.PacketReaderAffineCompose
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open PacketAffineSyntax (equation equation_rename equationBody intro_equation)
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n v s v1 s1 out p h t r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d w))
    (hk : Derives Γ (.mem k w)) (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w))
    (hBP : Derives Γ (product w B k p)) (hN : Derives Γ (sum w d p n))
    (hD : Derives Γ (product w d s h)) (hV : Derives Γ (sum w v h v1))
    (hScale : Derives Γ (product w s B s1)) (hT : Derives Γ (product w k s1 t))
    (hOut : Derives Γ (sum w v1 t out)) (hR : Derives Γ (sum w h t r)) :
    Derives Γ (equation w n v s out) := by
  have hpN := mul_range hZ w B k p hw hBP
  have hhN := mul_range hZ w d s h hw hD
  have htN := mul_range hZ w k s1 t hw hT
  have hs1N := mul_range hZ w s B s1 hw hScale
  have hnN := add_range hZ w d p n hw hd hN
  have hSD := NaturalMultiplicationCommutative.commute hZ w d s h hw hd hs hD
  have hTK := NaturalMultiplicationCommutative.commute hZ w k s1 t hw hk hs1N hT
  have hSP := NaturalMultiplicationAssociative.associate hZ w s B s1 k p t hw hs hB hk hScale hBP hTK
  have hSN := NaturalMultiplicationDistributive.distribute hZ w s d h p n t r hw hs hd hpN hSD hN hSP hR
  have hNS := NaturalMultiplicationCommutative.commute hZ w s n r hw hs hnN hSN
  have hVR := add_associate hZ w v h v1 t r out hw hv hhN htN hV hR hOut
  exact intro_equation w n v s out r hNS hVR

theorem from_witnesses {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n v s v1 s1 out p h t : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d w))
    (hk : Derives Γ (.mem k w)) (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w))
    (hBP : Derives Γ (product w B k p)) (hN : Derives Γ (sum w d p n))
    (hD : Derives Γ (product w d s h)) (hV : Derives Γ (sum w v h v1))
    (hScale : Derives Γ (product w s B s1)) (hT : Derives Γ (product w k s1 t))
    (hOut : Derives Γ (sum w v1 t out)) : Derives Γ (equation w n v s out) := by
  have hhN := mul_range hZ w d s h hw hD
  have htN := mul_range hZ w k s1 t hw hT
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc h.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (add_exists hZ w h t hw hhN htN)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hBP1 := of_eq (product_rename w B k p Fin.castSucc) (under hBP R)
  have hN1 := of_eq (sum_rename w d p n Fin.castSucc) (under hN R)
  have hD1 := of_eq (product_rename w d s h Fin.castSucc) (under hD R)
  have hV1 := of_eq (sum_rename w v h v1 Fin.castSucc) (under hV R)
  have hScale1 := of_eq (product_rename w s B s1 Fin.castSucc) (under hScale R)
  have hT1 := of_eq (product_rename w k s1 t Fin.castSucc) (under hT R)
  have hOut1 := of_eq (sum_rename w v1 t out Fin.castSucc) (under hOut R)
  simpa only [Formula.raise,equation_rename] using
    point hZ1 w.castSucc B.castSucc d.castSucc k.castSucc n.castSucc v.castSucc s.castSucc v1.castSucc s1.castSucc out.castSucc p.castSucc h.castSucc t.castSucc (Fin.last m)
      hw1 (under hB R) (under hd R) (under hk R) (under hv R) (under hs R) hBP1 hN1 hD1 hV1 hScale1 hT1 hOut1 (.conjR hR)

theorem compose {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n v s v1 s1 out : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d w))
    (hk : Derives Γ (.mem k w)) (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w))
    (hN : Derives Γ (equation w B d k n)) (hDigit : Derives Γ (equation w d v s v1))
    (hScale : Derives Γ (product w s B s1)) (hTail : Derives Γ (equation w k v1 s1 out)) :
    Derives Γ (equation w n v s out) := by
  let P := equationBody w B d k n
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hN
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hDigit1 := of_eq (equation_rename w d v s v1 Fin.castSucc) (under hDigit P)
  let Q := equationBody w.castSucc d.castSucc v.castSucc s.castSucc v1.castSucc
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) hDigit1
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hTail1 := of_eq (equation_rename w k v1 s1 out Fin.castSucc) (under hTail P)
  have hTail2 := of_eq (equation_rename w.castSucc k.castSucc v1.castSucc s1.castSucc out.castSucc Fin.castSucc) (under hTail1 Q)
  let T := equationBody w.castSucc.castSucc k.castSucc.castSucc v1.castSucc.castSucc s1.castSucc.castSucc out.castSucc.castSucc
  let Θ := Context.add T (Context.image Formula.raise Ξ)
  apply Derives.exE (p := T) hTail2
  have hT : Derives Θ T := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under (ZFContext.under (ZFContext.under hZ P) Q) T
  have hw3 : Derives Θ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,omega_rename] using under (under (under hw P) Q) T
  have hBP3 : Derives Θ (product w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := by
    simpa only [Formula.raise,product_rename] using under (under (.conjL hP) Q) T
  have hN3 : Derives Θ (sum w.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,sum_rename] using under (under (.conjR hP) Q) T
  have hD3 : Derives Θ (product w.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := by
    simpa only [Formula.raise,product_rename] using under (.conjL hQ) T
  have hV3 : Derives Θ (sum w.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc v1.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,sum_rename] using under (.conjR hQ) T
  have hScale3 : Derives Θ (product w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc s1.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise,product_rename] using under (under (under hScale P) Q) T
  simpa only [Formula.raise,equation_rename] using
    from_witnesses hZ3 w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc v1.castSucc.castSucc.castSucc s1.castSucc.castSucc.castSucc out.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
      hw3 (under (under (under hB P) Q) T) (under (under (under hd P) Q) T) (under (under (under hk P) Q) T) (under (under (under hv P) Q) T) (under (under (under hs P) Q) T) hBP3 hN3 hD3 hV3 hScale3 (.conjL hT) (.conjR hT)

theorem output_subst {m} {Γ : Context m} (w b v s x y : Fin m) (he : Derives Γ (.equal x y))
    (hx : Derives Γ (equation w b v s x)) : Derives Γ (equation w b v s y) := by
  let P := equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m)
  have h0 : P.instantiate x = equation w b v s x := by simp only [P,Formula.instantiate,equation_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate y = equation w b v s y := by simp only [P,Formula.instantiate,equation_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hx))

theorem decompose {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n v s v1 s1 out : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d w))
    (hk : Derives Γ (.mem k w)) (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w))
    (hN : Derives Γ (equation w B d k n)) (hDigit : Derives Γ (equation w d v s v1))
    (hScale : Derives Γ (product w s B s1)) (hOut : Derives Γ (equation w n v s out)) :
    Derives Γ (equation w k v1 s1 out) := by
  have hnN := PacketReaderArithmetic.equation_range hZ w B d k n hw hd hN
  have hv1N := PacketReaderArithmetic.equation_range hZ w d v s v1 hw hv hDigit
  have hs1N := mul_range hZ w s B s1 hw hScale
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (equation w.castSucc k.castSucc v1.castSucc s1.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderArithmetic.exists_equation hZ w k v1 s1 hw hk hv1N hs1N)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hN1 := of_eq (equation_rename w B d k n Fin.castSucc) (under hN R)
  have hDigit1 := of_eq (equation_rename w d v s v1 Fin.castSucc) (under hDigit R)
  have hScale1 := of_eq (product_rename w s B s1 Fin.castSucc) (under hScale R)
  have hOut1 := of_eq (equation_rename w n v s out Fin.castSucc) (under hOut R)
  have hFull := compose hZ1 w.castSucc B.castSucc d.castSucc k.castSucc n.castSucc v.castSucc s.castSucc v1.castSucc s1.castSucc (Fin.last m)
    hw1 (under hB R) (under hd R) (under hk R) (under hv R) (under hs R) hN1 hDigit1 hScale1 (.conjR hR)
  have heq := PacketAffineCore.equation_unique hZ1 w.castSucc n.castSucc v.castSucc s.castSucc (Fin.last m) out.castSucc hw1 (under hnN R) (under hs R) hFull hOut1
  simpa only [Formula.raise,equation_rename] using output_subst _ _ _ _ _ _ heq (.conjR hR)

theorem exact_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n v s v1 s1 out : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hd : Derives Γ (.mem d w))
    (hk : Derives Γ (.mem k w)) (hv : Derives Γ (.mem v w)) (hs : Derives Γ (.mem s w))
    (hN : Derives Γ (equation w B d k n)) (hDigit : Derives Γ (equation w d v s v1))
    (hScale : Derives Γ (product w s B s1)) :
    Derives Γ ((equation w n v s out).iff (equation w k v1 s1 out)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact decompose (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hd _) (add hk _) (add hv _) (add hs _) (add hN _) (add hDigit _) (add hScale _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact compose (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ (add hw _) (add hB _) (add hd _) (add hk _) (add hv _) (add hs _) (add hN _) (add hDigit _) (add hScale _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketReaderAffineCompose
