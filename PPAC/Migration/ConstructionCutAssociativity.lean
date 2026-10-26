/- Associativity needed by the pinned ProbeMargins interval inequalities and
Word height sums. Reuse native ordinal arithmetic and the accepted rational
representation equivalences; fraction code equality is never assumed. -/
import PPAC.Migration.ConstructionCutArithmetic

namespace PPAC.Migration.ConstructionCutAssociativity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
open ConstructionFractionAddition (Sum)
open ConstructionCutAddition (SumMember SumCut)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem equiv_trans (hM : FirstOrder.Theory.Models M nativeZF) {w q r s : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hqr : Le hM w q r ∧ Le hM w r q) (hrs : Le hM w r s ∧ Le hM w s r) :
    Le hM w q s ∧ Le hM w s q :=
  ⟨le_trans hM hw hqr.1 hrs.1,le_trans hM hw hrs.2 hqr.2⟩

/-- Three arbitrary internal fraction codes admit equivalent codes with one
common denominator. This is internal finite arithmetic, not external choice. -/
theorem common_denominator (hM : FirstOrder.Theory.Models M nativeZF) {w q r t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hq : Fraction w q) (hr : Fraction w r) (ht : Fraction w t) :
    ∃ den a b c q' r' t', Coordinates w q' a den ∧ Coordinates w r' b den ∧
      Coordinates w t' c den ∧ (Le hM w q q' ∧ Le hM w q' q) ∧
      (Le hM w r r' ∧ Le hM w r' r) ∧ (Le hM w t t' ∧ Le hM w t' t) := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨c,d,hr⟩ := hr
  obtain ⟨e,f,ht⟩ := ht
  obtain ⟨ad,hAd,had⟩ := mul_exists hM hw hq.1 hr.2.1
  obtain ⟨cb,hCb,hcb⟩ := mul_exists hM hw hr.1 hq.2.1
  obtain ⟨bd,hBd,hbd⟩ := mul_exists hM hw hq.2.1 hr.2.1
  have hBdn := ConstructionFractionAddition.mul_nonempty hM hw hq.2.1 hr.2.1 hq.2.2.1 hr.2.2.1 hbd
  obtain ⟨q0,hq0code⟩ := KuratowskiZF.exists_code hM ad bd
  obtain ⟨r0,hr0code⟩ := KuratowskiZF.exists_code hM cb bd
  have hq0 : Coordinates w q0 ad bd := ⟨hAd,hBd,hBdn,hq0code⟩
  have hr0 : Coordinates w r0 cb bd := ⟨hCb,hBd,hBdn,hr0code⟩
  have eqQ0 := ConstructionFractionDifference.scaled_equiv hM hw hq hq0 hr.2.1 had hbd
  have eqR0 := ConstructionFractionDifference.scaled_equiv hM hw hr hr0 hq.2.1 hcb
    (mul_comm hM hw hq.2.1 hr.2.1 hbd)
  obtain ⟨den,hDen,hden⟩ := mul_exists hM hw hBd ht.2.1
  obtain ⟨an,hAn,han⟩ := mul_exists hM hw hAd ht.2.1
  obtain ⟨bn,hBn,hbn⟩ := mul_exists hM hw hCb ht.2.1
  obtain ⟨cn,hCn,hcn⟩ := mul_exists hM hw ht.1 hBd
  have hDenn := ConstructionFractionAddition.mul_nonempty hM hw hBd ht.2.1 hBdn ht.2.2.1 hden
  obtain ⟨q',hq'code⟩ := KuratowskiZF.exists_code hM an den
  obtain ⟨r',hr'code⟩ := KuratowskiZF.exists_code hM bn den
  obtain ⟨t',ht'code⟩ := KuratowskiZF.exists_code hM cn den
  have hq' : Coordinates w q' an den := ⟨hAn,hDen,hDenn,hq'code⟩
  have hr' : Coordinates w r' bn den := ⟨hBn,hDen,hDenn,hr'code⟩
  have ht' : Coordinates w t' cn den := ⟨hCn,hDen,hDenn,ht'code⟩
  exact ⟨den,an,bn,cn,q',r',t',hq',hr',ht',
    equiv_trans hM hw eqQ0 (ConstructionFractionDifference.scaled_equiv hM hw hq0 hq' ht.2.1 han hden),
    equiv_trans hM hw eqR0 (ConstructionFractionDifference.scaled_equiv hM hw hr0 hr' ht.2.1 hbn hden),
    ConstructionFractionDifference.scaled_equiv hM hw ht ht' hBd hcn (mul_comm hM hw hBd ht.2.1 hden)⟩

theorem sum_common_denominator (hM : FirstOrder.Theory.Models M nativeZF)
    {w q r s q' r' t a b den n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Sum hM w q r s) (hq : Coordinates w q' a den) (hr : Coordinates w r' b den)
    (ht : Coordinates w t n den) (hn : Add hM a b n)
    (eqQ : Le hM w q q' ∧ Le hM w q' q) (eqR : Le hM w r r' ∧ Le hM w r' r) :
    Le hM w s t ∧ Le hM w t s := by
  obtain ⟨s',hs'⟩ := ConstructionFractionAddition.sum_exists hM hw ⟨a,den,hq⟩ ⟨b,den,hr⟩
  exact equiv_trans hM hw (ConstructionFractionAddition.sum_equiv hM hw hs hs' eqQ eqR)
    (ConstructionFractionDifference.same_den_sum hM hw hq hr ht hn hs')

/-- Associativity by value on all internal codes, including nonstandard ones. -/
theorem fraction_assoc (hM : FirstOrder.Theory.Models M nativeZF) {w q r t qr rt left right : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hqr : Sum hM w q r qr) (hrt : Sum hM w r t rt)
    (hl : Sum hM w qr t left) (hr : Sum hM w q rt right) :
    Le hM w left right ∧ Le hM w right left := by
  have hqrCopy := hqr
  obtain ⟨a0,b0,c0,d0,_,_,hq0,hr0,_,_⟩ := hqrCopy
  have hrtCopy := hrt
  obtain ⟨_,_,e0,f0,_,_,_,ht0,_,_⟩ := hrtCopy
  obtain ⟨den,a,b,c,q',r',t',hq',hr',ht',eqQ,eqR,eqT⟩ :=
    common_denominator hM hw ⟨a0,b0,hq0⟩ ⟨c0,d0,hr0⟩ ⟨e0,f0,ht0⟩
  obtain ⟨ab,hAb,hab⟩ := add_exists hM hw hq'.1 hr'.1
  obtain ⟨bc,hBc,hbc⟩ := add_exists hM hw hr'.1 ht'.1
  obtain ⟨n,hN,hn⟩ := add_exists hM hw hAb ht'.1
  obtain ⟨n',_,hn'⟩ := add_exists hM hw hq'.1 hBc
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have he := ZF.ordinalAddition_assoc hZF (KuratowskiZF.interpretation hM)
    (ord a hq'.1) (ord b hr'.1) (ord c ht'.1) hab hbc hn' hn
  subst n'
  obtain ⟨qab,hQab⟩ := KuratowskiZF.exists_code hM ab den
  obtain ⟨qbc,hQbc⟩ := KuratowskiZF.exists_code hM bc den
  obtain ⟨total,hTotal⟩ := KuratowskiZF.exists_code hM n den
  have hqab : Coordinates w qab ab den := ⟨hAb,hq'.2.1,hq'.2.2.1,hQab⟩
  have hqbc : Coordinates w qbc bc den := ⟨hBc,hq'.2.1,hq'.2.2.1,hQbc⟩
  have htotal : Coordinates w total n den := ⟨hN,hq'.2.1,hq'.2.2.1,hTotal⟩
  have eqQR := sum_common_denominator hM hw hqr hq' hr' hqab hab eqQ eqR
  have eqRT := sum_common_denominator hM hw hrt hr' ht' hqbc hbc eqR eqT
  have eqLeft := sum_common_denominator hM hw hl hqab ht' htotal hn eqQR eqT
  have eqRight := sum_common_denominator hM hw hr hq' hqbc htotal hn' eqQ eqRT
  exact ⟨le_trans hM hw eqLeft.1 eqRight.2,le_trans hM hw eqRight.1 eqLeft.2⟩

theorem sum_fraction {hM : FirstOrder.Theory.Models M nativeZF} {w q r s : M.Carrier .set}
    (hs : Sum hM w q r s) : Fraction w s := by
  obtain ⟨_,_,_,_,n,den,_,_,h,_⟩ := hs
  exact ⟨n,den,h⟩

theorem sum_is_cut (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : SumCut hM w Q a b c) : Cut hM w Q c := by
  obtain ⟨d,hd,hs⟩ := ConstructionCutArithmetic.exists_sum hM hw hQ ha hb
  exact (ConstructionCutAddition.sum_unique hM hs hc) ▸ hd

theorem member_reassociate (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c ab bc p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hab : SumCut hM w Q a b ab) (hbc : SumCut hM w Q b c bc)
    (hp : SumMember hM w ab c p) : SumMember hM w a bc p := by
  have hbcCut := sum_is_cut hM hw hQ hb hc hbc
  have bIn := (ConstructionCutArithmetic.sum_contains hb hc hbc).1
  have cIn := (ConstructionCutArithmetic.sum_contains hb hc hbc).2
  rcases hp with hp | hp | ⟨q,r,s,hq,hr,hs,hps⟩
  · rcases ((hab p).mp hp).2 with hp | hp | ⟨q,r,s,hq,hr,hs,hps⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl (bIn p hp))
    · exact Or.inr (Or.inr ⟨q,r,s,hq,bIn r hr,hs,hps⟩)
  · exact Or.inr (Or.inl (cIn p hp))
  · rcases ((hab q).mp hq).2 with hq | hq | ⟨x,y,z,hx,hy,hxy,hqz⟩
    · exact Or.inr (Or.inr ⟨q,r,s,hq,cIn r hr,hs,hps⟩)
    · have hsb := (hbc s).mpr ⟨(hQ s).mpr (sum_fraction hs),Or.inr (Or.inr
        ⟨q,r,s,hq,hr,hs,le_refl hM hw (sum_fraction hs)⟩)⟩
      exact Or.inr (Or.inl (hbcCut.2.1 p s hsb hps))
    · obtain ⟨yr,hyr⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ y).mp (hb.1 y hy))
        ((hQ r).mp (hc.1 r hr))
      have hyrbc := (hbc yr).mpr ⟨(hQ yr).mpr (sum_fraction hyr),Or.inr (Or.inr
        ⟨y,r,yr,hy,hr,hyr,le_refl hM hw (sum_fraction hyr)⟩)⟩
      obtain ⟨xyr,hxyr⟩ := ConstructionFractionAddition.sum_exists hM hw ((hQ x).mp (ha.1 x hx)) (sum_fraction hyr)
      obtain ⟨zr,hzr⟩ := ConstructionFractionAddition.sum_exists hM hw (sum_fraction hxy) ((hQ r).mp (hc.1 r hr))
      have hszr := (ConstructionFractionAddition.sum_right_le_iff hM hw hs hzr).mpr hqz
      have he := fraction_assoc hM hw hxy hyr hzr hxyr
      exact Or.inr (Or.inr ⟨x,yr,xyr,hx,hyrbc,hxyr,le_trans hM hw hps (le_trans hM hw hszr he.1)⟩)

/-- Equality of the actual two bracketings on arbitrary cuts, with no
retained associativity or rational-representability assumption. -/
theorem cut_assoc (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c ab bc left right : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (ha : Cut hM w Q a) (hb : Cut hM w Q b) (hc : Cut hM w Q c)
    (hab : SumCut hM w Q a b ab) (hbc : SumCut hM w Q b c bc)
    (hl : SumCut hM w Q ab c left) (hr : SumCut hM w Q a bc right) : left = right := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members left right
  intro p
  constructor
  · intro hp
    obtain ⟨hpQ,hp⟩ := (hl p).mp hp
    exact (hr p).mpr ⟨hpQ,member_reassociate hM hw hQ ha hb hc hab hbc hp⟩
  · intro hp
    obtain ⟨hpQ,hp⟩ := ((ConstructionCutArithmetic.sum_comm hM hw hr) p).mp hp
    have h := member_reassociate hM hw hQ hc hb ha
      (ConstructionCutArithmetic.sum_comm hM hw hbc) (ConstructionCutArithmetic.sum_comm hM hw hab) hp
    exact ((ConstructionCutArithmetic.sum_comm hM hw hl) p).mpr ⟨hpQ,h⟩

end PPAC.Migration.ConstructionCutAssociativity
