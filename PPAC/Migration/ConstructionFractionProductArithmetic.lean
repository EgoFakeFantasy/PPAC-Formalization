/- The fraction product laws consumed by pinned same-head margin.
Positive order reflection reuses the accepted natural Times.order_iff and
scaled_equiv; distribution reuses the accepted common denominator/sum adapter. -/
import PPAC.Migration.ConstructionFractionProduct
import PPAC.Migration.ConstructionFractionScaling
import PPAC.Migration.ConstructionCutAssociativity

namespace PPAC.Migration.ConstructionFractionProductArithmetic
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionFractionProduct
open ConstructionFractionAddition (Sum)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Factor c/d is reduced to the EXISTING positive natural scalings c and d. -/
theorem positive_product_le_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w q r k s t c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q k s) (ht : Product hM w r k t)
    (hk : Coordinates w k c d) (hc : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z c) :
    Le hM w s t ↔ Le hM w q r := by
  refine ⟨?_,fun h => product_left_mono hM hw hs ht h⟩
  intro hst
  obtain ⟨a,b,c',d',n,den,hq,hk',hsC,hn,hd⟩ := hs
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hk.2.2.2 hk'.2.2.2
  obtain ⟨a',b',c',d',n',den',hr,hk',htC,hn',hd'⟩ := ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hk.2.2.2 hk'.2.2.2
  obtain ⟨sBase,hsBaseCode⟩ := KuratowskiZF.exists_code hM n b
  obtain ⟨tBase,htBaseCode⟩ := KuratowskiZF.exists_code hM n' b'
  have hsBase : Coordinates w sBase n b := ⟨hsC.1,hq.2.1,hq.2.2.1,hsBaseCode⟩
  have htBase : Coordinates w tBase n' b' := ⟨htC.1,hr.2.1,hr.2.2.1,htBaseCode⟩
  have hQTimes : ConstructionFractionScaling.Times hM w c q sBase := ⟨a,b,n,hq,hn,hsBase⟩
  have hRTimes : ConstructionFractionScaling.Times hM w c r tBase := ⟨a',b',n',hr,hn',htBase⟩
  obtain ⟨sScaled,hSTimes⟩ := ConstructionFractionScaling.exists_times hM hw hk.2.1 ⟨n,den,hsC⟩
  obtain ⟨tScaled,hTTimes⟩ := ConstructionFractionScaling.exists_times hM hw hk.2.1 ⟨n',den',htC⟩
  obtain ⟨n0,den0,nd,hsC',hND,hSScaled⟩ := hSTimes
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hsC.2.2.2 hsC'.2.2.2
  obtain ⟨n0,den0,nd',htC',hND',hTScaled⟩ := hTTimes
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective htC.2.2.2 htC'.2.2.2
  have eqS := ConstructionFractionDifference.scaled_equiv hM hw hsBase hSScaled hk.2.1 hND hd
  have eqT := ConstructionFractionDifference.scaled_equiv hM hw htBase hTScaled hk.2.1 hND' hd'
  have hScaled := (ConstructionFractionScaling.order_iff hM hw hk.2.1 hk.2.2.1
    ⟨n,den,nd,hsC,hND,hSScaled⟩ ⟨n',den',nd',htC,hND',hTScaled⟩).mpr hst
  have hBases := le_trans hM hw eqS.1 (le_trans hM hw hScaled eqT.2)
  exact (ConstructionFractionScaling.order_iff hM hw hk.1 hc hQTimes hRTimes).mp hBases

theorem positive_product_lt (hM : FirstOrder.Theory.Models M nativeZF)
    {w q r k s t c d : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q k s) (ht : Product hM w r k t)
    (hk : Coordinates w k c d) (hc : ∃ z, (Project.FirstOrderSemantics.reduct M).mem z c)
    (hqr : Lt hM w q r) : Lt hM w s t :=
  ⟨product_left_mono hM hw hs ht hqr.1,
    fun h => hqr.2 ((positive_product_le_iff hM hw ht hs hk hc).mp h)⟩

theorem product_equiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w q r q' r' s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hs : Product hM w q r s) (ht : Product hM w q' r' t)
    (hq : Le hM w q q' ∧ Le hM w q' q) (hr : Le hM w r r' ∧ Le hM w r' r) :
    Le hM w s t ∧ Le hM w t s :=
  ⟨product_mono hM hw hs ht hq.1 hr.1,product_mono hM hw ht hs hq.2 hr.2⟩

/-- q*(r+t) and q*r+q*t agree by represented value on all internal codes. -/
theorem fraction_distrib (hM : FirstOrder.Theory.Models M nativeZF)
    {w q r t rt qr qt left right : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hRT : Sum hM w r t rt) (hl : Product hM w q rt left)
    (hQR : Product hM w q r qr) (hQT : Product hM w q t qt)
    (hr : Sum hM w qr qt right) : Le hM w left right ∧ Le hM w right left := by
  have hQRCopy := hQR
  have hQTCopy := hQT
  obtain ⟨a,b,c0,d0,_,_,hq,hr0,_,_,_⟩ := hQRCopy
  obtain ⟨_,_,e0,f0,_,_,_,ht0,_,_,_⟩ := hQTCopy
  obtain ⟨den,c,e,_,r',t',_,hr',ht',_,eqR,eqT,_⟩ :=
    ConstructionCutAssociativity.common_denominator hM hw ⟨c0,d0,hr0⟩ ⟨e0,f0,ht0⟩ ⟨e0,f0,ht0⟩
  obtain ⟨n,hnw,hn⟩ := add_exists hM hw hr'.1 ht'.1
  obtain ⟨sumN,hSumNCode⟩ := KuratowskiZF.exists_code hM n den
  have hSumN : Coordinates w sumN n den := ⟨hnw,hr'.2.1,hr'.2.2.1,hSumNCode⟩
  have eqRT := ConstructionCutAssociativity.sum_common_denominator hM hw hRT hr' ht' hSumN hn eqR eqT
  obtain ⟨ac,hacw,hac⟩ := mul_exists hM hw hq.1 hr'.1
  obtain ⟨ae,haew,hae⟩ := mul_exists hM hw hq.1 ht'.1
  obtain ⟨an,hanw,han⟩ := mul_exists hM hw hq.1 hnw
  obtain ⟨bd,hbdw,hbd⟩ := mul_exists hM hw hq.2.1 hr'.2.1
  have hbdN := ConstructionFractionAddition.mul_nonempty hM hw hq.2.1 hr'.2.1 hq.2.2.1 hr'.2.2.1 hbd
  obtain ⟨u,huCode⟩ := KuratowskiZF.exists_code hM ac bd
  obtain ⟨v,hvCode⟩ := KuratowskiZF.exists_code hM ae bd
  obtain ⟨out,hOutCode⟩ := KuratowskiZF.exists_code hM an bd
  have hu : Coordinates w u ac bd := ⟨hacw,hbdw,hbdN,huCode⟩
  have hv : Coordinates w v ae bd := ⟨haew,hbdw,hbdN,hvCode⟩
  have hout : Coordinates w out an bd := ⟨hanw,hbdw,hbdN,hOutCode⟩
  have hProdR : Product hM w q r' u := ⟨a,b,c,den,ac,bd,hq,hr',hu,hac,hbd⟩
  have hProdT : Product hM w q t' v := ⟨a,b,e,den,ae,bd,hq,ht',hv,hae,hbd⟩
  have hProdSum : Product hM w q sumN out := ⟨a,b,n,den,an,bd,hq,hSumN,hout,han,hbd⟩
  have hAdd := mul_add hM hw hq.1 hr'.1 ht'.1 hn han hac hae
  have hQRefl := le_refl hM hw ⟨a,b,hq⟩
  have eqQR := product_equiv hM hw hQR hProdR ⟨hQRefl,hQRefl⟩ eqR
  have eqQT := product_equiv hM hw hQT hProdT ⟨hQRefl,hQRefl⟩ eqT
  have eqLeft := product_equiv hM hw hl hProdSum ⟨hQRefl,hQRefl⟩ eqRT
  have eqRight := ConstructionCutAssociativity.sum_common_denominator hM hw hr hu hv hout hAdd eqQR eqQT
  exact ⟨le_trans hM hw eqLeft.1 eqRight.2,le_trans hM hw eqRight.1 eqLeft.2⟩

end PPAC.Migration.ConstructionFractionProductArithmetic
