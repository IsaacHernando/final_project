import Project.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Data.Int.Parity

open ZMod legendreSym Nat Int List

variable (a : ℤ)

example (h : a < 0) : -a > 0 := by exact Int.neg_pos_of_neg h

lemma pos_eq_natAbs (h : a > 0) : a = a.natAbs := by
  cases a
  simp only [ofNat_eq_coe, natAbs_ofNat]
  case negSucc h' => norm_cast

lemma neg_mul_eq_natAbs (h : a < 0) : -a = a.natAbs := by
  have := pos_eq_natAbs (-a) (Int.neg_pos_of_neg h)
  norm_cast at this
  simp at this
  norm_cast

lemma list_prod_eq_int_pos (h: a > 0) : List.prod (factors (natAbs a)) = a := by
  nth_rewrite 2 [pos_eq_natAbs a]
  norm_cast
  apply prod_factors
  simp only [ne_eq, natAbs_eq_zero]
  exact Int.ne_of_gt h
  assumption

lemma list_prod_eq_int_neg (h: a < 0) : List.prod (factors (natAbs a)) = -a := by
  have : natAbs a = natAbs (-a) := by simp
  rw [this]
  have aa := pos_eq_natAbs (-a) (Int.neg_pos_of_neg h)
  norm_cast at aa
  simp at aa
  have : -a = (natAbs a) := by norm_cast
  apply list_prod_eq_int_pos
  simp only [gt_iff_lt, Left.neg_pos_iff]
  assumption

lemma list_prod_eq_int_neg' (h : a < 0) : (-1) * List.prod (factors (natAbs a)) = a := by
  rw [list_prod_eq_int_neg]
  simp only [mul_neg, neg_mul, one_mul, neg_neg]
  assumption

lemma pos_int_is_nat (h : a > 0) : a.toNat = a := toNat_of_nonneg (Int.nonneg_of_pos h)

variable (p : ℕ) [hp : Fact p.Prime] (a : ℤ)

lemma legendre_neg_mul : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (-a)) := by
  have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
  nth_rewrite 1 [this]
  exact legendreSym.mul p (-1) (-a)

lemma legendre_neg_mul' (h : a < 0) : legendreSym p a = (legendreSym p (-1)) * (legendreSym p (a.natAbs)) := by
  have : a = -1 * -a := by simp only [mul_neg, neg_mul, one_mul, neg_neg]
  nth_rewrite 1 [this]
  have : natAbs a = natAbs (-a) := by simp
  have aa := pos_eq_natAbs (-a) (Int.neg_pos_of_neg h)
  norm_cast at aa
  simp at aa
  have : -a = (natAbs a) := by norm_cast
  rw [this]
  apply legendreSym.mul

lemma legendre_factorization_pos (h : a > 0) : legendreSym p a = legendreSym p (List.prod (factors a.natAbs)) := by
  have := list_prod_eq_int_pos a h
  norm_cast at this
  nth_rewrite 1 [←this]
  rw [Lean.Internal.coeM, @bind_pure_comp]
  rfl

lemma legendre_factorization_neg (h : a < 0)
  : legendreSym p a = (legendreSym p (-1)) * legendreSym p (List.prod (factors a.natAbs)) := by
    rw [legendre_neg_mul']
    congr 1
    · nth_rewrite 1 [legendre_factorization_pos]
      norm_cast ; norm_cast
      have := neg_mul_eq_natAbs a h
      have h' : -a > 0 := by exact Int.neg_pos_of_neg h
      rw [this] at h'
      norm_cast at h'
    · assumption

lemma factorization_eq_prod_factorization_pos (h : a > 0): (legendreSym p a) = List.prod ( a.natAbs.factors.pmap (fun q _ => @legendreSym p hp  q) (fun _ _ => hp) ):= by
  rw [legendre_factorization_pos, Lean.Internal.coeM, @bind_pure_comp]
  simp only [map_eq_map, pmap_eq_map, map_map]
  induction (factors (natAbs a))
  case nil => simp only [map_nil, prod_nil, at_one]
  case cons => simp only [map_cons, prod_cons, Function.comp_apply, legendreSym.mul] ; congr 1
  assumption

lemma factorization_eq_prod_factorization_neg (h : a < 0): (legendreSym p a) = (legendreSym p (-1)) * List.prod ( a.natAbs.factors.pmap (fun q _ => @legendreSym p hp q) (fun _ _ => hp) ):= by
  rw [legendre_neg_mul]
  congr 1
  rw [neg_mul_eq_natAbs]
  case e_a =>
    have hh := factorization_eq_prod_factorization_pos p (natAbs a) (by simp ; exact Int.ne_of_lt h)
    rw [hh]
    norm_cast
  assumption

variable (hp' : p ≠ 2) in
lemma lengedre_eq_reciprocity_map_odd_map (h : a ≠ 0) (h' : Odd a)
  : map (fun a => legendreSym p a) (Lean.Internal.coeM a.natAbs.factors)
      = (pmap (fun q hq =>
                  let hq' : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
                  (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) (factors (natAbs a))
                  (fun _ x => x)) := by
    apply List.ext
    intros n
    simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
    split
    case a.h_1 _ _ _ _ o _ =>
      simp only [get?_eq_none] at o
      rw [Lean.Internal.coeM, @bind_pure_comp]
      simp only [map_eq_map, get?_map, Option.map_eq_map, Option.map_map,
        Option.map_eq_none', get?_eq_none]
      exact o
    case a.h_2 _ _ _ o₄ o₅ o₆ _ =>
      simp only [Option.map_eq_map, Nat.odd_iff_not_even, Option.map_eq_some']
      use o₄
      constructor
      · rw[Lean.Internal.coeM, @bind_pure_comp]
        simp only [map_eq_map, get?_map, Option.map_eq_some']
        exact ⟨o₄, ⟨o₆ ,rfl ⟩⟩
      ·
        letI : Fact (Nat.Prime o₄) := ⟨prime_of_mem_factors (o₅ o₄ rfl)⟩
        have : o₄ ≠ 2 := by
            by_contra s
            have : Even (a.natAbs) ∧ Odd (a.natAbs) := {
              left := even_iff_two_dvd.mpr <|
                (mem_factors_iff_dvd (natAbs_ne_zero.mpr h) Nat.prime_two).mp
                (o₅ 2 (congrArg some s))
              right := Odd.natAbs h' }
            simp only [Nat.odd_iff_not_even, and_not_self] at this
        rw [quadratic_reciprocity' this hp']

variable (hp' : p ≠ 2) in
lemma legendre_eq_quadratic_reciprocity_pos_odd (h : a > 0) (h' : Odd a)
  : legendreSym p a = List.prod (a.natAbs.factors.pmap
    (fun q (hq : q ∈ a.natAbs.factors) =>
        let hq' : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
        (-1) ^ (q / 2 * (p / 2)) * legendreSym q p)
    (fun _ b => b)) := by
        simp only [factorization_eq_prod_factorization_pos p a h,
          map_eq_map, pmap_eq_map, map_map, Nat.odd_iff_not_even]
        rw [lengedre_eq_reciprocity_map_odd_map]
        assumption'
        exact Int.ne_of_gt h

variable (hp' : p ≠ 2) in
lemma legendre_eq_quadratic_reciprocity_neg_odd (h : a < 0) (h' : Odd a)
  : legendreSym p a = (legendreSym p (-1)) * List.prod (a.natAbs.factors.pmap
    (fun q (hq : q ∈ a.natAbs.factors) =>
        let hq' : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
        (-1) ^ (q / 2 * (p / 2)) * legendreSym q p)
    (fun _ b => b)) := by
        simp only [factorization_eq_prod_factorization_neg p a h,
          map_eq_map, pmap_eq_map, map_map, Nat.odd_iff_not_even]
        rw [lengedre_eq_reciprocity_map_odd_map]
        assumption'
        exact Int.ne_of_lt h

variable (hp' : p ≠ 2) in
lemma lengedre_eq_reciprocity_map
  : map (fun a => legendreSym p a) (Lean.Internal.coeM a.natAbs.factors)
      = (pmap (fun q hq =>
                  if q = 2 then legendreSym p 2
                  else
                      let hq' : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
                      (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) (a.natAbs.factors)
              (fun _ x =>x)) := by
    apply List.ext
    intros n
    simp only [get?_map, Nat.odd_iff_not_even, @get?_pmap, ← @Option.map_eq_map, Option.pmap]
    split
    case a.h_1 _ _ _ _ o _ =>
      simp only [get?_eq_none] at o
      rw [Lean.Internal.coeM, @bind_pure_comp]
      simp only [map_eq_map, get?_map, Option.map_eq_map, Option.map_map,
        Option.map_eq_none', get?_eq_none]
      exact o
    case a.h_2 _ _ _ o₄ o₅ o₆ _ =>
      simp only [Option.map_eq_map, Nat.odd_iff_not_even, Option.map_eq_some']
      use o₄
      constructor
      · rw[Lean.Internal.coeM, @bind_pure_comp]
        simp only [map_eq_map, get?_map, Option.map_eq_some']
        exact ⟨o₄, ⟨o₆ ,rfl ⟩⟩
      ·
        letI : Fact (Nat.Prime o₄) := ⟨prime_of_mem_factors (o₅ o₄ rfl)⟩
        split_ifs
        case pos h => simp [h]
        case neg h => exact quadratic_reciprocity' h hp'

def legendreAlg_reciprocity : ℤ :=
   if _ : a = 0 then 0
   else
       if _ : p = 2 then legendreSym p (a % p)
       else
          if _ : a > 0 then
              List.prod <|
                   (pmap (fun q hq =>
                  if q = 2 then legendreSym p 2
                  else
                      let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
                      (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) (a.natAbs.factors)
              (fun _ x =>x))
          else
              (legendreSym p (-1)) *
              (List.prod <|
                   (pmap (fun q hq =>
                  if q = 2 then legendreSym p 2
                  else
                      let _ : Fact (Nat.Prime q) := ⟨prime_of_mem_factors hq⟩
                      (-1) ^ (q / 2 * (p / 2)) * legendreSym q p) (a.natAbs.factors)
                  (fun _ x =>x)))

@[csimp]
theorem legendreAlg_eq_legendreSym : @legendreSym = @legendreAlg_reciprocity := by {
  ext p hp a
  simp only [legendreAlg_reciprocity]
  split_ifs
  case pos h => rw [h] ; simp
  case pos => exact legendreSym.mod p a
  case pos h h' k => {

    have := lengedre_eq_reciprocity_map p a h'
    simp at this
    rw [←this]
    rw [factorization_eq_prod_factorization_pos]
    assumption'
    simp only [pmap_eq_map]
  }
  case neg h h' k=> {
    rw [legendre_neg_mul']
    congr 1
    have := lengedre_eq_reciprocity_map p a h'
    simp at this
    rw [←this]
    rw [factorization_eq_prod_factorization_pos p (a.natAbs)]
    simp only [coe_natAbs, pmap_eq_map]
    have : natAbs |a| = natAbs a := by {
      exact natAbs_abs a
    }
    rw [this]
    simp ; exact h
    by_contra kk
    exact ltByCases a 0 kk h k
  }
}
