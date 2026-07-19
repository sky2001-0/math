import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold

-- # 一階述語論理

namespace FirstOrderLogic

-- ## 命題の定式化

-- 非論理記号の型
structure Signature where
  Func : Type
  FuncArity : Func -> Nat
  Pred : Type
  PredArity : Pred -> Nat

variable {S : Signature}

-- 変数の型
abbrev Variable := Nat

-- 変数の集まりの型
abbrev VarSet := Finset Variable

namespace VarSet

  -- 与えられた変数の集まりに入っていない、新しい変数を用意する。
  def fresh (s : VarSet) : Variable :=
    s.sup (fun n : Variable => n) + 1

  lemma fresh_not_mem
    {x : Variable} {s : VarSet}
    (x_in_s : x ∈ s) :
    x ≠ fresh s
  := by
    apply ne_of_lt
    . calc
      x ≤ s.sup id := Finset.le_sup (f := id) x_in_s
      _ < fresh s := Nat.lt_succ_self _

  abbrev replace {n : Nat} (f : Fin n → VarSet) : VarSet :=
    (Finset.univ : Finset (Fin n)).biUnion f

  lemma mem_replace
    {n : Nat} {f : Fin n → VarSet} {v : Variable} :
    v ∈ replace f ↔ ∃ i, v ∈ f i
  := by simp [replace]

end VarSet

-- 項の型
inductive Term (S : Signature) : Type
| var  : Variable -> Term S
| func : (f : S.Func) -> (Fin (S.FuncArity f) -> Term S) -> Term S

namespace Term

  -- 項から使用変数の集まりを返す
  def vars : Term S -> VarSet
  | .var x => {x}
  | .func _ args => VarSet.replace (fun i => vars (args i))

  -- 項内の変数への項の代入
  def substitute (x : Variable) (t : Term S) : Term S → Term S
  | .var y => if y = x then t else Term.var y
  | .func f args => .func f (fun i => substitute x t (args i))

  lemma subst_self
    {x : Variable} {t : Term S} :
    substitute x (Term.var x) t = t
  := by
    induction t with
    | var y =>
      by_cases y_eq_x : y = x
      . simp [substitute, y_eq_x]
      . simp [substitute, y_eq_x]
    | func f args ih => simp [substitute, ih]

  lemma subst_clean
    {x y : Variable} {t : Term S}
    (x_neq_y : x ≠ y) :
    x ∉ vars (substitute x (Term.var y) t)
  := by
    induction t with
    | var z =>
      by_cases z_eq_x : z = x
      · simp [substitute, vars, x_neq_y, z_eq_x]
      · simp [substitute, vars, Ne.symm z_eq_x, eq_comm]
    | func f args ih =>
      simpa [vars, substitute, VarSet.mem_replace] using ih

  lemma subst_new
    {x y : Variable} {t : Term S}
    (x_in_t : x ∈ vars t) :
    y ∈ vars (substitute x (Term.var y) t)
  := by
    induction t with
    | var z =>
      simp [vars] at x_in_t
      simp [vars, substitute, x_in_t]
    | func f args ih =>
      obtain ⟨i, x_in_arg⟩ := (VarSet.mem_replace).1 x_in_t
      exact (VarSet.mem_replace).2 ⟨i, ih i x_in_arg⟩

  lemma subst_preserve
    {x y z : Variable} {t : Term S}
    (x_in_t : x ∈ vars t) (x_neq_y : x ≠ y) :
    x ∈ vars (substitute y (Term.var z) t)
  := by
    induction t with
    | var w =>
      simp [vars] at x_in_t
      have w_neq_y : w ≠ y := by
        simpa [x_in_t] using x_neq_y
      simp [substitute, vars, w_neq_y, x_in_t]
    | func f args ih =>
      simp only [vars, VarSet.mem_replace] at x_in_t
      obtain ⟨i, x_in_args⟩ := x_in_t
      simp only [substitute, vars, VarSet.mem_replace]
      exact ⟨i, ih i x_in_args⟩

  lemma subst_nonvar
    {x : Variable} {s t : Term S}
    (x_nin_t : x ∉ vars t) :
    substitute x s t = t
  := by
    induction t with
    | var y =>
      simp [vars] at x_nin_t
      simp [substitute, Ne.symm x_nin_t]
    | func f args ih =>
      simp [vars] at x_nin_t
      simp [substitute, fun i => ih i (x_nin_t i)]

  lemma subst_cancel
    {x y : Variable} {t : Term S}
    (y_nin_t : y ∉ vars t) :
    substitute y (Term.var x) (substitute x (Term.var y) t) = t
  := by
    induction t with
    | var z =>
      simp [vars] at y_nin_t
      by_cases z_eq_x : z = x
      · simp [substitute, z_eq_x]
      · simp [substitute, z_eq_x, Ne.symm y_nin_t]
    | func f args ih =>
      simp [vars] at y_nin_t
      simp [substitute, fun i => ih i (y_nin_t i)]

end Term

-- 命題
inductive Formula (S : Signature) : Type
| bot     : Formula S
| land    : Formula S -> Formula S -> Formula S
| imply   : Formula S -> Formula S -> Formula S
| pred    : (p : S.Pred) -> (Fin (S.PredArity p) -> Term S) -> Formula S
| lforall : Variable -> Formula S -> Formula S

namespace Formula
  -- 真理
  def top : Formula S := imply bot bot

  -- 否定
  def lnot (φ : Formula S) : Formula S := imply φ bot

  -- 同値
  def iff (φ ψ : Formula S) : Formula S := land (imply φ ψ) (imply ψ φ)

  -- 選言
  def lor (φ ψ : Formula S) : Formula S := imply (lnot φ) ψ

  -- 存在量化子
  def lexists (x : Variable) (φ : Formula S) : Formula S := lnot (lforall x (lnot φ))

  -- Leanの再帰定義のために命題の大きさを定める
  def size : Formula S → Nat
  | .bot => 1
  | .land φ ψ => size φ + size ψ + 1
  | .imply φ ψ => size φ + size ψ + 1
  | .pred _ _ => 1
  | .lforall _ φ => size φ + 1

  -- 命題から自由変数の集まりを返す
  def free_vars : Formula S -> VarSet
  | .bot => ∅
  | .land φ ψ => free_vars φ ∪ free_vars ψ
  | .imply φ ψ => free_vars φ ∪ free_vars ψ
  | .pred _ args => VarSet.replace (fun i => Term.vars (args i))
  | .lforall x φ => free_vars φ \ {x}

  -- 命題から束縛変数の集まりを返す
  def bound_vars : Formula S → VarSet
  | .bot => ∅
  | .land φ ψ => bound_vars φ ∪ bound_vars ψ
  | .imply φ ψ => bound_vars φ ∪ bound_vars ψ
  | .pred _ _ => ∅
  | .lforall x φ => bound_vars φ ∪ {x}

  def all_vars (φ : Formula S) : VarSet :=
    free_vars φ ∪ bound_vars φ

  lemma all_vars_land
    {φ ψ : Formula S} :
    all_vars (.land φ ψ) = all_vars φ ∪ all_vars ψ
  := by
    simp [all_vars, free_vars, bound_vars]
    ac_rfl

  lemma all_vars_imply
    {φ ψ : Formula S} :
    all_vars (.imply φ ψ) = all_vars φ ∪ all_vars ψ
  := by
    simp [all_vars, free_vars, bound_vars]
    ac_rfl

  lemma all_vars_lforall
    {x : Variable} {φ : Formula S} :
    all_vars (.lforall x φ) = {x} ∪ (all_vars φ)
  := by
    ext v
    simp [all_vars, free_vars, bound_vars, or_comm]
    by_cases v_eq_x : v = x <;> simp [v_eq_x]

  -- 命題内の変数への変数の代入
  def rename (x y : Variable) : Formula S → Formula S
  | .bot => .bot
  | .land φ ψ => .land (rename x y φ) (rename x y ψ)
  | .imply φ ψ => .imply (rename x y φ) (rename x y ψ)
  | .pred p args => .pred p (fun i => Term.substitute x (Term.var y) (args i))
  | .lforall z φ => if z = x then .lforall z φ else .lforall z (rename x y φ)

  lemma rename_size
    {x y : Variable} {φ : Formula S} :
    size (rename x y φ) = size φ
  := by
    induction φ with
    | bot => simp [rename, size]
    | land φ1 φ2 ihφ1 ihφ2 => simp [rename, size, ihφ1, ihφ2]
    | imply φ1 φ2 ihφ1 ihφ2 => simp [rename, size, ihφ1, ihφ2]
    | pred p args => simp [rename, size]
    | lforall z ψ ih => by_cases z_eq_x : z = x <;> simp [rename, size, z_eq_x, ih]

  lemma rename_preserve
    {x y z : Variable} {φ : Formula S}
    (x_in_FVφ : x ∈ free_vars φ) (x_neq_y : x ≠ y) :
    x ∈ free_vars (rename y z φ)
  := by
    induction φ with
    | bot => simp [free_vars] at x_in_FVφ
    | land φ1 φ2 ihφ1 ihφ2 =>
      simp [free_vars] at x_in_FVφ
      simpa [rename, free_vars] using x_in_FVφ.imp ihφ1 ihφ2
    | imply φ1 φ2 ihφ1 ihφ2 =>
      simp [free_vars] at x_in_FVφ
      simpa [rename, free_vars] using x_in_FVφ.imp ihφ1 ihφ2
    | pred p args =>
      simp [free_vars] at x_in_FVφ
      obtain ⟨i, x_in_arg⟩ := x_in_FVφ
      simpa [rename, free_vars, VarSet.mem_replace] using
        ⟨i, Term.subst_preserve x_in_arg x_neq_y⟩
    | lforall w ψ ih =>
      simp [free_vars] at x_in_FVφ
      by_cases w_eq_y : w = y
      · simpa [rename, free_vars, w_eq_y] using x_in_FVφ
      · simpa [rename, free_vars, w_eq_y] using And.intro (ih x_in_FVφ.1) x_in_FVφ.2

  lemma rename_nonvar
    {x y : Variable} {φ : Formula S}
    (x_nin_FVφ : x ∉ free_vars φ) :
    rename x y φ = φ
  := by
    induction φ with
    | bot => simp [rename]
    | land φ1 φ2 ihφ1 ihφ2 =>
      simp [free_vars] at x_nin_FVφ
      simp [rename, ihφ1 x_nin_FVφ.1, ihφ2 x_nin_FVφ.2]
    | imply φ1 φ2 ihφ1 ihφ2 =>
      simp [free_vars] at x_nin_FVφ
      simp [rename, ihφ1 x_nin_FVφ.1, ihφ2 x_nin_FVφ.2]
    | pred p args =>
      simp [free_vars] at x_nin_FVφ
      simp [rename, Term.subst_nonvar, x_nin_FVφ]
    | lforall z ψ ih =>
      simp [free_vars] at x_nin_FVφ
      by_cases z_eq_x : z = x
      . simp [rename, z_eq_x]
      . simp [rename, z_eq_x, ih (mt x_nin_FVφ (Ne.symm z_eq_x))]

  lemma rename_clean
    {x y : Variable} {φ : Formula S}
    (x_neq_y : x ≠ y) :
    x ∉ free_vars (rename x y φ)
  := by
    induction φ with
    | bot => simp [rename, free_vars]
    | land φ1 φ2 ihφ1 ihφ2 => simp [rename, free_vars, ihφ1, ihφ2]
    | imply φ1 φ2 ihφ1 ihφ2 => simp [rename, free_vars, ihφ1, ihφ2]
    | pred p args => simp [rename, free_vars, Term.subst_clean, x_neq_y]
    | lforall z ψ ih =>
      by_cases z_eq_x : z = x <;> simp [rename, free_vars, z_eq_x, ih]

  lemma rename_cancel
    {x y : Variable} {φ : Formula S}
    (x_neq_y : x ≠ y) (y_nin_φ : y ∉ all_vars φ) :
    rename y x (rename x y φ) = φ
  := by
    induction φ with
    | bot => rfl
    | land φ1 φ2 ihφ1 ihφ2 =>
      simp [all_vars_land] at y_nin_φ
      simp [rename, ihφ1 y_nin_φ.1, ihφ2 y_nin_φ.2]
    | imply φ1 φ2 ihφ1 ihφ2 =>
      simp [all_vars_imply] at y_nin_φ
      simp [rename, ihφ1 y_nin_φ.1, ihφ2 y_nin_φ.2]
    | pred p args =>
      have y_nin_arg : ∀ i, y ∉ Term.vars (args i) := by
        simpa [all_vars, free_vars, bound_vars] using y_nin_φ
      simp [rename, Term.subst_cancel, y_nin_arg]
    | lforall z ψ ih =>
      simp [all_vars_lforall] at y_nin_φ
      obtain ⟨y_neq_z, y_nin_ψ⟩ := y_nin_φ
      by_cases z_eq_x : z = x
      · have y_nin_FVψ : y ∉ free_vars ψ := by
          simp [all_vars] at y_nin_ψ
          exact y_nin_ψ.1
        simp [rename, x_neq_y, rename_nonvar y_nin_FVψ, z_eq_x]
      · simp [rename, z_eq_x, Ne.symm y_neq_z, ih y_nin_ψ]

  -- 命題内の変数への項の代入
  def substitute (x : Variable) (t : Term S) : Formula S → Formula S
  | .bot => bot
  | .land φ ψ => land (substitute x t φ) (substitute x t ψ)
  | .imply φ ψ => imply (substitute x t φ) (substitute x t ψ)
  | .pred p args => pred p (fun i => Term.substitute x t (args i))
  | .lforall y φ =>
    if x = y then
      lforall y φ
    else if x ∉ free_vars φ then
      lforall y φ
    else if y ∉ Term.vars t then
      lforall y (substitute x t φ)
    else
      let z := VarSet.fresh (Term.vars t ∪ all_vars φ ∪ {x})
      lforall z (substitute x t (rename y z φ))
  termination_by
    χ => size χ
  decreasing_by
    all_goals
      simp [size, rename_size] <;> omega

  lemma rename_eq_substitute
    {x y : Variable} {φ : Formula S}
    (y_nin_φ : y ∉ all_vars φ) :
    rename x y φ = substitute x (Term.var y) φ
  := by
    induction φ with
    | bot => simp [rename, substitute]
    | land φ1 φ2 ihφ1 ihφ2 =>
      simp [all_vars_land] at y_nin_φ
      simp [rename, substitute, ihφ1 y_nin_φ.1, ihφ2 y_nin_φ.2]
    | imply φ1 φ2 ihφ1 ihφ2 =>
      simp [all_vars_imply] at y_nin_φ
      simp [rename, substitute, ihφ1 y_nin_φ.1, ihφ2 y_nin_φ.2]
    | pred p args => simp [rename, substitute]
    | lforall z ψ ih =>
      simp [all_vars_lforall] at y_nin_φ
      obtain ⟨y_neq_z, y_nin_ψ⟩ := y_nin_φ
      by_cases z_eq_x : z = x
      . simp [rename, substitute, z_eq_x]
      . by_cases x_in_FVψ : x ∈ free_vars ψ
        · have z_nin_y : z ∉ Term.vars (Term.var (S := S) y) := by
            simp [Term.vars, Ne.symm y_neq_z]
          simp [rename, substitute, z_eq_x, Ne.symm z_eq_x, x_in_FVψ, z_nin_y, ih y_nin_ψ]
        · simp [rename, substitute, z_eq_x, Ne.symm z_eq_x, x_in_FVψ, rename_nonvar x_in_FVψ]

  lemma subst_self
    {x : Variable} {φ : Formula S} :
    substitute x (Term.var x) φ = φ
  := by
    induction φ with
    | bot => simp [substitute]
    | land φ ψ ihφ ihψ => simp [substitute, ihφ, ihψ]
    | imply φ ψ ihφ ihψ => simp [substitute, ihφ, ihψ]
    | pred p args => simp [substitute, Term.subst_self]
    | lforall y φ ih => by_cases y_eq_x : y = x <;> simp [substitute, y_eq_x, Term.vars, ih]

  lemma subst_clean
    {x y : Variable} {φ : Formula S}
    (x_neq_y : x ≠ y) :
    x ∉ free_vars (substitute x (Term.var y) φ)
  := by
    induction hsize : size φ using Nat.strong_induction_on generalizing φ with
    | h n ih =>
      cases φ with
      | bot => simp [substitute, free_vars]
      | land φ1 φ2 =>
        simp [size] at hsize
        have ihφ1 : x ∉ free_vars (substitute x (Term.var y) φ1) := by
          exact ih (size φ1) (by omega) rfl
        have ihφ2 : x ∉ free_vars (substitute x (Term.var y) φ2) := by
          exact ih (size φ2) (by omega) rfl
        simp [substitute, free_vars, ihφ1, ihφ2]
      | imply φ1 φ2 =>
        simp [size] at hsize
        have ihφ1 : x ∉ free_vars (substitute x (Term.var y) φ1) := by
          exact ih (size φ1) (by omega) rfl
        have ihφ2 : x ∉ free_vars (substitute x (Term.var y) φ2) := by
          exact ih (size φ2) (by omega) rfl
        simp [substitute, free_vars, ihφ1, ihφ2]
      | pred p args =>
        simp [substitute, free_vars, Term.subst_clean, x_neq_y]
      | lforall z ψ =>
        simp [size] at hsize
        by_cases x_eq_z : x = z
        · simp [substitute, free_vars, x_eq_z]
        · by_cases x_in_FVψ : x ∈ free_vars ψ
          . let t := Term.var (S:=S) y
            by_cases z_eq_y : z = y
            · have z_in_t : z ∈ Term.vars t := by
                simp [z_eq_y, t, Term.vars]
              let w := VarSet.fresh (Term.vars t ∪ all_vars ψ ∪ {x})
              let ψr := rename z w ψ
              let ψs := substitute x t ψr
              have h_nin_FVallψs : x ∉ free_vars (lforall w ψs) := by
                have x_nin_FVψs : x ∉ free_vars ψs := by
                  have hsize_ψr : size ψr < n := by
                    rw [rename_size]
                    omega
                  exact ih (size ψr) hsize_ψr rfl
                simp [free_vars, x_nin_FVψs]
              simpa [substitute, x_eq_z, x_in_FVψ, z_in_t, t, w, ψr, ψs] using h_nin_FVallψs
            · have z_nin_t : z ∉ Term.vars t := by
                simp [z_eq_y, t, Term.vars]
              have ihψ : x ∉ free_vars (substitute x t ψ) := by
                exact ih (size ψ) (by omega) rfl
              have x_nin_FVall : x ∉ free_vars (lforall z (substitute x t ψ)) := by
                simp [free_vars, ihψ]
              simpa [substitute, x_eq_z, x_in_FVψ, z_nin_t, t] using x_nin_FVall
          · simp [substitute, free_vars, x_eq_z, x_in_FVψ]

  lemma subst_new
    {x y : Variable} {φ : Formula S}
    (x_in_FVφ : x ∈ free_vars φ) :
    y ∈ free_vars (substitute x (Term.var y) φ)
  := by
    induction hsize : size φ using Nat.strong_induction_on generalizing φ with
    | h n ih =>
      cases φ with
      | bot => simp [free_vars] at x_in_FVφ
      | land φ1 φ2 =>
        simp [size] at hsize
        simp [free_vars] at x_in_FVφ
        rcases x_in_FVφ with x_in_FVφ1 | x_in_FVφ2
        . have ihφ1 : y ∈ free_vars (substitute x (Term.var y) φ1) := by
            exact ih (size φ1) (by omega) x_in_FVφ1 rfl
          simp [substitute, free_vars, ihφ1]
        . have ihφ2 : y ∈ free_vars (substitute x (Term.var y) φ2) := by
            exact ih (size φ2) (by omega) x_in_FVφ2 rfl
          simp [substitute, free_vars, ihφ2]
      | imply φ1 φ2 =>
        simp [size] at hsize
        simp [free_vars] at x_in_FVφ
        rcases x_in_FVφ with x_in_FVφ1 | x_in_FVφ2
        . have ihφ1 : y ∈ free_vars (substitute x (Term.var y) φ1) := by
            exact ih (size φ1) (by omega) x_in_FVφ1 rfl
          simp [substitute, free_vars, ihφ1]
        . have ihφ2 : y ∈ free_vars (substitute x (Term.var y) φ2) := by
            exact ih (size φ2) (by omega) x_in_FVφ2 rfl
          simp [substitute, free_vars, ihφ2]
      | pred p args =>
        obtain ⟨i, arg_in_FVφ⟩ := (VarSet.mem_replace).1 x_in_FVφ
        have arg_in_argxtoy : ∃ i, y ∈ Term.vars (Term.substitute x (Term.var y) (args i)) := by
          exact ⟨i, Term.subst_new arg_in_FVφ⟩
        simpa [substitute, free_vars, VarSet.mem_replace] using arg_in_argxtoy
      | lforall z ψ =>
        simp [size] at hsize
        simp [free_vars] at x_in_FVφ
        obtain ⟨x_in_FVψ, x_neq_z⟩ := x_in_FVφ
        let t := Term.var (S:=S) y
        by_cases z_eq_y : z = y
        · have z_in_t : z ∈ Term.vars t := by
            simpa [Term.vars, t] using z_eq_y
          let w := VarSet.fresh (Term.vars t ∪ all_vars ψ ∪ {x})
          let ψr := rename z w ψ
          let ψs := substitute x t ψr
          have y_in_allψs : y ∈ free_vars (lforall w ψs) := by
            have y_in_ψs : y ∈ free_vars ψs := by
              have ψr_lt_n : size ψr < n := by
                simp [ψr, rename_size]
                omega
              have x_in_ψr : x ∈ free_vars ψr := by
                exact rename_preserve x_in_FVψ x_neq_z
              exact ih (size ψr) ψr_lt_n x_in_ψr (by simp [ψr, rename_size])
            have y_neq_w : y ≠ w := by
              apply VarSet.fresh_not_mem
              simp [Term.vars, t]
            simp [free_vars, y_neq_w, y_in_ψs]
          simpa [substitute, x_neq_z, x_in_FVψ, z_in_t, t, w, ψr, ψs] using y_in_allψs
        · have z_nin_t : z ∉ Term.vars t := by
            simpa [t, Term.vars] using z_eq_y
          have ihψ : y ∈ free_vars (substitute x t ψ) := by
            exact ih (size ψ) (by omega) x_in_FVψ rfl
          have y_in_FVall :
              y ∈ free_vars (lforall z (substitute x t ψ)) := by
            simpa [free_vars, Ne.symm z_eq_y] using ihψ
          simpa [substitute, x_neq_z, x_in_FVψ, z_nin_t, t] using y_in_FVall

end Formula

-- ## 古典論理の推論規則

-- 推論規則
inductive Derive : Formula S -> Formula S -> Prop
| ax {φ: Formula S} :
  Derive φ φ
| cut {φ ψ χ: Formula S} :
  Derive φ ψ -> Derive ψ χ -> Derive φ χ
| intro_and {φ ψ χ: Formula S} :
  Derive φ ψ -> Derive φ χ -> Derive φ (Formula.land ψ χ)
| elim_and1 {φ ψ: Formula S} :
  Derive (Formula.land φ ψ) φ
| elim_and2 {φ ψ: Formula S} :
  Derive (Formula.land φ ψ) ψ
| intro_imp {φ ψ χ: Formula S} :
  Derive (Formula.land φ ψ) χ -> Derive φ (Formula.imply ψ χ)
| elim_imp {φ ψ: Formula S} :
  Derive (Formula.land φ (Formula.imply φ ψ)) ψ
| dne {φ: Formula S} :
  Derive (Formula.imply (Formula.imply φ Formula.bot) Formula.bot) φ
| intro_forall {φ ψ: Formula S} {x : Variable} :
  (x ∉ Formula.free_vars φ) -> Derive φ ψ -> Derive φ (Formula.lforall x ψ)
| elim_forall {φ: Formula S} {x : Variable} {t : Term S} :
  -- tの自由変数でありφの束縛変数であるものは、置換できれいにする。
  Derive (Formula.lforall x φ) (Formula.substitute x t φ)

-- Derive が推移律を満たすことを、Leanに教える。
instance : Trans (Derive (S := S)) (Derive (S := S)) (Derive (S := S)) where
  trans := Derive.cut (S := S)

namespace Derive

  open Formula

  theorem land_mono
    {φ1 φ2 ψ1 ψ2 : Formula S }
    (hφ : Derive φ1 φ2) (hψ : Derive ψ1 ψ2) :
    Derive (land φ1 ψ1) (land φ2 ψ2)
  := by
    apply intro_and
    . exact cut elim_and1 hφ
    . exact cut elim_and2 hψ

  theorem imply_mono
    {φ1 φ2 ψ1 ψ2 : Formula S }
    (hφ : Derive φ1 φ2) (hψ : Derive ψ1 ψ2) :
    Derive (imply φ2 ψ1) (imply φ1 ψ2)
  := by
    apply intro_imp
    calc
      Derive (land (imply φ2 ψ1) φ1) (land φ2 (imply φ2 ψ1)) := by
        apply intro_and
        . exact cut elim_and2 hφ
        . exact elim_and1
      Derive _ ψ1 := elim_imp
      Derive _ ψ2 := hψ

  theorem lforall_mono
    {x : Variable} {φ ψ : Formula S}
    (h : Derive φ ψ) :
    Derive (lforall x φ) (lforall x ψ)
  := by
    have x_nin_FVxφ : x ∉ free_vars (lforall x φ) := by
      simp [free_vars]
    apply intro_forall x_nin_FVxφ
    calc
      Derive (lforall x φ) (substitute x (Term.var x) φ) := elim_forall
      Derive _ φ := by simpa [subst_self] using ax
      Derive _ ψ := h

end Derive

-- 双方向推論
def Equiv (φ ψ : Formula S) : Prop := And (Derive φ ψ) (Derive ψ φ)

namespace Equiv

  open Derive Formula

  lemma refl
    {φ : Formula S} :
    Equiv φ φ
  := ⟨.ax, .ax⟩

  lemma symm
    {φ ψ : Formula S}
    (h : Equiv φ ψ) :
    Equiv ψ φ
  := And.intro h.2 h.1

  lemma trans
    {φ ψ χ : Formula S}
    (h1 : Equiv φ ψ) (h2 : Equiv ψ χ) :
    Equiv φ χ
  := And.intro (.cut h1.1 h2.1) (.cut h2.2 h1.2)

  lemma land_mono
    {φ1 φ2 ψ1 ψ2 : Formula S}
    (hφ : Equiv φ1 φ2) (hψ : Equiv ψ1 ψ2) :
    Equiv (land φ1 ψ1) (land φ2 ψ2)
  := by
    exact ⟨Derive.land_mono hφ.1 hψ.1, Derive.land_mono hφ.2 hψ.2⟩

  lemma imply_mono
    {φ1 φ2 ψ1 ψ2 : Formula S}
    (hφ : Equiv φ1 φ2) (hψ : Equiv ψ1 ψ2) :
    Equiv (imply φ1 ψ1) (imply φ2 ψ2)
  := by
    exact ⟨Derive.imply_mono hφ.2 hψ.1, Derive.imply_mono hφ.1 hψ.2⟩

  lemma lforall_mono
    {x : Variable} {φ ψ : Formula S}
    (h : Equiv φ ψ) :
    Equiv (Formula.lforall x φ) (Formula.lforall x ψ)
  := by
    exact ⟨Derive.lforall_mono h.1, Derive.lforall_mono h.2⟩

  lemma lnot_mono
    {φ ψ : Formula S}
    (h : Equiv φ ψ) :
    Equiv (Formula.lnot φ) (Formula.lnot ψ)
  := by
    simpa [Formula.lnot] using imply_mono h Equiv.refl

  lemma iff_mono
    {φ1 φ2 ψ1 ψ2 : Formula S}
    (hφ : Equiv φ1 φ2) (hψ : Equiv ψ1 ψ2) :
    Equiv (Formula.iff φ1 ψ1) (Formula.iff φ2 ψ2)
  := by
    simpa [Formula.iff] using land_mono (imply_mono hφ hψ) (imply_mono hψ hφ)

  lemma lor_mono
    {φ1 φ2 ψ1 ψ2 : Formula S}
    (hφ : Equiv φ1 φ2) (hψ : Equiv ψ1 ψ2) :
    Equiv (Formula.lor φ1 ψ1) (Formula.lor φ2 ψ2)
  := by
    simpa [Formula.lor] using imply_mono (lnot_mono hφ) hψ

  lemma lexists
    {x : Variable} {φ ψ : Formula S}
    (h : Equiv φ ψ) :
    Equiv (Formula.lexists x φ) (Formula.lexists x ψ)
  := by
    simpa [Formula.lexists] using lnot_mono (lforall_mono (lnot_mono h))

end Equiv

-- Equiv が推移律を満たすことを、Leanに教える。
instance : Trans (Equiv (S := S)) (Equiv (S := S)) (Equiv (S := S)) where
  trans := Equiv.trans

namespace Formula

  open Derive

  lemma subst_cancel
    {x y : Variable} {φ : Formula S}
    (y_nin_FVφ : y ∉ free_vars φ) :
    Equiv (substitute y (Term.var x) (substitute x (Term.var y) φ)) φ
  := by
    induction hsize : size φ using Nat.strong_induction_on generalizing φ x y with
    | h n ih =>
      cases φ with
      | bot =>
        constructor <;> simpa [substitute] using ax
      | land φ1 φ2 =>
        simp [size] at hsize
        simp [free_vars, not_or] at y_nin_FVφ
        simp only [substitute]
        apply Equiv.land_mono
        · exact ih (size φ1) (by omega) y_nin_FVφ.1 rfl
        · exact ih (size φ2) (by omega) y_nin_FVφ.2 rfl
      | imply φ1 φ2 =>
        simp [size] at hsize
        simp [free_vars, not_or] at y_nin_FVφ
        simp only [substitute]
        apply Equiv.imply_mono
        · exact ih (size φ1) (by omega) y_nin_FVφ.1 rfl
        · exact ih (size φ2) (by omega) y_nin_FVφ.2 rfl
      | pred p args =>
        simp [free_vars] at y_nin_FVφ
        simpa [substitute, y_nin_FVφ, Term.subst_cancel] using Equiv.refl
      | lforall z ψ =>
        simp [size] at hsize
        simp [free_vars] at y_nin_FVφ
        by_cases x_eq_z : x = z
        · by_cases y_eq_x : y = x
          . simpa [substitute, x_eq_z, y_eq_x] using Equiv.refl
          · have y_nin_FVψ : y ∉ free_vars ψ := by
              have y_neq_z : y ≠ z := by
                simpa [x_eq_z] using y_eq_x
              exact mt y_nin_FVφ y_neq_z
            simpa [substitute, x_eq_z, y_nin_FVψ] using Equiv.refl
        . by_cases x_in_FVψ : x ∈ free_vars ψ
          . by_cases y_eq_z : y = z
            . let w := VarSet.fresh (Term.vars (Term.var (S:=S) z) ∪ all_vars ψ ∪ {x})
              have w_nin_ψ : w ∉ all_vars ψ := by
                intro w_in_ψ
                have w_neq_w : w ≠ w := by
                  apply VarSet.fresh_not_mem
                  simp [w_in_ψ]
                exact w_neq_w rfl
              have z_neq_w : z ≠ w := by
                apply VarSet.fresh_not_mem
                simp [Term.vars]
              have x_neq_w : x ≠ w := by
                apply VarSet.fresh_not_mem
                simp
              let ψ_rename := rename z w ψ
              calc
                Equiv _ (substitute z (Term.var x) (substitute x (Term.var z) (lforall z ψ))) := by
                  simpa [y_eq_z] using Equiv.refl
                Equiv _ (substitute z (Term.var x) (lforall w (substitute x (Term.var z) ψ_rename))) := by
                  simpa [substitute, x_eq_z, x_in_FVψ, Term.vars, w, ψ_rename] using Equiv.refl
                Equiv _ (lforall w (substitute z (Term.var x) (substitute x (Term.var z) ψ_rename))) := by
                  have z_in_new : z ∈ free_vars (substitute x (Term.var z) ψ_rename) := by
                    have x_in_FVψrename : x ∈ free_vars ψ_rename := by
                      exact rename_preserve x_in_FVψ x_eq_z
                    exact subst_new x_in_FVψrename
                  simpa [substitute, z_neq_w, z_in_new, Ne.symm x_neq_w, Term.vars] using Equiv.refl
                Equiv _ (lforall w ψ_rename) := by
                  apply Equiv.lforall_mono
                  have z_nin_FVψ_rename : z ∉ free_vars ψ_rename := by
                    exact rename_clean z_neq_w
                  exact ih (size ψ_rename) (by simp [ψ_rename, rename_size]; omega) z_nin_FVψ_rename rfl
                Equiv _ (lforall w (substitute z (Term.var w) ψ)) := by
                   simpa [rename_eq_substitute w_nin_ψ, ψ_rename] using Equiv.refl
                Equiv _ (lforall z ψ) := by
                  have w_nin_FVψ : w ∉ free_vars ψ := by
                    simp [all_vars] at w_nin_ψ
                    exact w_nin_ψ.1
                  constructor
                  . calc
                      Derive _ (lforall z (substitute w (Term.var z) (substitute z (Term.var w) ψ))) := by
                        have z_nin_FVwψsub : z ∉ free_vars (lforall w (substitute z (Term.var w) ψ)) := by
                          have z_nin_FVψ_rename : z ∉ free_vars (substitute z (Term.var w) ψ) := by
                            exact subst_clean z_neq_w
                          simp [free_vars, z_nin_FVψ_rename]
                        exact intro_forall z_nin_FVwψsub elim_forall
                      Derive _ _ := by
                        apply Derive.lforall_mono
                        have ihψ : Equiv (substitute w (Term.var z) (substitute z (Term.var w) ψ)) ψ := by
                          exact ih (size ψ) (by omega) (x := z) (y := w) w_nin_FVψ rfl
                        exact ihψ.1
                  . have w_nin_FVzψ : w ∉ free_vars (lforall z ψ) := by
                      simp [free_vars, w_nin_FVψ]
                    exact intro_forall w_nin_FVzψ elim_forall
            · have y_in_ψnew : y ∈ free_vars (substitute x (Term.var y) ψ) := subst_new x_in_FVψ
              have ihψ : Equiv (substitute y (Term.var x) (substitute x (Term.var y) ψ)) ψ := by
                have y_nin_FVψ : y ∉ free_vars ψ :=
                    mt y_nin_FVφ y_eq_z
                exact ih (size ψ) (by omega) y_nin_FVψ rfl
              simpa [substitute, x_eq_z, x_in_FVψ, y_eq_z, Term.vars, eq_comm, y_in_ψnew] using Equiv.lforall_mono ihψ
          . by_cases y_eq_z : y = z
            . simpa [substitute, x_in_FVψ, y_eq_z] using Equiv.refl
            . have y_nin_FVψ : y ∉ free_vars ψ :=
                mt y_nin_FVφ y_eq_z
              simpa [substitute, x_eq_z, x_in_FVψ, y_eq_z, y_nin_FVψ] using Equiv.refl

-- end Formula

-- ## 古典論理の重要な定理

-- -- Lean上の表記を簡潔にするために
notation "bot" => Formula.bot
notation "top" => Formula.top
prefix:58 "lnot" => Formula.lnot
infixr:57 " land " => Formula.land
infixr:56 " lor " => Formula.lor
infixr:55 " imply " => Formula.imply
infixr:54 " iff " => Formula.iff
notation:53 "lforall" x "," φ => Formula.lforall x φ
notation:52 "lexists" x "," φ => Formula.lexists x φ
notation:51 φ " vdash " ψ => Derive φ ψ

open Derive

-- Modus Ponens
theorem modus_ponens
  {φ ψ χ : Formula S}
  (h1 : φ vdash ψ) (h2 : φ vdash ψ imply χ) :
  φ vdash χ
:= by
  calc
    φ vdash ψ land (ψ imply χ) := by
      apply intro_and
      . exact h1
      . exact h2
    _ vdash χ := elim_imp

-- 弱化
theorem weaken
  {φ ψ χ : Formula S}
  (h : φ vdash ψ) :
  φ land χ vdash ψ
:= by
  calc
    φ land χ vdash φ := elim_and1
    _ vdash ψ := h

-- 連言の冪等律
theorem land_idempotence
  {φ : Formula S} :
  Equiv φ (φ land φ)
:= by
  constructor
  . apply intro_and
    . exact ax
    . exact ax
  . exact elim_and1

-- 連言の結合律
theorem land_associative1
  {φ ψ χ : Formula S} :
  Equiv ((φ land ψ) land χ) (φ land (ψ land χ))
:= by
  constructor
  . apply intro_and
    . calc
        (φ land ψ) land χ vdash φ land ψ := elim_and1
        _ vdash φ := elim_and1
    . apply intro_and
      . calc
        (φ land ψ) land χ vdash φ land ψ := elim_and1
        _ vdash ψ := elim_and2
      . exact elim_and2
  . apply intro_and
    . apply intro_and
      . exact elim_and1
      . calc
        φ land (ψ land χ) vdash (ψ land χ) := elim_and2
        _ vdash ψ := elim_and1
    . calc
      φ land (ψ land χ) vdash (ψ land χ) := elim_and2
      _ vdash χ := elim_and2

-- 連言の交換律
theorem land_exchange
  {φ ψ : Formula S} :
  (φ land ψ) vdash (ψ land φ)
:= by
  apply intro_and
  . exact elim_and2
  . exact elim_and1

-- 仮言三段論法
theorem hypothetical_syllogism
  {φ ψ χ : Formula S} :
  ((φ imply ψ) land (ψ imply χ)) vdash (φ imply χ)
:= by
  apply intro_imp
  let Γ := ((φ imply ψ) land (ψ imply χ)) land φ
  apply modus_ponens
  . apply modus_ponens
    . exact elim_and2
    . calc
      Γ vdash (φ imply ψ) land (ψ imply χ) := elim_and1
      _ vdash φ imply ψ := elim_and1
  . calc
    Γ vdash (φ imply ψ) land (ψ imply χ) := elim_and1
    _ vdash ψ imply χ := elim_and2

-- 逆演繹定理
theorem converse_deduction
  {φ ψ χ : Formula S}
  (h : φ vdash ψ imply χ) :
  φ land ψ vdash χ
:= by
  apply modus_ponens
  . exact elim_and2
  . calc
    _ vdash φ := elim_and1
    _ vdash ψ imply χ := h

-- Lukasiewiczの第一公理
theorem lukasiewicz
  {φ ψ : Formula S} :
  φ vdash ψ imply φ
:= by
  exact intro_imp elim_and1

-- ## 否定

-- 否定の導入則
theorem intro_not
  {φ ψ : Formula S}
  (h : (φ land ψ) vdash bot) :
  φ vdash lnot ψ
:= by
  exact intro_imp h

-- 否定の除去則
theorem elim_not
  {φ : Formula S} :
  φ land lnot φ vdash bot
:= elim_imp

-- 二重否定導入
theorem intro_dn
  {φ : Formula S} :
  φ vdash lnot lnot φ
:= by
  exact intro_imp elim_not

-- 爆発律
theorem explosion
  {φ : Formula S} :
  bot vdash φ
:= by
  calc
    bot vdash lnot lnot φ := intro_imp elim_and1
    _ vdash _ := dne

-- 否定含意からの前件の取り出し
theorem not_imply_elim
  {φ ψ : Formula S} :
  lnot (φ imply ψ) vdash φ
:= by
  calc
    lnot (φ imply ψ) vdash lnot lnot φ := by
      apply intro_not
      let Γ := (lnot (φ imply ψ)) land (lnot φ)
      apply modus_ponens
      . apply intro_imp
        calc
          Γ land φ vdash bot := by
            apply modus_ponens
            . exact elim_and2
            . calc
              Γ land φ vdash Γ := elim_and1
              _ vdash lnot φ := elim_and2
          _ vdash ψ := explosion
      . exact elim_and1
    _ vdash φ := dne

-- Pierce則
theorem peirce
  {φ ψ : Formula S} :
  (φ imply ψ) imply φ vdash φ
:= by
  calc
    (φ imply ψ) imply φ vdash lnot lnot φ := by
      apply intro_imp
      let Γ := ((φ imply ψ) imply φ) land lnot φ
      apply modus_ponens
      . apply modus_ponens
        . calc
            Γ vdash lnot φ := elim_and2
            _ vdash φ imply ψ := by
              apply intro_imp
              calc
                _ vdash φ land lnot φ := land_exchange
                _ vdash bot := elim_not
                _ vdash ψ := explosion
        . exact elim_and1
      . exact elim_and2
    _ vdash _ := dne

-- 背理法
theorem proof_contradiction
  {φ ψ : Formula S}
  (h : φ land lnot ψ vdash bot) :
  φ vdash ψ
:= by
  calc
    φ vdash lnot lnot ψ := intro_imp h
    _ vdash ψ := dne

-- 対偶法
theorem proof_contraposition
  {φ ψ : Formula S} :
  (lnot φ vdash lnot ψ) <-> (ψ vdash φ)
:= by
  constructor
  . intro h1
    calc
      ψ vdash lnot lnot φ := by
        apply intro_imp
        apply modus_ponens
        . exact elim_and1
        . calc
            ψ land lnot φ vdash lnot φ := elim_and2
            _ vdash lnot ψ := h1
      _ vdash φ := dne
  . intro h2
    apply intro_imp
    apply modus_ponens
    . calc
        lnot φ land ψ vdash ψ := elim_and2
        _ vdash φ := h2
    . exact elim_and1

-- ## 同値

-- 連言への代入
theorem substitution_iff
  {φ ψ χ : Formula S} :
  (φ land χ) land (φ iff ψ) vdash ψ land χ
:= by
  apply intro_and
  . apply modus_ponens
    . calc
      _ vdash φ land χ := elim_and1
      _ vdash φ := elim_and1
    . calc
      _ vdash φ iff ψ := elim_and2
      _ vdash φ imply ψ := elim_and1
  . calc
    _ vdash φ land χ := elim_and1
    _ vdash χ := elim_and2

-- 含意の前件への代入
theorem substitution_iff_to_imply1
  {φ ψ χ : Formula S} :
  (φ imply ψ) land (φ iff χ) vdash χ imply ψ
:= by
  calc
    (φ imply ψ) land (φ iff χ) vdash (χ imply φ) land (φ imply ψ) := by
      apply intro_and
      . calc
          (φ imply ψ) land (φ iff χ) vdash φ iff χ := elim_and2
          _ vdash χ imply φ := elim_and2
      . exact elim_and1
    _ vdash χ imply ψ := hypothetical_syllogism

-- 含意の後件への代入
theorem substitution_iff_to_imply2
  {φ ψ χ : Formula S} :
  (φ imply ψ) land (ψ iff χ) vdash φ imply χ
:= by
  calc
    (φ imply ψ) land (ψ iff χ) vdash (φ imply ψ) land (ψ imply χ) := by
      apply intro_and
      . exact elim_and1
      . calc
          (φ imply ψ) land (ψ iff χ) vdash ψ iff χ := elim_and2
          _ vdash ψ imply χ := elim_and1
    _ vdash φ imply χ := hypothetical_syllogism

-- 真理の導入則
theorem intro_top
  {φ : Formula S} :
  φ vdash top
:= by
  exact intro_imp elim_and2

lemma intro_imp_from_derivation
  {φ ψ : Formula S}
  (h : φ vdash ψ) :
  top vdash φ imply ψ
:= by
  apply intro_imp
  calc
    top land φ vdash φ := elim_and2
    _ vdash ψ := h

lemma derive_from_top_imp
  {φ ψ : Formula S}
  (h : top vdash φ imply ψ) :
  φ vdash ψ
:= by
  apply modus_ponens
  . exact ax
  . calc
      φ vdash top := intro_top
      _ vdash φ imply ψ := h

lemma equiv_iff_top_derives_iff
  {φ ψ : Formula S} :
  Equiv φ ψ <-> top vdash φ iff ψ
:= by
  constructor
  . rintro ⟨hφψ, hψφ⟩
    apply intro_and
    . exact intro_imp_from_derivation hφψ
    . exact intro_imp_from_derivation hψφ
  . intro h
    constructor
    . apply derive_from_top_imp
      calc
        top vdash φ iff ψ := h
        _ vdash φ imply ψ := elim_and1
    . apply derive_from_top_imp
      calc
        top vdash φ iff ψ := h
        _ vdash ψ imply φ := elim_and2

-- 連言の単位律
theorem land_unit
  {φ : Formula S} :
  Equiv φ (top land φ)
:= by
  constructor
  . apply intro_and
    . exact intro_top
    . exact ax
  . exact elim_and2

-- ## 選言

-- 選言の導入則１
theorem intro_or1
  {φ ψ : Formula S} :
  φ vdash φ lor ψ
:= by
  apply intro_imp
  calc
    φ land lnot φ vdash bot := elim_not
    _ vdash ψ := explosion

-- 選言の導入則２
theorem intro_or2
  {φ ψ : Formula S} :
  φ vdash ψ lor φ
:= lukasiewicz

-- 選言の除去則
theorem elim_or
  {φ ψ χ ω : Formula S}
  (h1 : φ land ψ vdash χ) (h2 : φ land ω vdash χ) :
  φ land (ψ lor ω) vdash χ
:= by
  calc
    φ land (ψ lor ω) vdash lnot lnot χ := by
      apply intro_not
      let Γ1 := (φ land (ψ lor ω)) land lnot χ
      have Γ1_derives_φ : Γ1 vdash φ := by
        calc
          Γ1 vdash φ land (ψ lor ω) := elim_and1
          _ vdash φ := elim_and1
      apply modus_ponens
      . calc
          Γ1 vdash φ land ψ := by
            apply intro_and
            . exact Γ1_derives_φ
            . calc
              Γ1 vdash lnot lnot ψ := by
                apply intro_not
                let Γ2 := Γ1 land lnot ψ
                apply modus_ponens
                . calc
                    Γ2 vdash φ land ω := by
                      apply intro_and
                      . calc
                          Γ2 vdash Γ1 := elim_and1
                          _ vdash φ := Γ1_derives_φ
                      . apply modus_ponens
                        . exact elim_and2
                        . calc
                          Γ2 vdash Γ1 := elim_and1
                          _ vdash φ land (ψ lor ω) := elim_and1
                          _ vdash ψ lor ω := elim_and2
                    _ vdash χ := h2
                . calc
                    Γ2 vdash Γ1 := elim_and1
                    _ vdash lnot χ := elim_and2
              _ vdash ψ := dne
          _ vdash χ := h1
      . exact elim_and2
    _ vdash χ := dne

-- 選言の除去則（簡易版）
theorem elim_or0
  {φ ψ χ : Formula S}
  (h1 : φ vdash ψ) (h2 : χ vdash ψ) :
  φ lor χ vdash ψ
:= by
  calc
    φ lor χ vdash top land (φ lor χ) := land_unit.left
    _ vdash ψ := by
      apply elim_or
      . calc
          top land φ vdash φ land top := land_exchange
          φ land top vdash ψ := weaken h1
      . calc
          top land χ vdash χ land top := land_exchange
          χ land top vdash ψ := weaken h2

-- 選言の冪等律
theorem lor_idempotence
  {φ : Formula S} :
  Equiv φ (φ lor φ)
:= by
  constructor
  . exact intro_or1
  . apply elim_or0
    . exact ax
    . exact ax

-- 選言の結合律
theorem lor_associative1
  {φ ψ χ : Formula S} :
  Equiv ((φ lor ψ) lor χ) (φ lor (ψ lor χ))
:= by
  constructor
  . apply elim_or0
    . apply elim_or0
      . exact intro_or1
      . calc
          ψ vdash ψ lor χ := intro_or1
          _ vdash φ lor (ψ lor χ) := intro_or2
    . calc
        χ vdash ψ lor χ := intro_or2
        _ vdash φ lor (ψ lor χ) := intro_or2
  . apply elim_or0
    . calc
        φ vdash φ lor ψ := intro_or1
        _ vdash (φ lor ψ) lor χ := intro_or1
    . apply elim_or0
      . calc
          ψ vdash φ lor ψ := intro_or2
          _ vdash (φ lor ψ) lor χ := intro_or1
      . exact intro_or2

-- 選言の交換律
theorem lor_exchange
  {φ ψ : Formula S} :
  φ lor ψ vdash ψ lor φ
:= by
  apply elim_or0
  . exact intro_or2
  . exact intro_or1

-- 選言三段論法
theorem disjunctive_syllogism
  {φ ψ : Formula S} :
  lnot φ land (φ lor ψ) vdash ψ
:= by
  apply elim_or
  . calc
    lnot φ land φ vdash φ land lnot φ := land_exchange
    _ vdash bot := elim_not
    _ vdash ψ := explosion
  . exact elim_and2

-- 吸収律１
theorem absorption1
  {φ ψ : Formula S} :
  Equiv (φ lor (φ land ψ)) φ
:= by
  constructor
  . apply elim_or0
    . exact ax
    . exact elim_and1
  . exact intro_or1

-- 吸収律２
theorem absorption2
  {φ ψ : Formula S} :
  Equiv (φ land (φ lor ψ)) φ
:= by
  constructor
  . exact elim_and1
  . apply intro_and
    . exact ax
    . exact intro_or1

-- 分配律１
theorem distributive1
  {φ ψ χ : Formula S} :
  Equiv (φ lor (ψ land χ)) ((φ lor ψ) land (φ lor χ))
:= by
  constructor
  . apply intro_and
    . apply elim_or0
      . exact intro_or1
      . calc
          ψ land χ vdash ψ := elim_and1
          _ vdash φ lor ψ := intro_or2
    . apply elim_or0
      . exact intro_or1
      . calc
          ψ land χ vdash χ := elim_and2
          _ vdash φ lor χ := intro_or2
  . apply elim_or
    . calc
        (φ lor ψ) land φ vdash φ := elim_and2
        _ vdash φ lor (ψ land χ) := intro_or1
    . calc
        (φ lor ψ) land χ vdash χ land (φ lor ψ) := land_exchange
        _ vdash φ lor (ψ land χ) := by
          apply elim_or
          . calc
              χ land φ vdash φ := elim_and2
              _ vdash φ lor (ψ land χ) := intro_or1
          . calc
              χ land ψ vdash ψ land χ := land_exchange
              _ vdash φ lor (ψ land χ) := intro_or2

-- 分配律２
theorem distributive2
  {φ ψ χ : Formula S} :
  Equiv (φ land (ψ lor χ)) ((φ land ψ) lor (φ land χ))
:= by
  constructor
  . apply elim_or
    . exact intro_or1
    . exact intro_or2
  . apply elim_or0
    . apply intro_and
      . exact elim_and1
      . calc
          φ land ψ vdash ψ := elim_and2
          _ vdash ψ lor χ := intro_or1
    . apply intro_and
      . exact elim_and1
      . calc
          φ land χ vdash χ := elim_and2
          _ vdash ψ lor χ := intro_or2

-- De Morganの法則１
theorem de_morgan1
  {φ ψ : Formula S} :
  Equiv ((lnot φ) lor (lnot ψ)) (lnot (φ land ψ))
:= by
  constructor
  . apply intro_not
    let Γ1 := (lnot φ lor lnot ψ) land (φ land ψ)
    calc
      Γ1 vdash (φ land ψ) land (lnot φ lor lnot ψ) := land_exchange
      _ vdash bot := by
        apply elim_or
        . apply modus_ponens
          . calc
              (φ land ψ) land lnot φ vdash φ land ψ := elim_and1
              φ land ψ vdash φ := elim_and1
          . exact elim_and2
        . apply modus_ponens
          . exact cut elim_and1 elim_and2
          . exact elim_and2
  · let Θ := lnot φ lor lnot ψ
    calc
      lnot (φ land ψ) vdash lnot lnot Θ := by
        apply intro_not
        let Γ2 := (lnot (φ land ψ)) land lnot Θ
        apply modus_ponens
        . calc
            (lnot (φ land ψ)) land lnot Θ vdash lnot φ := by
              apply intro_not
              apply modus_ponens
              . calc
                  (Γ2 land φ) vdash lnot ψ := by
                    apply intro_not
                    apply modus_ponens
                    . apply intro_and
                      . calc
                          (Γ2 land φ) land ψ vdash Γ2 land φ := elim_and1
                          Γ2 land φ vdash φ := elim_and2
                      . exact elim_and2
                    . calc
                        (Γ2 land φ) land ψ vdash Γ2 land φ := elim_and1
                        _ vdash (lnot (φ land ψ)) land lnot Θ := elim_and1
                        _ vdash lnot (φ land ψ) := elim_and1
                  _ vdash Θ := intro_or2
              . calc
                  Γ2 land φ vdash (lnot (φ land ψ)) land lnot Θ := elim_and1
                  _ vdash lnot Θ := elim_and2
            _ vdash Θ := intro_or1
        . exact elim_and2
      _ vdash Θ := dne

-- De Morganの法則２
theorem de_morgan2
  {φ ψ : Formula S} :
  Equiv (lnot φ land lnot ψ) (lnot (φ lor ψ))
:= by
  constructor
  · apply intro_not
    apply elim_or
    . apply modus_ponens
      . exact elim_and2
      . calc
          (lnot φ land lnot ψ) land φ vdash lnot φ land lnot ψ := elim_and1
          _ vdash lnot φ := elim_and1
    . apply modus_ponens
      . exact elim_and2
      . calc
          (lnot φ land lnot ψ) land ψ vdash lnot φ land lnot ψ := elim_and1
          _ vdash lnot ψ := elim_and2
  · apply intro_and
    · apply intro_not
      apply modus_ponens
      . calc
          lnot (φ lor ψ) land φ vdash φ := elim_and2
          φ vdash φ lor ψ := intro_or1
      . exact elim_and1
    · apply intro_not
      apply modus_ponens
      . calc
          lnot (φ lor ψ) land ψ vdash ψ := elim_and2
          ψ vdash φ lor ψ := intro_or2
      . exact elim_and1

-- 排中律
theorem excluded_middle
  {φ : Formula S} :
  top vdash φ lor lnot φ
:= by
  let Θ := φ lor lnot φ
  calc
    top vdash lnot lnot Θ := by
      apply intro_imp
      calc
        top land lnot Θ vdash lnot Θ := elim_and2
        _ vdash bot := by
          apply modus_ponens
          . calc
              lnot Θ vdash lnot φ := by
                apply intro_not
                apply modus_ponens
                . calc
                    lnot Θ land φ vdash φ := elim_and2
                    φ vdash Θ := intro_or1
                . exact elim_and1
              _ vdash Θ := intro_or2
          . exact ax
    _ vdash Θ := dne

-- Dummetの法則
theorem dummet
  {φ ψ : Formula S} :
  top vdash (φ imply ψ) lor (ψ imply φ)
:= by
    let Θ := φ imply ψ
    calc
      top vdash Θ lor lnot Θ := excluded_middle
      Θ lor lnot Θ vdash Θ lor (ψ imply φ) := by
        apply elim_or0
        . exact intro_or1
        . calc
            lnot Θ vdash ψ imply φ := by
              calc
                lnot Θ vdash (φ imply ψ) imply φ := by
                  apply intro_imp
                  calc
                    lnot Θ land Θ vdash Θ land lnot Θ := land_exchange
                    _ vdash bot := elim_not
                    _ vdash φ := explosion
                _ vdash φ := peirce
                _ vdash ψ imply φ := lukasiewicz
            _ vdash Θ lor (ψ imply φ) := intro_or2

-- ## 量化

-- 全称の除去則（簡易版）
theorem elim_forall0
  {x : Variable} {φ : Formula S} :
  (lforall x, φ) vdash φ
:= by
  calc
    (lforall x, φ) vdash (Formula.substitute x (Term.var x) φ) := elim_forall
    _ vdash φ := by simpa [Formula.subst_self] using ax

-- 量化と演繹
theorem forall_monotone
  {x : Variable} {φ ψ : Formula S} :
  (φ vdash ψ) -> ((lforall x, φ) vdash (lforall x, ψ))
:= Derive.lforall_mono

-- アルファ同値の導出
theorem alpha_equivalence
  {x y : Variable} {φ : Formula S}
  (y_nin_FVφ : y ∉ Formula.free_vars φ) :
  Equiv (lforall x, φ) (lforall y, Formula.substitute x (Term.var y) φ)
:= by
  let φ_y := Formula.substitute x (Term.var y) φ
  constructor
  . have y_nin_FVxφ : y ∉ Formula.free_vars (lforall x, φ) := by
      simp [Formula.free_vars, y_nin_FVφ]
    have allφ_derives_φy : (lforall x, φ) vdash φ_y := by
      exact elim_forall
    exact intro_forall y_nin_FVxφ allφ_derives_φy
  . by_cases y_eq_x : y = x
    . simpa [y_eq_x, φ_y, Formula.subst_self] using ax
    . have y_nin_FVyφy : x ∉ Formula.free_vars (lforall y, φ_y) := by
        have y_nin_FVφy : x ∉ Formula.free_vars φ_y := by
          have x_neq_y : x ≠ y := by
            simpa [eq_comm] using y_eq_x
          exact Formula.subst_clean x_neq_y
        simp [y_nin_FVφy, Formula.free_vars]
      have allφy_derives_φ : (lforall y, φ_y) vdash φ := by
        calc
          (lforall y, φ_y) vdash (Formula.substitute y (Term.var x) φ_y) := by
            simpa [Formula.substitute] using elim_forall
          _ vdash φ := (Formula.subst_cancel y_nin_FVφ).1
      exact intro_forall y_nin_FVyφy allφy_derives_φ

-- 存在の導入則
theorem intro_exists
  {x : Variable} {t : Term S} {φ : Formula S} :
  (Formula.substitute x t φ) vdash (lexists x, φ)
:= by
  apply intro_not
  apply modus_ponens
  . exact elim_and1
  . calc
      (Formula.substitute x t φ) land (lforall x, lnot φ) vdash (lforall x, lnot φ) := elim_and2
      _ vdash (Formula.substitute x t (lnot φ)) := elim_forall
      _ vdash lnot (Formula.substitute x t φ) := by
        simpa [Formula.lnot, Formula.substitute] using ax

-- 存在の導入則（簡易版）
theorem intro_exists0
  {x : Variable} {φ : Formula S} :
  φ vdash (lexists x, φ)
:= by
  calc
    φ vdash (Formula.substitute x (Term.var x) φ) := by simpa [Formula.subst_self] using ax
    _ vdash (lexists x, φ) := intro_exists

-- 存在の除去則
theorem elim_exists
  {x : Variable} {φ ψ χ : Formula S}
  (x_nin_FVφ_cup_FVχ : x ∉ Formula.free_vars φ ∪ Formula.free_vars χ) (h : φ land ψ vdash χ) :
  (φ land (lexists x, ψ) vdash χ)
:= by
  let Γ := (φ land (lexists x, ψ)) land (lnot χ)

  apply proof_contradiction
  apply modus_ponens
  . have x_nin_FVΓ : x ∉ Formula.free_vars Γ := by
      simp [not_or] at x_nin_FVφ_cup_FVχ
      simp [Γ, Formula.free_vars, Formula.lexists, Formula.lnot, x_nin_FVφ_cup_FVχ]
    apply intro_forall x_nin_FVΓ
    apply intro_not
    apply modus_ponens
    . calc
        (Γ land ψ) vdash (φ land ψ) := by
          apply intro_and
          . calc
            Γ land ψ vdash Γ := elim_and1
            _ vdash φ land (lexists x, ψ) := elim_and1
            _ vdash φ := elim_and1
          . exact elim_and2
        _ vdash χ := h
    . calc
      Γ land ψ vdash Γ := elim_and1
      _ vdash lnot χ := elim_and2
  . calc
      Γ vdash (φ land (lexists x, ψ)) := elim_and1
      _ vdash lexists x, ψ := elim_and2

-- 存在の除去則（簡易版）
theorem elim_exists0
  {x : Variable} {φ ψ : Formula S}
  (x_nin_FVψ : x ∉ Formula.free_vars ψ) (h : φ vdash ψ) :
  (lexists x, φ) vdash ψ
:= by
  calc
    (lexists x, φ) vdash top land (lexists x, φ) := land_unit.left
    _ vdash ψ := by
      have x_nin_FVtop_cup_FVψ : x ∉ Formula.free_vars (S:=S) top ∪ Formula.free_vars ψ := by
        simpa [Formula.free_vars, Formula.top] using x_nin_FVψ
      apply elim_exists x_nin_FVtop_cup_FVψ
      calc
        top land φ vdash φ := elim_and2
        _ vdash ψ := h

-- 全称量化子の交換
theorem forall_exchange
  {x y : Variable} {φ : Formula S} :
  (lforall x, (lforall y, φ)) vdash (lforall y, (lforall x, φ))
:= by
  let Γ := lforall x, (lforall y, φ)
  have y_nin_FVΓ : y ∉ Formula.free_vars Γ := by
    simp [Γ, Formula.free_vars]
  apply intro_forall y_nin_FVΓ
  have x_nin_FVΓ : x ∉ Formula.free_vars Γ := by
    simp [Γ, Formula.free_vars]
  apply intro_forall x_nin_FVΓ
  calc
    Γ vdash (lforall y, φ) := elim_forall0
    _ vdash φ := elim_forall0

-- 存在量化子の交換
theorem exists_exchange
  {x y : Variable} {φ : Formula S} :
  (lexists x, (lexists y, φ)) vdash (lexists y, (lexists x, φ))
:= by
  let Θ := lexists y, (lexists x, φ)
  have x_nin_FVΘ : x ∉ Formula.free_vars Θ := by
      simp [Θ, Formula.free_vars, Formula.lexists, Formula.lnot]
  apply elim_exists0 x_nin_FVΘ
  have y_nin_FVΘ : y ∉ Formula.free_vars Θ := by
    simp [Θ, Formula.free_vars, Formula.lexists, Formula.lnot]
  apply elim_exists0 y_nin_FVΘ
  calc
    φ vdash (lexists x, φ) := intro_exists0
    _ vdash Θ := intro_exists0

-- 量化子と否定１
theorem forall_exists_lnot1
  {x : Variable} {φ : Formula S} :
  Equiv (lforall x, lnot φ) (lnot (lexists x, φ))
:= by
  constructor
  . exact intro_dn
  . exact proof_contraposition.1 intro_dn

-- 量化子と否定２
theorem forall_exists_lnot2
  {x : Variable} {φ : Formula S} :
  Equiv (lnot (lforall x, φ)) (lexists x, lnot φ)
:= by
  constructor
  . exact proof_contraposition.2 (forall_monotone dne)
  . exact proof_contraposition.2 (forall_monotone intro_dn)

-- 全称量化子と連言
theorem forall_distribution_over_land
  {x : Variable} {φ ψ : Formula S} :
  Equiv ((lforall x, φ) land (lforall x, ψ)) (lforall x, φ land ψ)
:= by
  constructor
  . let Γ1 := (lforall x, φ) land (lforall x, ψ)
    have x_nin_FVΓ1 : x ∉ Formula.free_vars Γ1 := by
      simp [Γ1, Formula.free_vars]
    apply intro_forall x_nin_FVΓ1
    apply intro_and
    . calc
        Γ1 vdash (lforall x, φ) := elim_and1
        _ vdash φ := elim_forall0
    . calc
        Γ1 vdash (lforall x, ψ) := elim_and2
        _ vdash ψ := elim_forall0
  . let Γ2 := lforall x, φ land ψ
    have x_nin_FVΓ2 : x ∉ Formula.free_vars Γ2 := by
      simp [Γ2, Formula.free_vars]
    apply intro_and
    . apply intro_forall x_nin_FVΓ2
      calc
        Γ2 vdash φ land ψ := elim_forall0
        _ vdash φ := elim_and1
    . apply intro_forall x_nin_FVΓ2
      calc
        Γ2 vdash φ land ψ := elim_forall0
        _ vdash ψ := elim_and2

-- 存在量化子と選言
theorem exists_distribution_over_lor
  {x : Variable} {φ ψ : Formula S} :
  Equiv ((lexists x, φ) lor (lexists x, ψ)) (lexists x, φ lor ψ)
:= by
  let Γ1 := (lexists x, φ) lor (lexists x, ψ)
  let Γ2 := lexists x, φ lor ψ
  constructor
  · have x_nin_FVΓ2 : x ∉ Formula.free_vars Γ2 := by
      simp [Γ2, Formula.free_vars, Formula.lexists, Formula.lnot]
    apply elim_or0
    . apply elim_exists0 x_nin_FVΓ2
      calc
        φ vdash φ lor ψ := intro_or1
        _ vdash Γ2 := intro_exists0
    . apply elim_exists0 x_nin_FVΓ2
      calc
        ψ vdash φ lor ψ := intro_or2
        _ vdash Γ2 := intro_exists0
  · have x_nin_FVΓ1 : x ∉ Formula.free_vars Γ1 := by
      simp [Γ1, Formula.free_vars, Formula.lor, Formula.lexists, Formula.lnot]
    apply elim_exists0 x_nin_FVΓ1
    apply elim_or0
    · calc
        φ vdash (lexists x, φ) := intro_exists0
        _ vdash Γ1 := intro_or1
    · calc
        ψ vdash (lexists x, ψ) := intro_exists0
        _ vdash Γ1 := intro_or2

-- 全称量化子と選言
theorem forall_distribution_over_lor
  {x : Variable} {φ ψ : Formula S} :
  ((lforall x, φ) lor (lforall x, ψ)) vdash (lforall x, φ lor ψ)
:= by
  apply elim_or0
  · have x_nin_FVxφ : x ∉ Formula.free_vars (lforall x, φ) := by
      simp [Formula.free_vars]
    apply intro_forall x_nin_FVxφ
    calc
      (lforall x, φ) vdash φ := elim_forall0
      _ vdash φ lor ψ := intro_or1
  · have x_nin_FVxψ : x ∉ Formula.free_vars (lforall x, ψ) := by
      simp [Formula.free_vars]
    apply intro_forall x_nin_FVxψ
    calc
      (lforall x, ψ) vdash ψ := elim_forall0
      _ vdash φ lor ψ := intro_or2

-- 存在量化子と連言
theorem exists_distribution_over_land
  {x : Variable} {φ ψ : Formula S} :
  (lexists x, (φ land ψ)) vdash (lexists x, φ) land (lexists x, ψ)
:= by
  let Θ := (lexists x, φ) land (lexists x, ψ)
  have x_nin_FVΘ : x ∉ Formula.free_vars Θ := by
    simp [Θ, Formula.free_vars, Formula.lexists, Formula.lnot]
  apply elim_exists0 x_nin_FVΘ
  apply intro_and
  · calc
      φ land ψ vdash φ := elim_and1
      _ vdash lexists x, φ := intro_exists0
  · calc
      φ land ψ vdash ψ := elim_and2
      _ vdash lexists x, ψ := intro_exists0

-- 酒場の法則
theorem drinking_principle
  {x y : Variable} {φ : Formula S}
  (y_nin_FVφ : y ∉ Formula.free_vars φ) :
  top vdash lexists x, (φ imply (lforall y, (Formula.substitute x (Term.var y) φ)))
:= by
  let φ_y := Formula.substitute x (Term.var y) φ
  let Γ := lforall y, φ_y
  let Γ_y := Formula.substitute x (Term.var y) Γ
  apply intro_not
  apply modus_ponens
  . exact elim_and2
  . let Θ := lforall x, (lnot (φ imply Γ))
    calc
      top land Θ vdash Θ := elim_and2
      _ vdash Γ := by
        have y_nin_FVΘ : y ∉ Formula.free_vars Θ := by
          simp [Θ, Γ, Formula.free_vars, Formula.lnot, y_nin_FVφ]
        apply intro_forall y_nin_FVΘ
        calc
          Θ vdash (Formula.substitute x (Term.var y) (lnot (φ imply Γ))) := elim_forall
          _ vdash lnot (φ_y imply Γ_y) := by
            simpa [Formula.substitute, Formula.lnot] using ax
          _ vdash φ_y := not_imply_elim
      Γ vdash (φ imply Γ) := lukasiewicz
      _ vdash lnot Θ := intro_exists0

-- ## 推論規則の追加

abbrev ExtraRule (S : Signature) := Formula S -> Formula S -> Prop

inductive DeriveWith (R : ExtraRule S) : Formula S -> Formula S -> Prop
| core { φ ψ : Formula S } :
  Derive φ ψ -> DeriveWith R φ ψ
| extra { φ ψ : Formula S } :
  R φ ψ -> DeriveWith R φ ψ
| cut { φ ψ χ : Formula S } :
  DeriveWith R φ ψ -> DeriveWith R ψ χ -> DeriveWith R φ χ
| intro_and { φ ψ χ : Formula S } :
  DeriveWith R φ ψ -> DeriveWith R φ χ -> DeriveWith R φ (Formula.land ψ χ)
| intro_imp { φ ψ χ : Formula S } :
  DeriveWith R (Formula.land φ ψ) χ -> DeriveWith R φ (Formula.imply ψ χ)
| intro_forall { φ ψ : Formula S } { x : Variable } :
  x ∉ Formula.free_vars φ -> DeriveWith R φ ψ -> DeriveWith R φ (Formula.lforall x ψ)

-- namespace DeriveWith

--   open Formula

--   theorem ax : DeriveWith R φ φ := .core Derive.ax

--   theorem elim_and1 : DeriveWith R (Formula.land φ ψ) φ := .core Derive.elim_and1

--   theorem elim_and2 : DeriveWith R (Formula.land φ ψ) ψ := .core Derive.elim_and2

--   theorem elim_imp : DeriveWith R (Formula.land φ (Formula.imply φ ψ)) ψ := .core Derive.elim_imp

--   theorem intro_top : DeriveWith R φ top := .core FirstOrderLogic.intro_top

--   theorem land_exchange : DeriveWith R (Formula.land φ ψ) (Formula.land ψ φ) :=
--     .core FirstOrderLogic.land_exchange

--   theorem modus_ponens :
--     DeriveWith R φ ψ
--     -> DeriveWith R φ (Formula.imply ψ χ)
--     -> DeriveWith R φ χ
--   := by
--     intro hψ himp
--     exact .cut (.intro_and hψ himp) DeriveWith.elim_imp

--   theorem contraposition :
--     DeriveWith R ψ φ
--     -> DeriveWith R (Formula.lnot φ) (Formula.lnot ψ)
--   := by
--     intro h
--     apply DeriveWith.intro_imp
--     apply DeriveWith.cut
--       (DeriveWith.intro_and
--         (DeriveWith.cut DeriveWith.elim_and2 h)
--         DeriveWith.elim_and1)
--     exact DeriveWith.elim_imp

-- end DeriveWith

-- -- ## 等号

-- namespace WithEqual

--   inductive pred (P : Type) : Type
--   | equal : pred P
--   | other : P → pred P

--   def arity {P : Type} (arity_ : P → Nat) : pred P → Nat
--   | .equal => 2
--   | .other p => arity_ p

--   def SignatureWithEqual (S : Signature) : Signature where
--     Func := S.Func
--     FuncArity := S.FuncArity
--     Pred := WithEqual.pred S.Pred
--     PredArity := WithEqual.arity S.PredArity

--   def lift_term : Term S → Term (SignatureWithEqual S)
--   | .var x => .var x
--   | .func f args => .func f (fun i => lift_term (args i))

--   def lift_formula : Formula S → Formula (SignatureWithEqual S)
--   | .bot => .bot
--   | .land φ ψ => .land (lift_formula φ) (lift_formula ψ)
--   | .imply φ ψ => .imply (lift_formula φ) (lift_formula ψ)
--   | .pred p args => .pred (pred.other p) (fun i => lift_term (args i))
--   | .lforall x φ => .lforall x (lift_formula φ)

--   def equal (t s : Term (SignatureWithEqual S)) : Formula (SignatureWithEqual S) :=
--     .pred (pred.equal : pred S.Pred) (fun i => if (i : Nat) = 0 then t else s)

--   open Formula

--   variable {t s u : Term (SignatureWithEqual S)}
--   variable {φ : Formula (SignatureWithEqual S)}

--   inductive EqualityRule (S : Signature) : ExtraRule (SignatureWithEqual S)
--   | refl (t : Term (SignatureWithEqual S)) :
--     EqualityRule S top (equal t t)
--   | subst
--       (x : Variable)
--       (t s : Term (SignatureWithEqual S))
--       (φ : Formula (SignatureWithEqual S)) :
--     EqualityRule S ((substitute x t φ) land (equal t s)) (substitute x s φ)

--   local infix:51 " eqvdash " => DeriveWith (EqualityRule S)

--   theorem eq_reflexive :
--     top eqvdash (equal t t)
--   := .extra (.refl t)

--   theorem eq_subst :
--     (substitute x t φ) land (equal t s) eqvdash (substitute x s φ)
--   := .extra (.subst x t s φ)

--   theorem eq_symmetry :
--     (equal t s) eqvdash (equal s t)
--   := by
--     let x := VarSet.fresh (Term.vars t)
--     have x_nfree_t : x ∉ Term.vars t := by
--       show x ∈ Term.vars t -> False
--       intro x_free_t
--       exact (VarSet.fresh_not_mem x_free_t) (by simp [x])
--     have subst_equal (u : Term (SignatureWithEqual S)) :
--       (substitute x u (equal (Term.var x) t)) = (equal u t)
--     := by
--       have same_t : (Term.substitute x u t) = t := by
--         exact Term.subst_same x_nfree_t
--       unfold equal
--       simp [substitute]
--       funext i
--       cases i using Fin.cases with
--       | zero =>
--         simp [Term.substitute]
--       | succ j =>
--         simp [same_t]
--     calc
--       (equal t s) eqvdash (substitute x t (equal (Term.var x) t)) land (equal t s) := by
--         apply DeriveWith.intro_and
--         . calc
--             (equal t s) eqvdash top := DeriveWith.intro_top
--             _ eqvdash (equal t t) := eq_reflexive
--             _ eqvdash (substitute x t (equal (Term.var x) t)) := by
--               simpa [subst_equal] using (DeriveWith.ax :
--                 DeriveWith (EqualityRule S) (equal t t) (equal t t))
--         . exact DeriveWith.ax
--       _ eqvdash (substitute x s (equal (Term.var x) t)) := eq_subst
--       _ eqvdash (equal s t) := by
--         simpa [subst_equal] using (DeriveWith.ax :
--           DeriveWith (EqualityRule S) (equal s t) (equal s t))

--   theorem eq_transitive :
--     (equal t s) land (equal s u) eqvdash (equal t u)
--   := by
--     let x := VarSet.fresh (Term.vars t)
--     have x_nfree_t : x ∉ Term.vars t := by
--       show x ∈ Term.vars t -> False
--       intro x_free_t
--       exact (VarSet.fresh_not_mem x_free_t) (by simp [x])
--     have subst_equal (v : Term (SignatureWithEqual S)) :
--       (substitute x v (equal t (Term.var x))) = (equal t v)
--     := by
--       have same_t : (Term.substitute x v t) = t := by
--         exact Term.subst_same x_nfree_t
--       unfold equal
--       simp [substitute]
--       funext i
--       cases i using Fin.cases with
--       | zero =>
--         simp [same_t]
--       | succ j =>
--         simp [Term.substitute]
--     calc
--       (equal t s) land (equal s u) eqvdash (substitute x s (equal t (Term.var x))) land (equal s u) := by
--         apply DeriveWith.intro_and
--         . simpa [subst_equal] using (DeriveWith.elim_and1 :
--             DeriveWith (EqualityRule S) ((equal t s) land (equal s u)) (equal t s))
--         . exact DeriveWith.elim_and2
--       _ eqvdash (substitute x u (equal t (Term.var x))) := eq_subst
--       _ eqvdash (equal t u) := by
--         simpa [subst_equal] using (DeriveWith.ax :
--           DeriveWith (EqualityRule S) (equal t u) (equal t u))

--   theorem neq_symmetry :
--     lnot (equal t s) eqvdash lnot (equal s t)
--   := DeriveWith.contraposition eq_symmetry

-- end WithEqual

-- end FirstOrderLogic
