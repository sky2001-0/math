import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

-- # 一階述語論理

namespace FirstOrderLogic

-- ## 命題の定式化

-- 非論理記号の型
structure Signature where
  Func      : Type
  FuncArity : Func -> Nat
  Pred      : Type
  PredArity : Pred -> Nat

variable {S : Signature}

-- 変数の型
abbrev Variable := Nat

variable {x y z w : Variable}

-- 変数の集まりの型
abbrev VarSet := Finset Variable

namespace VarSet

  --与えられた変数の集まりに入っていない、新しい変数を用意する。
  def fresh (s : VarSet) : Variable :=
    s.sup (fun n : Variable => n) + 1

  lemma fresh_gt_mem {s : VarSet} :
    x ∈ s -> x < fresh s
  := by
    intro x_mem
    let func_id := fun n : Variable => n
    have hx_le : x ≤ s.sup func_id := by
      simpa using (Finset.le_sup (f:=func_id) x_mem)
    exact lt_of_le_of_lt hx_le (Nat.lt_succ_self _)

  lemma fresh_not_mem {s : VarSet} :
    x ∈ s -> x ≠ fresh s
  := by
    intro x_in_s
    exact ne_of_lt (fresh_gt_mem x_in_s)

  abbrev replace {n : Nat} (f : Fin n → VarSet) : VarSet :=
    (Finset.univ : Finset (Fin n)).biUnion f

  lemma mem_replace {n : Nat} {f : Fin n → VarSet} {v : Variable} :
    v ∈ replace f ↔ ∃ i, v ∈ f i
  := by simp [replace]

end VarSet

-- 項の型
inductive Term (S : Signature) : Type
| var  : Variable -> Term S
| func : (f : S.Func) -> (Fin (S.FuncArity f) -> Term S) -> Term S

variable {t s : Term S}

namespace Term

  -- 項から使用変数の集まりを返す
  def vars : Term S -> VarSet
  | .var x => {x}
  | .func _ args => VarSet.replace (fun i => vars (args i))

  -- 項内の変数への項の代入
  def substitute (x : Variable) (t : Term S) : Term S → Term S
  | .var y => if y = x then t else Term.var y
  | .func f args => .func f (fun i => substitute x t (args i))

  lemma subst_self (x : Variable) (t : Term S) :
    substitute x (Term.var x) t = t
  := by
    induction t with
    | var y => by_cases y_eq_x: y = x <;> simp [substitute, y_eq_x]
    | func f args ih => simp [substitute, ih]

  lemma subst_clean :
    x ≠ y
    -> x ∉ vars (substitute x (Term.var y) t)
  := by
    intro x_neq_y
    induction t with
    | var z =>
      by_cases z_eq_x : z = x
      · simp [substitute, vars, z_eq_x, x_neq_y]
      · have x_neq_z : x ≠ z := by
          simpa [eq_comm] using z_eq_x
        simpa [substitute, vars, z_eq_x] using x_neq_z
    | func f args ih =>
      simpa [vars, substitute, VarSet.mem_replace] using ih

  lemma subst_new :
    x ∈ vars t
    -> y ∈ vars (substitute x (Term.var y) t)
  := by
    intro h0
    induction t with
    | var z =>
      have x_eq_z : x = z := by
        simpa [vars] using h0
      simp [vars, substitute, x_eq_z]
    | func f args ih =>
      obtain ⟨i, h0_i⟩ := (VarSet.mem_replace).1 h0
      exact (VarSet.mem_replace).2 ⟨i, ih i h0_i⟩

  lemma subst_preserve :
    x ∈ vars t
    -> x ≠ y
    -> x ∈ vars (substitute y (Term.var z) t) := by
      intro h0 x_neq_y
      induction t with
      | var w =>
        have x_eq_w : x = w := by
          simpa [vars] using h0
        have w_neq_y : w ≠ y := by
          show w = y -> False
          intro w_eq_y
          exact x_neq_y (x_eq_w.trans w_eq_y)
        simp [substitute, vars, x_eq_w, w_neq_y]
      | func f args ih =>
        have h0_iz : ∃ i, x ∈ vars (substitute y (Term.var z) (args i)) := by
          have h0' : ∃ i, x ∈ vars (args i) := by
            simpa [vars, VarSet.mem_replace] using h0
          obtain ⟨i, h0_i⟩ := h0'
          exact ⟨i, ih i h0_i⟩
        simpa [substitute, vars, VarSet.mem_replace] using h0_iz

  lemma subst_same :
    x ∉ vars t
    -> substitute x s t = t
  := by
    intro h0
    induction t with
    | var y =>
      have y_neq_x : y ≠ x := by
        show y = x -> False
        intro y_eq_x
        exact h0 (by simp [vars, y_eq_x])
      simp [substitute, y_neq_x]
    | func f args ih =>
      have subst_same :
        ∀ i, substitute x s (args i) = args i
      := by
        intro i
        have h0_i : x ∉ vars (args i) := by
          show x ∈ vars (args i) -> False
          intro h_mem_i
          have h_mem : x ∈ vars (.func f args) := by
            simpa [vars] using ((VarSet.mem_replace).2 ⟨i, h_mem_i⟩)
          exact h0 h_mem
        exact ih i h0_i
      simp [substitute, subst_same]

  lemma subst_double :
    y ∉ vars t
    -> substitute y (Term.var x) (substitute x (Term.var y) t) = t
  := by
    intro h0
    induction t with
    | var z =>
      by_cases z_eq_x : z = x
      · simp [substitute, z_eq_x]
      · have z_neq_y : z ≠ y := by
          simpa [eq_comm, Term.vars] using h0
        simp [substitute, z_eq_x, z_neq_y]
    | func f args ih =>
      have subst_double_args :
        ∀ i, substitute y (Term.var x) (substitute x (Term.var y) (args i)) = args i
      := by
        intro i
        have h0_i : y ∉ vars (args i) := by
          show y ∈ vars (args i) -> False
          intro h_mem_i
          have h_mem : y ∈ vars (.func f args) := by
            simpa [vars] using ((VarSet.mem_replace).2 ⟨i, h_mem_i⟩)
          exact h0 h_mem
        exact ih i h0_i
      simp [substitute, subst_double_args]

end Term

-- 命題
inductive Formula (S : Signature) : Type
| bot     : Formula S
| land    : Formula S -> Formula S -> Formula S
| imply   : Formula S -> Formula S -> Formula S
| pred    : (p : S.Pred) -> (Fin (S.PredArity p) -> Term S) -> Formula S
| lforall : Variable -> Formula S -> Formula S

variable {φ ψ χ ω : Formula S}

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

  -- 命題内の変数への変数の代入
  def rename (x y : Variable) : Formula S → Formula S
  | .bot => .bot
  | .land φ ψ => .land (rename x y φ) (rename x y ψ)
  | .imply φ ψ => .imply (rename x y φ) (rename x y ψ)
  | .pred p args => .pred p (fun i => Term.substitute x (Term.var y) (args i))
  | .lforall z φ => if z = x then .lforall z φ else .lforall z (rename x y φ)

  lemma size_rename :
    size (rename x y φ) = size φ
  := by
    induction φ with
    | bot => simp [rename, size]
    | land φ ψ ihφ ihψ => simp [rename, size, ihφ, ihψ]
    | imply φ ψ ihφ ihψ => simp [rename, size, ihφ, ihψ]
    | pred p args => simp [rename, size]
    | lforall z φ ih => by_cases z_eq_x : z = x <;> simp [rename, size, z_eq_x, ih]

  lemma rename_preserve :
    x ∈ free_vars φ
    -> x ≠ y
    -> x ∈ free_vars (rename y z φ)
  := by
    intro h0 x_neq_y
    induction φ with
    | bot => simp [free_vars] at h0
    | land φ ψ ihφ ihψ =>
      have h0' : x ∈ free_vars φ ∨ x ∈ free_vars ψ := by
        simpa [free_vars] using h0
      cases h0' with
      | inl h0_φ =>
          have h0_φz : x ∈ free_vars (rename y z φ) := by
            exact ihφ h0_φ
          simp [rename, free_vars, h0_φz]
      | inr h0_ψ =>
          have h0_ψz : x ∈ free_vars (rename y z ψ) := by
            exact ihψ h0_ψ
          simp [rename, free_vars, h0_ψz]
    | imply φ ψ ihφ ihψ =>
      have h0' : x ∈ free_vars φ ∨ x ∈ free_vars ψ := by
        simpa [free_vars] using h0
      cases h0' with
      | inl h0_φ =>
          have h0_φz : x ∈ free_vars (rename y z φ) := by
            exact ihφ h0_φ
          simp [rename, free_vars, h0_φz]
      | inr h0_ψ =>
          have h0_ψz : x ∈ free_vars (rename y z ψ) := by
            exact ihψ h0_ψ
          simp [rename, free_vars, h0_ψz]
    | pred p args =>
      have h0' : ∃ i, x ∈ (args i).vars := by
        simpa [free_vars, VarSet.mem_replace] using h0
      obtain ⟨i, h0_i⟩ := h0'
      have h0_iz : ∃ i, x ∈ (Term.substitute y (Term.var z) (args i)).vars := by
        exact ⟨i, Term.subst_preserve h0_i x_neq_y⟩
      simpa [rename, free_vars, VarSet.mem_replace] using h0_iz
    | lforall w φ ih =>
      by_cases w_eq_y : w = y
      · simpa [rename, free_vars, w_eq_y] using h0
      · have h0' : x ∈ free_vars φ ∧ x ≠ w := by
          simpa [free_vars] using h0
        have h0_φz : x ∈ free_vars (rename y z φ) := by
          exact ih h0'.1
        simp [rename, free_vars, w_eq_y, h0_φz, h0'.2]

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
      simp [size, size_rename] <;> omega

  lemma subst_self :
    substitute x (Term.var x) φ = φ
  := by
    induction φ with
    | bot => simp [substitute]
    | land φ ψ ihφ ihψ => simp [substitute, ihφ, ihψ]
    | imply φ ψ ihφ ihψ => simp [substitute, ihφ, ihψ]
    | pred p args => simp [substitute, Term.subst_self]
    | lforall y φ ih => by_cases y_eq_x : y = x <;> simp [substitute, y_eq_x, Term.vars, ih]

  lemma subst_clean:
    x ≠ y ->
    x ∉ free_vars (substitute x (Term.var y) φ)
  := by
    intro x_neq_y

    have hmain :
      ∀n : Nat, ∀φ : Formula S,
      size φ = n ->
      x ≠ y ->
      x ∉ free_vars (substitute x (Term.var y) φ)
    := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro φ hsize x_neq_y
        cases φ with
        | bot => simp [substitute, free_vars]
        | land φ ψ =>
          have hsize': size φ + size ψ + 1 = n := by
            simpa [size] using hsize
          have ihφ : x ∉ free_vars (substitute x (Term.var y) φ) := by
            exact ih (size φ) (by omega) φ rfl x_neq_y
          have ihψ : x ∉ free_vars (substitute x (Term.var y) ψ) := by
            exact ih (size ψ) (by omega) ψ rfl x_neq_y
          simp [substitute, free_vars, ihφ, ihψ]
        | imply φ ψ =>
          have hsize' : size φ + size ψ + 1 = n := by
            simpa [size] using hsize
          have ihφ : x ∉ free_vars (substitute x (Term.var y) φ) := by
            exact ih (size φ) (by omega) φ rfl x_neq_y
          have ihψ : x ∉ free_vars (substitute x (Term.var y) ψ) := by
            exact ih (size ψ) (by omega) ψ rfl x_neq_y
          simp [substitute, free_vars, ihφ, ihψ]
        | pred p args =>
          simp [substitute, free_vars, Term.subst_clean, x_neq_y]
        | lforall z φ =>
          have hsize' : size φ + 1 = n := by
            simpa [size] using hsize
          by_cases x_eq_z : x = z
          · simp [substitute, free_vars, x_eq_z]
          · by_cases x_free : x ∈ free_vars φ
            let t := Term.var (S:=S) y
            · by_cases z_free : z ∈ Term.vars t
              · have z_eq_y : z = y := by
                  simpa [Term.vars, t] using z_free
                let w := VarSet.fresh (Term.vars t ∪ all_vars φ ∪ {x})
                have x_neq_w : x ≠ w := by
                  exact VarSet.fresh_not_mem (by simp)
                let φ_r := rename y w φ
                have ihφ_r : x ∉ free_vars (substitute x t φ_r) := by
                  have small_size_rename : size φ_r < n := by
                    calc
                      size (rename y w φ) = size φ := size_rename
                      _ < n := by omega
                  exact ih (size φ_r) small_size_rename φ_r
                    (by simp [size_rename, φ_r])
                    x_neq_y
                have ih :
                  x ∉ free_vars (lforall w (substitute x t φ_r)) := by
                  simp [free_vars, x_neq_w, ihφ_r]
                simpa [substitute, free_vars, Term.vars, x_neq_y, x_free, w, t, φ_r, z_eq_y] using ih
              · have z_neq_y : z ≠ y := by
                  simpa [Term.vars, t] using z_free
                have ihφ : x ∉ free_vars (substitute x t φ) := by
                  exact ih (size φ) (by omega) φ rfl x_neq_y
                simpa [substitute, free_vars, x_eq_z, x_free, z_free, z_neq_y, t] using ihφ
            · simp [substitute, free_vars, x_eq_z, x_free]

    exact hmain (size φ) φ rfl x_neq_y

  lemma subst_new :
    x ∈ free_vars φ ->
    y ∈ free_vars (substitute x (Term.var y) φ)
  := by
    intro h0
    have hmain :
      ∀ n : Nat, ∀ φ : Formula S,
        size φ = n ->
        x ∈ free_vars φ ->
        y ∈ free_vars (substitute x (Term.var y) φ)
    := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro φ hsize h0
        cases φ with
        | bot => simp [free_vars] at h0
        | land φ ψ =>
          have hsize': size φ + size ψ + 1 = n := by
            simpa [size] using hsize
          have h0' : x ∈ free_vars φ ∨ x ∈ free_vars ψ := by
            simpa [free_vars] using h0
          cases h0' with
          | inl h0_φ =>
            have ihφ : y ∈ free_vars (substitute x (Term.var y) φ) := by
              exact ih (size φ) (by omega) φ rfl h0_φ
            simp [substitute, free_vars, ihφ]
          | inr h0_ψ =>
            have ihψ : y ∈ free_vars (substitute x (Term.var y) ψ) := by
              exact ih (size ψ) (by omega) ψ rfl h0_ψ
            simp [substitute, free_vars, ihψ]
        | imply φ ψ =>
          have hsize': size φ + size ψ + 1 = n := by
            simpa [size] using hsize
          have h0' : x ∈ free_vars φ ∨ x ∈ free_vars ψ := by
            simpa [free_vars] using h0
          cases h0' with
          | inl h0_φ =>
            have ihφ : y ∈ free_vars (substitute x (Term.var y) φ) := by
              exact ih (size φ) (by omega) φ rfl h0_φ
            simp [substitute, free_vars, ihφ]
          | inr h0_ψ =>
            have ihψ : y ∈ free_vars (substitute x (Term.var y) ψ) := by
              exact ih (size ψ) (by omega) ψ rfl h0_ψ
            simp [substitute, free_vars, ihψ]
        | pred p args =>
          obtain ⟨i, h0_i⟩ := (VarSet.mem_replace).1 h0
          have h0_iy : ∃ i, y ∈ Term.vars (Term.substitute x (Term.var y) (args i)) := by
            exact ⟨i, Term.subst_new h0_i⟩
          simpa [substitute, free_vars, VarSet.mem_replace] using h0_iy
        | lforall z φ =>
          have hsize': size φ + 1 = n := by
            simpa [size] using hsize
          have x_neq_z : x ≠ z := by
            show x = z -> False
            intro x_eq_z
            have h0_false : x ∉ free_vars (lforall z φ) := by
              simp [free_vars, x_eq_z]
            exact h0_false h0
          have h0_φ : x ∈ free_vars φ := by
            simpa [free_vars, x_neq_z] using h0
          let t := Term.var (S:=S) y
          by_cases z_free : z ∈ Term.vars t
          · have z_eq_y : z = y := by
              simpa [Term.vars, t] using z_free
            let w := VarSet.fresh (Term.vars t ∪ all_vars φ ∪ {x})
            let φ_r := rename z w φ
            have h0φ_r : x ∈ free_vars φ_r := by
              exact rename_preserve h0_φ x_neq_z
            have ihφ_r : y ∈ free_vars (substitute x t φ_r) := by
              have hlt : size φ_r < n := by
                calc
                  size φ_r = size φ := by simp [φ_r, size_rename]
                  _ < n := by omega
              exact ih (size φ_r) hlt φ_r (by simp [φ_r, size_rename]) h0φ_r
            have y_neq_w : y ≠ w := by
              apply VarSet.fresh_not_mem
              simp [Term.vars, t]
            have ih : y ∈ free_vars (lforall w (substitute x t φ_r)) := by
              simp [free_vars, y_neq_w, ihφ_r]
            simpa [substitute, free_vars, x_neq_z, h0_φ, z_free, t, w, φ_r] using ih
          · have y_neq_z : y ≠ z := by
              simpa [Term.vars, t, eq_comm] using z_free
            have ihφ : y ∈ free_vars (substitute x t φ) := by
              exact ih (size φ) (by omega) φ rfl h0_φ
            simpa [substitute, free_vars, x_neq_z, h0_φ, z_free, y_neq_z, t] using ihφ

    exact hmain (size φ) φ rfl h0

end Formula

-- ## 古典論理の推論規則

-- 推論規則
inductive Derive : Formula S -> Formula S -> Prop
| ax {φ} :
  Derive φ φ
| cut {φ ψ χ} :
  Derive φ ψ -> Derive ψ χ -> Derive φ χ
| intro_and {φ ψ χ} :
  Derive φ ψ -> Derive φ χ -> Derive φ (Formula.land ψ χ)
| elim_and1 {φ ψ} :
  Derive (Formula.land φ ψ) φ
| elim_and2 {φ ψ} :
  Derive (Formula.land φ ψ) ψ
| intro_imp {φ ψ χ} :
  Derive (Formula.land φ ψ) χ -> Derive φ (Formula.imply ψ χ)
| elim_imp {φ ψ} :
  Derive (Formula.land φ (Formula.imply φ ψ)) ψ
| dne {φ} :
  Derive (Formula.imply (Formula.imply φ Formula.bot) Formula.bot) φ
| intro_forall {φ ψ} {x : Variable} :
  (x ∉ Formula.free_vars φ) -> Derive φ ψ -> Derive φ (Formula.lforall x ψ)
| elim_forall {φ} {x : Variable} {t : Term S} :
  -- tの自由変数でありφの束縛変数であるものは、置換できれいにする。
  Derive (Formula.lforall x φ) (Formula.substitute x t φ)

-- Derive が推移律を満たすことを、Leanに教える。
instance : Trans (Derive (S := S)) (Derive (S := S)) (Derive (S := S)) where
  trans := Derive.cut (S := S)

-- 双方向推論
def Equiv (φ ψ : Formula S) : Prop := And (Derive φ ψ) (Derive ψ φ)

namespace Formula

  open Derive

  lemma subst_double :
    y ∉ all_vars φ
    -> Equiv (substitute y (Term.var x) (substitute x (Term.var y) φ)) φ
  := by
    intro h0
    have hmain :
      ∀ n : Nat, ∀ φ : Formula S,
      size φ = n ->
      y ∉ all_vars φ ->
      Equiv (substitute y (Term.var x) (substitute x (Term.var y) φ)) φ
    := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro φ hsize h0
        cases φ with
        | bot =>
          constructor <;> simpa [substitute] using ax
        | land φ ψ =>
          have hsize': size φ + size ψ + 1 = n := by
            simpa [size] using hsize
          have h0_split :
            y ∉ Formula.free_vars φ
            ∧ y ∉ Formula.free_vars ψ
            ∧ y ∉ Formula.bound_vars φ
            ∧ y ∉ Formula.bound_vars ψ
          := by
            simpa [all_vars, free_vars, bound_vars, not_or] using h0
          let φ_new := substitute y (Term.var x) (substitute x (Term.var y) φ)
          let ψ_new := substitute y (Term.var x) (substitute x (Term.var y) ψ)
          have ihφ : Equiv φ_new φ := by
            have h0_φ : y ∉ all_vars φ := by
              obtain ⟨h0_φf, _, h0_φb, _⟩ := h0_split
              simp [all_vars, h0_φf, h0_φb]
            simpa [φ_new] using (ih (size φ) (by omega) φ rfl h0_φ)
          have ihψ : Equiv ψ_new ψ := by
            have h0_ψ : y ∉ all_vars ψ := by
              obtain ⟨_, h0_ψf, _, h0_ψb⟩ := h0_split
              simp [all_vars, h0_ψf, h0_ψb]
            simpa [ψ_new] using (ih (size ψ) (by omega) ψ rfl h0_ψ)
          constructor
          . have ih : Derive (land φ_new ψ_new) (land φ ψ) := by
              apply intro_and
              · calc
                  Derive (land φ_new ψ_new) φ_new := elim_and1
                  Derive _ φ := ihφ.1
              · calc
                  Derive (land φ_new ψ_new) ψ_new := elim_and2
                  Derive _ ψ := ihψ.1
            simpa [substitute, φ_new, ψ_new] using ih
          . have ih : Derive (land φ ψ) (land φ_new ψ_new) := by
              apply intro_and
              · calc
                  Derive (land φ ψ) φ := elim_and1
                  Derive _ φ_new := ihφ.2
              · calc
                  Derive (land φ ψ) ψ := elim_and2
                  Derive _ ψ_new := ihψ.2
            simpa [substitute, φ_new, ψ_new] using ih
        | imply φ ψ =>
          have hsize': size φ + size ψ + 1 = n := by
            simpa [size] using hsize
          have h0_split :
            y ∉ Formula.free_vars φ
            ∧ y ∉ Formula.free_vars ψ
            ∧ y ∉ Formula.bound_vars φ
            ∧ y ∉ Formula.bound_vars ψ
          := by
            simpa [all_vars, free_vars, bound_vars, not_or] using h0
          let φ_new := substitute y (Term.var x) (substitute x (Term.var y) φ)
          let ψ_new := substitute y (Term.var x) (substitute x (Term.var y) ψ)
          have ihφ : Equiv φ_new φ := by
            have h0_φ : y ∉ all_vars φ := by
              obtain ⟨h0_φf, _, h0_φb, _⟩ := h0_split
              simp [all_vars, h0_φf, h0_φb]
            simpa [φ_new] using (ih (size φ) (by omega) φ rfl h0_φ)
          have ihψ : Equiv ψ_new ψ := by
            have h0_ψ : y ∉ all_vars ψ := by
              obtain ⟨_, h0_ψf, _, h0_ψb⟩ := h0_split
              simp [all_vars, h0_ψf, h0_ψb]
            simpa [ψ_new] using (ih (size ψ) (by omega) ψ rfl h0_ψ)
          constructor
          . have ih : Derive (imply φ_new ψ_new) (imply φ ψ) := by
              have : Derive (land (imply φ_new ψ_new) φ) ψ := by
                calc
                  Derive (land (imply φ_new ψ_new) φ) (land φ_new (imply φ_new ψ_new)) := by
                    apply intro_and
                    . calc
                        Derive _ φ := elim_and2
                        Derive _ _ := ihφ.2
                    . exact elim_and1
                  Derive _ ψ_new := elim_imp
                  Derive _ ψ := ihψ.1
              exact intro_imp this
            simpa [substitute, φ_new, ψ_new] using ih
          . have ih : Derive (imply φ ψ) (imply φ_new ψ_new) := by
              have : Derive (land (imply φ ψ) φ_new) ψ_new := by
                calc
                  Derive (land (imply φ ψ) φ_new) (land φ (imply φ ψ)) := by
                    apply intro_and
                    . calc
                        Derive _ φ_new := elim_and2
                        Derive _ _ := ihφ.1
                    . exact elim_and1
                  Derive _ ψ := elim_imp
                  Derive _ ψ_new := ihψ.2
              exact intro_imp this
            simpa [substitute, φ_new, ψ_new] using ih
        | pred p args =>
          have hargs : ∀ i, y ∉ Term.vars (args i) := by
            intro i
            show y ∈ Term.vars (args i) -> False
            intro h0_i
            have h0_false : y ∈ all_vars (pred p args) := by
              simp [all_vars, free_vars, bound_vars]
              exact ⟨i, h0_i⟩
            exact h0 h0_false
          constructor <;> simpa [substitute, hargs, Term.subst_double] using ax
        | lforall z φ =>
          have hsize': size φ + 1 = n := by
            simpa [size] using hsize
          have y_neq_z : y ≠ z := by
            show y = z -> False
            intro y_eq_z
            have h0_false : y ∈ all_vars (lforall z φ) := by
              simp [all_vars, bound_vars, y_eq_z]
            exact h0 h0_false
          have y_nfree : y ∉ free_vars φ := by
            show y ∈ free_vars φ -> False
            intro y_free
            have h0_false : y ∈ all_vars (lforall z φ) := by
              simp [all_vars, free_vars, y_free, y_neq_z]
            exact h0 h0_false
          have y_nbound : y ∉ bound_vars φ := by
            show y ∈ bound_vars φ -> False
            intro y_bound
            have h0_false : y ∈ all_vars (lforall z φ) := by
              simp [all_vars, bound_vars, y_bound, y_neq_z]
            exact h0 h0_false
          have h0_φ : y ∉ all_vars φ := by
            simp [all_vars, y_nfree, y_nbound]
          by_cases x_eq_z : x = z
          · have is_same :
              (substitute y (Term.var x) (substitute x (Term.var y) (lforall z φ))) = (lforall z φ)
            := by
              simp [substitute, x_eq_z, y_nfree]
            constructor <;> simpa [is_same] using ax
          · by_cases x_free : x ∈ free_vars φ
            · let φ_new := substitute y (Term.var x) (substitute x (Term.var y) φ)
              have ihφ : Equiv φ_new φ := by
                simpa [φ_new] using (ih (size φ) (by omega) φ rfl h0_φ)
              have z_notin_y : z ∉ Term.vars (Term.var (S:=S) y) := by
                simp [Term.vars, eq_comm, y_neq_z]
              have z_notin_x : z ∉ Term.vars (Term.var (S:=S) x) := by
                simp [Term.vars, eq_comm, x_eq_z]
              have hy_new : y ∈ free_vars (substitute x (Term.var y) φ) := by
                exact Formula.subst_new x_free
              constructor
              . have ih : Derive (lforall z φ_new) (lforall z φ) := by
                  have h0_z : z ∉ free_vars (lforall z φ_new) := by
                    simp [free_vars]
                  have ih_φ : Derive (lforall z φ_new) φ := by
                    calc
                      Derive (lforall z φ_new) (substitute z (Term.var z) φ_new) := elim_forall
                      Derive _ φ_new := by simpa [subst_self] using ax
                      Derive _ φ := ihφ.1
                  exact intro_forall h0_z ih_φ
                simpa [substitute, φ_new, x_eq_z, x_free, y_neq_z, z_notin_y, z_notin_x, hy_new] using ih
              . have ih : Derive (lforall z φ) (lforall z φ_new) := by
                  have h0_z : z ∉ free_vars (lforall z φ) := by
                    simp [free_vars]
                  have ih_φ : Derive (lforall z φ) φ_new := by
                    calc
                      Derive (lforall z φ) (substitute z (Term.var z) φ) := elim_forall
                      Derive _ φ := by simpa [subst_self] using ax
                      Derive _ φ_new := ihφ.2
                  exact intro_forall h0_z ih_φ
                simpa [substitute, φ_new, x_eq_z, x_free, y_neq_z, z_notin_y, z_notin_x, hy_new] using ih
            · constructor <;>
                simpa [substitute, x_eq_z, x_free, y_nfree, y_neq_z] using ax

    exact hmain (size φ) φ rfl h0

end Formula

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
theorem modus_ponens :
  (φ vdash ψ) -> (φ vdash ψ imply χ) -> (φ vdash χ)
:= by
  intro h1 h2
  calc
    φ vdash ψ land (ψ imply χ) := by
      apply intro_and
      . exact h1
      . exact h2
    _ vdash χ := elim_imp

-- 弱化
theorem weaken :
  (φ vdash ψ) -> (φ land χ vdash ψ)
:= by
  intro h
  calc
    φ land χ vdash φ := elim_and1
    _ vdash ψ := h

-- 連言の冪等律
theorem land_idempotence :
  Equiv φ (φ land φ)
:= by
  constructor
  . apply intro_and
    . exact ax
    . exact ax
  . exact elim_and1

-- 連言の結合律
theorem land_associative1 :
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
theorem land_exchange :
  (φ land ψ) vdash (ψ land φ)
:= by
  apply intro_and
  . exact elim_and2
  . exact elim_and1

-- 仮言三段論法
theorem hypothetical_syllogism :
  ((φ imply ψ) land (ψ imply χ)) vdash (φ imply χ)
:= by
  let Γ := ((φ imply ψ) land (ψ imply χ)) land φ
  have Γ_derives_χ : Γ vdash χ := by
    apply modus_ponens
    . apply modus_ponens
      . exact elim_and2
      . calc
        Γ vdash (φ imply ψ) land (ψ imply χ) := elim_and1
        _ vdash φ imply ψ := elim_and1
    . calc
      Γ vdash (φ imply ψ) land (ψ imply χ) := elim_and1
      _ vdash ψ imply χ := elim_and2
  exact intro_imp Γ_derives_χ

-- 逆演繹定理
theorem converse_deduction :
  (φ vdash ψ imply χ) -> (φ land ψ vdash χ)
:= by
  intro h
  apply modus_ponens
  . exact elim_and2
  . calc
    _ vdash φ := elim_and1
    _ vdash ψ imply χ := h

-- Lukasiewiczの第一公理
theorem lukasiewicz :
  φ vdash ψ imply φ
:= by
  have φψ_derives_φ : φ land ψ vdash φ := elim_and1
  exact intro_imp φψ_derives_φ

-- ## 否定

-- 否定の導入則
theorem intro_not :
  ((φ land ψ) vdash bot) -> (φ vdash lnot ψ)
:= by
  intro h
  exact intro_imp h

-- 否定の除去則
theorem elim_not :
  φ land lnot φ vdash bot
:= elim_imp

-- 二重否定導入
theorem intro_dn:
  φ vdash lnot lnot φ
:= by
  have h: φ land lnot φ vdash bot := elim_not
  exact intro_imp h

-- 爆発律
theorem explosion :
  bot vdash φ
:= by
  have bot_notφ_derives_bot : bot land lnot φ vdash bot := elim_and1
  calc
    bot vdash lnot lnot φ := intro_imp bot_notφ_derives_bot
    _ vdash _ := dne

-- 否定含意からの前件の取り出し
theorem not_imply_elim :
  lnot (φ imply ψ) vdash φ
:= by
  let Γ := (lnot (φ imply ψ)) land (lnot φ)
  have Γ_derives_bot : Γ vdash bot := by
    apply modus_ponens
    . have Γφ_derives_ψ : Γ land φ vdash ψ := by
        calc
          Γ land φ vdash bot := by
            apply modus_ponens
            . exact elim_and2
            . calc
              Γ land φ vdash Γ := elim_and1
              _ vdash lnot φ := elim_and2
          _ vdash ψ := explosion
      exact intro_imp Γφ_derives_ψ
    . exact elim_and1
  calc
    lnot (φ imply ψ) vdash lnot lnot φ := intro_not Γ_derives_bot
    _ vdash φ := dne

-- Pierce則
theorem peirce :
  (φ imply ψ) imply φ vdash φ
:= by
  calc
    (φ imply ψ) imply φ vdash lnot lnot φ := by
      let Γ := ((φ imply ψ) imply φ) land lnot φ
      have Γ_derives_bot : Γ vdash bot := by
        apply modus_ponens
        . apply modus_ponens
          . calc
              Γ vdash lnot φ := elim_and2
              _ vdash φ imply ψ := by
                have notφ_φ_derives_ψ : (lnot φ land φ) vdash ψ := by
                  calc
                    lnot φ land φ vdash φ land lnot φ := land_exchange
                    _ vdash bot := elim_not
                    _ vdash ψ := explosion
                exact intro_imp notφ_φ_derives_ψ
          . exact elim_and1
        . exact elim_and2
      exact intro_imp Γ_derives_bot
    _ vdash _ := dne

-- 背理法
theorem proof_contradiction :
  (φ land lnot ψ vdash bot) -> (φ vdash ψ)
:= by
  intro h
  calc
    φ vdash lnot lnot ψ := intro_imp h
    _ vdash ψ := dne

-- 対偶法
theorem proof_contraposition :
  (lnot φ vdash lnot ψ) <-> (ψ vdash φ)
:= by
  constructor
  . intro h1
    calc
      ψ vdash lnot lnot φ := by
        have ψnotφ_derives_bot : ψ land lnot φ vdash bot := by
          apply modus_ponens
          . exact elim_and1
          . calc
              ψ land lnot φ vdash lnot φ := elim_and2
              _ vdash lnot ψ := h1
        exact intro_imp ψnotφ_derives_bot
      _ vdash φ := dne
  . intro h2
    have φnotψ_derives_bot : lnot φ land ψ vdash bot := by
      apply modus_ponens
      . calc
          lnot φ land ψ vdash ψ := elim_and2
          _ vdash φ := h2
      . exact elim_and1
    exact intro_imp φnotψ_derives_bot

-- ## 同値

-- 連言への代入
theorem substitution_iff :
  φ land (φ iff ψ) vdash ψ
:= by
  apply modus_ponens
  . exact elim_and1
  . calc
    φ land (φ iff ψ) vdash φ iff ψ := elim_and2
    _ vdash φ imply ψ := elim_and1

-- 含意の前件への代入
theorem substitution_iff_to_imply1 :
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
theorem substitution_iff_to_imply2 :
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
theorem intro_top :
  φ vdash top
:= by
  have φbot_derives_bot : φ land bot vdash bot := elim_and2
  exact intro_imp φbot_derives_bot

-- 連言の単位律
theorem land_unit :
  Equiv φ (top land φ)
:= by
  constructor
  . apply intro_and
    . exact intro_top
    . exact ax
  . exact elim_and2

-- ## 選言

-- 選言の導入則１
theorem intro_or1 :
  φ vdash φ lor ψ
:= by
  have φnotφ_derives_ψ : φ land lnot φ vdash ψ := by
    calc
      φ land lnot φ vdash bot := elim_not
      _ vdash ψ := explosion
  exact intro_imp φnotφ_derives_ψ

-- 選言の導入則２
theorem intro_or2 :
  φ vdash ψ lor φ
:= lukasiewicz

-- 選言の除去則
theorem elim_or :
  (φ land ψ vdash χ) -> (φ land ω vdash χ) -> (φ land (ψ lor ω) vdash χ)
:= by
  intro h1 h2
  calc
    φ land (ψ lor ω) vdash lnot lnot χ := by
      let Γ1 := (φ land (ψ lor ω)) land lnot χ
      have Γ1_derives_φ : Γ1 vdash φ := by
        calc
          Γ1 vdash φ land (ψ lor ω) := elim_and1
          _ vdash φ := elim_and1
      have Γ1_derives_bot : Γ1 vdash bot := by
        apply modus_ponens
        . calc
            Γ1 vdash φ land ψ := by
              apply intro_and
              . exact Γ1_derives_φ
              . calc
                Γ1 vdash lnot lnot ψ := by
                  let Γ2 := Γ1 land lnot ψ
                  have Γ2_derives_φ : Γ2 vdash φ := by
                    calc
                      Γ2 vdash Γ1 := elim_and1
                      _ vdash φ := Γ1_derives_φ
                  have Γ2_derives_notχ : Γ2 vdash lnot χ := by
                    calc
                      Γ2 vdash Γ1 := elim_and1
                      _ vdash lnot χ := elim_and2
                  have Γ2_derives_ψorω : Γ2 vdash ψ lor ω := by
                    calc
                      Γ2 vdash Γ1 := elim_and1
                      _ vdash φ land (ψ lor ω) := elim_and1
                      _ vdash ψ lor ω := elim_and2
                  have Γ2_derives_bot : Γ2 vdash bot := by
                    apply modus_ponens
                    . calc
                        Γ2 vdash φ land ω := by
                          apply intro_and
                          . exact Γ2_derives_φ
                          . apply modus_ponens
                            . exact elim_and2
                            . exact Γ2_derives_ψorω
                        _ vdash χ := h2
                    . exact Γ2_derives_notχ
                  exact intro_not Γ2_derives_bot
                _ vdash ψ := dne
            _ vdash χ := h1
        . exact elim_and2
      exact intro_not Γ1_derives_bot
    _ vdash χ := dne

-- 選言の除去則（簡易版）
theorem elim_or0 :
  (φ vdash ψ) -> (χ vdash ψ) -> (φ lor χ vdash ψ)
:= by
  intro h1 h2
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
theorem lor_idempotence :
  φ vdash φ lor φ
:= intro_or1

-- 選言の結合律
theorem lor_associative1 :
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
theorem lor_exchange :
  φ lor ψ vdash ψ lor φ
:= by
  apply elim_or0
  . exact intro_or2
  . exact intro_or1

-- 選言三段論法
theorem disjunctive_syllogism :
  lnot φ land (φ lor ψ) vdash ψ
:= by
  apply elim_or
  . calc
    lnot φ land φ vdash φ land lnot φ := land_exchange
    _ vdash bot := elim_not
    _ vdash ψ := explosion
  . exact elim_and2

-- 吸収律１
theorem absorption1 :
  Equiv (φ lor (φ land ψ)) φ
:= by
  constructor
  . apply elim_or0
    . exact ax
    . exact elim_and1
  . exact intro_or1

-- 吸収律２
theorem absorption2 :
  Equiv (φ land (φ lor ψ)) φ
:= by
  constructor
  . exact elim_and1
  . apply intro_and
    . exact ax
    . exact intro_or1

-- 分配律１
theorem distributive1 :
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
theorem distributive2 :
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
theorem de_morgan1 :
  Equiv ((lnot φ) lor (lnot ψ)) (lnot (φ land ψ))
:= by
  constructor
  . let Γ1 := (lnot φ lor lnot ψ) land (φ land ψ)
    have Γ1_derives_bot : Γ1 vdash bot := by
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
    exact intro_not Γ1_derives_bot
  · let Θ := lnot φ lor lnot ψ
    calc
      lnot (φ land ψ) vdash lnot lnot Θ := by
        let Γ2 := (lnot (φ land ψ)) land lnot Θ
        have Γ2_derives_bot : Γ2 vdash bot := by
          apply modus_ponens
          . calc
              (lnot (φ land ψ)) land lnot Θ vdash lnot φ := by
                have Γ2φ_derives_bot : Γ2 land φ vdash bot := by
                  apply modus_ponens
                  . calc
                      (Γ2 land φ) vdash lnot ψ := by
                        have Γ2φψ_derives_bot : (Γ2 land φ) land ψ vdash bot := by
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
                        exact intro_not Γ2φψ_derives_bot
                      _ vdash Θ := intro_or2
                  . calc
                      Γ2 land φ vdash (lnot (φ land ψ)) land lnot Θ := elim_and1
                      _ vdash lnot Θ := elim_and2
                exact intro_not Γ2φ_derives_bot
              _ vdash Θ := intro_or1
          . exact elim_and2
        exact intro_not Γ2_derives_bot
      _ vdash Θ := dne

-- De Morganの法則２
theorem de_morgan2 :
  Equiv (lnot φ land lnot ψ) (lnot (φ lor ψ))
:= by
  constructor
  · have notφornotψ_and_φorψ_derives_bot : (lnot φ land lnot ψ) land (φ lor ψ) vdash bot := by
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
    exact intro_not notφornotψ_and_φorψ_derives_bot
  · apply intro_and
    · have φorψ_and_φ_derives_bot : lnot (φ lor ψ) land φ vdash bot := by
        apply modus_ponens
        . calc
            lnot (φ lor ψ) land φ vdash φ := elim_and2
            φ vdash φ lor ψ := intro_or1
        . exact elim_and1
      exact intro_not φorψ_and_φ_derives_bot
    · have φorψ_and_ψ_derives_bot : lnot (φ lor ψ) land ψ vdash bot := by
        apply modus_ponens
        . calc
            lnot (φ lor ψ) land ψ vdash ψ := elim_and2
            ψ vdash φ lor ψ := intro_or2
        . exact elim_and1
      exact intro_not φorψ_and_ψ_derives_bot

-- 排中律
theorem excluded_middle :
  top vdash φ lor lnot φ
:= by
  let Θ := φ lor lnot φ
  calc
    top vdash lnot lnot Θ := by
      have notΘ_derives_bot : top land lnot Θ vdash bot := by
        calc
          top land lnot Θ vdash lnot Θ := elim_and2
          _ vdash bot := by
            apply modus_ponens
            . calc
                lnot Θ vdash lnot φ := by
                  have notΘφ_derives_bot : lnot Θ land φ vdash bot := by
                    apply modus_ponens
                    . calc
                        lnot Θ land φ vdash φ := elim_and2
                        φ vdash Θ := intro_or1
                    . exact elim_and1
                  exact intro_not notΘφ_derives_bot
                _ vdash Θ := intro_or2
            . exact ax
      exact intro_imp notΘ_derives_bot
    _ vdash Θ := dne

-- Dummetの法則
theorem dummet :
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
                  have notΘΘ_vdash_φ : lnot Θ land Θ vdash φ := by
                    calc
                      lnot Θ land Θ vdash Θ land lnot Θ := land_exchange
                      _ vdash bot := elim_not
                      _ vdash φ := explosion
                  exact intro_imp notΘΘ_vdash_φ
                _ vdash φ := peirce
                _ vdash ψ imply φ := lukasiewicz
            _ vdash Θ lor (ψ imply φ) := intro_or2

-- ## 量化

-- 全称の除去則（簡易版）
theorem elim_forall0 :
  (lforall x, φ) vdash φ
:= by
  calc
    (lforall x, φ) vdash (Formula.substitute x (Term.var x) φ) := elim_forall
    _ vdash φ := by simpa [Formula.subst_self] using ax

-- 量化と演繹
theorem forall_monotone :
  (φ vdash ψ) -> ((lforall x, φ) vdash (lforall x, ψ))
:= by
  intro h1
  have h0 : x ∉ Formula.free_vars (lforall x, φ) := by
    simp [Formula.free_vars]
  have allφ_derives_ψ: (lforall x, φ) vdash ψ := by
    calc
      (lforall x, φ) vdash φ := elim_forall0
      _ vdash ψ := h1
  exact intro_forall h0 allφ_derives_ψ

-- アルファ同値の導出
theorem alpha_equivalence:
  y ∉ Formula.all_vars φ
  -> Equiv (lforall x, φ) (lforall y, Formula.substitute x (Term.var y) φ)
:= by
  intro h0
  have h0_split : y ∉ Formula.free_vars φ ∧ y ∉ Formula.bound_vars φ := by
    simpa [Formula.all_vars, not_or] using h0
  let φ_y := Formula.substitute x (Term.var y) φ
  constructor
  . have h0_1 : y ∉ Formula.free_vars (lforall x, φ) := by
      simp [Formula.free_vars, h0_split]
    have allφ_derives_φy : (lforall x, φ) vdash φ_y := by
      exact elim_forall
    exact intro_forall h0_1 allφ_derives_φy
  . by_cases y_eq_x : y = x
    . simpa [y_eq_x, φ_y, Formula.subst_self] using ax
    . have h0_2 : x ∉ Formula.free_vars (lforall y, φ_y) := by
        have h0_21 : x ∉ Formula.free_vars φ_y := by
          have x_neq_y : x ≠ y := by
            simpa [eq_comm] using y_eq_x
          exact Formula.subst_clean x_neq_y
        simp [h0_21, Formula.free_vars]
      have allφy_derives_φ : (lforall y, φ_y) vdash φ := by
        calc
          (lforall y, φ_y) vdash (Formula.substitute y (Term.var x) φ_y) := by
            simpa [Formula.substitute] using elim_forall
          _ vdash φ := (Formula.subst_double h0).1
      exact intro_forall h0_2 allφy_derives_φ

-- 存在の導入則
theorem intro_exists :
  (Formula.substitute x t φ) vdash (lexists x, φ)
:= by
  have hh : (Formula.substitute x t φ) land (lforall x, lnot φ) vdash bot := by
    apply modus_ponens
    . exact elim_and1
    . calc
        (Formula.substitute x t φ) land (lforall x, lnot φ) vdash (lforall x, lnot φ) := elim_and2
        _ vdash (Formula.substitute x t (lnot φ)) := elim_forall
        _ vdash lnot (Formula.substitute x t φ) := by
          simpa [Formula.lnot, Formula.substitute] using ax
  exact intro_not hh

-- 存在の導入則（簡易版）
theorem intro_exists0 :
  φ vdash (lexists x, φ)
:= by
  calc
    φ vdash (Formula.substitute x (Term.var x) φ) := by simpa [Formula.subst_self] using ax
    _ vdash (lexists x, φ) := intro_exists

-- 存在の除去則
theorem elim_exists :
  x ∉ Formula.free_vars φ ∪ Formula.free_vars χ
  -> (φ land ψ vdash χ)
  -> (φ land (lexists x, ψ) vdash χ)
:= by
  intro h0 h1
  let Γ := (φ land (lexists x, ψ)) land (lnot χ)
  have h0' : x ∉ Formula.free_vars Γ := by
    have h0_split :
      x ∉ Formula.free_vars φ
      ∧ x ∉ Formula.free_vars χ
    := by
      simpa [not_or] using h0
    simp [Γ, Formula.free_vars, Formula.lexists, Formula.lnot, h0_split]

  have Γ_derives_bot : Γ vdash bot := by
    apply modus_ponens
    . have Γ_derives_notψ : Γ vdash lnot ψ := by
        have Γψ_derives_bot : (Γ land ψ) vdash bot := by
          apply modus_ponens
          . calc
              (Γ land ψ) vdash (φ land ψ) := by
                apply intro_and
                . calc
                  Γ land ψ vdash Γ := elim_and1
                  _ vdash φ land (lexists x, ψ) := elim_and1
                  _ vdash φ := elim_and1
                . exact elim_and2
              _ vdash χ := h1
          . calc
            Γ land ψ vdash Γ := elim_and1
            _ vdash lnot χ := elim_and2
        exact intro_not Γψ_derives_bot
      exact intro_forall h0' Γ_derives_notψ
    . calc
        Γ vdash (φ land (lexists x, ψ)) := elim_and1
        _ vdash lexists x, ψ := elim_and2
  exact proof_contradiction Γ_derives_bot

-- 存在の除去則（簡易版）
theorem elim_exists0 :
  x ∉ Formula.free_vars ψ
  -> (φ vdash ψ)
  -> (lexists x, φ) vdash ψ
:= by
  intro h0 h1
  have h0' : x ∉ Formula.free_vars (S:=S) top ∪ Formula.free_vars ψ := by
    simpa [Formula.free_vars, Formula.top] using h0
  have topφ_derives_ψ : top land φ vdash ψ := by
    calc
      top land φ vdash φ := elim_and2
      _ vdash ψ := h1
  calc
    (lexists x, φ) vdash top land (lexists x, φ) := land_unit.left
    _ vdash ψ := elim_exists h0' topφ_derives_ψ

-- 全称量化子の交換
theorem forall_exchange :
  (lforall x, (lforall y, φ)) vdash (lforall y, (lforall x, φ))
:= by
  let Γ := lforall x, (lforall y, φ)
  have Γ_derives_φ : Γ vdash φ := by
    calc
      Γ vdash (lforall y, φ) := elim_forall0
      _ vdash φ := elim_forall0
  have Γ_derives_allxφ : Γ vdash (lforall x, φ) := by
    have h0_x : x ∉ Formula.free_vars Γ := by
      simp [Γ, Formula.free_vars]
    exact intro_forall h0_x Γ_derives_φ
  have h0_y : y ∉ Formula.free_vars Γ := by
    simp [Γ, Formula.free_vars]
  exact intro_forall h0_y Γ_derives_allxφ

-- 存在量化子の交換
theorem exists_exchange :
  (lexists x, (lexists y, φ)) vdash (lexists y, (lexists x, φ))
:= by
  let Θ := lexists y, (lexists x, φ)
  have φ_derives_Θ : φ vdash Θ := by
    calc
      φ vdash (lexists x, φ) := intro_exists0
      _ vdash Θ := intro_exists0
  have existsyφ_derives_Θ : (lexists y, φ) vdash Θ := by
    have h0_y : y ∉ Formula.free_vars Θ := by
      simp [Θ, Formula.free_vars, Formula.lexists, Formula.lnot]
    exact elim_exists0 h0_y φ_derives_Θ
  have h0_x : x ∉ Formula.free_vars Θ := by
      simp [Θ, Formula.free_vars, Formula.lexists, Formula.lnot]
  exact elim_exists0 h0_x existsyφ_derives_Θ

-- 量化子と否定１
theorem forall_exists_lnot1 :
  Equiv (lforall x, lnot φ) (lnot (lexists x, φ))
:= by
  constructor
  . exact intro_dn
  . exact proof_contraposition.1 intro_dn

-- 量化子と否定２
theorem forall_exists_lnot2 :
  Equiv (lnot (lforall x, φ)) (lexists x, lnot φ)
:= by
  constructor
  . exact proof_contraposition.2 (forall_monotone dne)
  . exact proof_contraposition.2 (forall_monotone intro_dn)

-- 全称量化子と連言
theorem forall_distribution_over_land :
  Equiv ((lforall x, φ) land (lforall x, ψ)) (lforall x, φ land ψ)
:= by
  constructor
  . let Γ1 := (lforall x, φ) land (lforall x, ψ)
    have h0_Γ1 : x ∉ Formula.free_vars Γ1 := by
      simp [Γ1, Formula.free_vars]
    have Γ1_derives_φψ : Γ1 vdash φ land ψ := by
      apply intro_and
      . calc
          Γ1 vdash (lforall x, φ) := elim_and1
          _ vdash φ := elim_forall0
      . calc
          Γ1 vdash (lforall x, ψ) := elim_and2
          _ vdash ψ := elim_forall0
    exact intro_forall h0_Γ1 Γ1_derives_φψ
  . let Γ2 := lforall x, φ land ψ
    have h0_Γ2 : x ∉ Formula.free_vars Γ2 := by
      simp [Γ2, Formula.free_vars]
    apply intro_and
    . have Γ2_derives_φ : Γ2 vdash φ := by
        calc
          Γ2 vdash φ land ψ := elim_forall0
          _ vdash φ := elim_and1
      exact intro_forall h0_Γ2 Γ2_derives_φ
    . have Γ2_derives_ψ : Γ2 vdash ψ := by
        calc
          Γ2 vdash φ land ψ := elim_forall0
          _ vdash ψ := elim_and2
      exact intro_forall h0_Γ2 Γ2_derives_ψ

-- 存在量化子と選言
theorem exists_distribution_over_lor :
  Equiv ((lexists x, φ) lor (lexists x, ψ)) (lexists x, φ lor ψ)
:= by
  let Γ1 := (lexists x, φ) lor (lexists x, ψ)
  let Γ2 := lexists x, φ lor ψ
  constructor
  · have h0_Γ2 : x ∉ Formula.free_vars Γ2 := by
      simp [Γ2, Formula.free_vars, Formula.lexists, Formula.lnot]
    apply elim_or0
    . have φ_derives_Γ2: φ vdash Γ2 := by
        calc
          φ vdash φ lor ψ := intro_or1
          _ vdash Γ2 := intro_exists0
      exact elim_exists0 h0_Γ2 φ_derives_Γ2
    . have ψ_derives_Γ2: ψ vdash Γ2 := by
        calc
          ψ vdash φ lor ψ := intro_or2
          _ vdash Γ2 := intro_exists0
      exact elim_exists0 h0_Γ2 ψ_derives_Γ2
  · have h0_Γ1 : x ∉ Formula.free_vars Γ1 := by
      simp [Γ1, Formula.free_vars, Formula.lor, Formula.lexists, Formula.lnot]
    have φorψ_derives_Γ1 : (φ lor ψ) vdash Γ1 := by
      apply elim_or0
      · calc
          φ vdash (lexists x, φ) := intro_exists0
          _ vdash Γ1 := intro_or1
      · calc
          ψ vdash (lexists x, ψ) := intro_exists0
          _ vdash Γ1 := intro_or2
    exact elim_exists0 h0_Γ1 φorψ_derives_Γ1

-- 全称量化子と選言
theorem forall_distribution_over_lor :
  ((lforall x, φ) lor (lforall x, ψ)) vdash (lforall x, φ lor ψ)
:= by
  apply elim_or0
  · have h0_φ : x ∉ Formula.free_vars (lforall x, φ) := by
      simp [Formula.free_vars]
    have allxφ_derives_φorψ : (lforall x, φ) vdash (φ lor ψ) := by
      calc
        (lforall x, φ) vdash φ := elim_forall0
        _ vdash φ lor ψ := intro_or1
    exact intro_forall h0_φ allxφ_derives_φorψ
  · have h0_ψ : x ∉ Formula.free_vars (lforall x, ψ) := by
      simp [Formula.free_vars]
    have allxφ_derives_φorψ : (lforall x, ψ) vdash (φ lor ψ) := by
      calc
        (lforall x, ψ) vdash ψ := elim_forall0
        _ vdash φ lor ψ := intro_or2
    exact intro_forall h0_ψ allxφ_derives_φorψ

-- 存在量化子と連言
theorem exists_distribution_over_land :
  (lexists x, (φ land ψ)) vdash (lexists x, φ) land (lexists x, ψ)
:= by
  let Θ := (lexists x, φ) land (lexists x, ψ)
  have h0 : x ∉ Formula.free_vars Θ := by
    simp [Θ, Formula.free_vars, Formula.lexists, Formula.lnot]
  have φψ_derives_Θ : φ land ψ vdash Θ := by
    apply intro_and
    · calc
        φ land ψ vdash φ := elim_and1
        _ vdash lexists x, φ := intro_exists0
    · calc
        φ land ψ vdash ψ := elim_and2
        _ vdash lexists x, ψ := intro_exists0
  exact elim_exists0 h0 φψ_derives_Θ

-- 酒場の法則
theorem drinking_principle :
  y ∉ Formula.free_vars φ
  -> top vdash lexists x, (φ imply (lforall y, (Formula.substitute x (Term.var y) φ)))
:= by
  intro h0
  let φ_y := Formula.substitute x (Term.var y) φ
  let Γ := lforall y, φ_y
  let Γ_y := Formula.substitute x (Term.var y) Γ
  let Θ := lforall x, (lnot (φ imply Γ))
  have h0' : y ∉ Formula.free_vars Θ := by
    simp [Θ, Γ, Formula.free_vars, Formula.lnot, h0]
  have Θ_derives_bot : top land Θ vdash bot := by
    apply modus_ponens
    . exact elim_and2
    . calc
        top land Θ vdash Θ := elim_and2
        _ vdash Γ := by
          have Θ_derives_φy : Θ vdash φ_y := by
            calc
              Θ vdash (Formula.substitute x (Term.var y) (lnot (φ imply Γ))) := elim_forall
              _ vdash lnot (φ_y imply Γ_y) := by
                simpa [Formula.substitute, Formula.lnot] using ax
              _ vdash φ_y := not_imply_elim
          exact intro_forall h0' Θ_derives_φy
        Γ vdash (φ imply Γ) := lukasiewicz
        _ vdash lnot Θ := intro_exists0
  exact intro_not Θ_derives_bot

-- ## 等号

namespace WithEqual

  inductive pred (P : Type) : Type
  | equal : pred P
  | other : P → pred P

  def arity {P : Type} (arity_ : P → Nat) : pred P → Nat
  | .equal => 2
  | .other p => arity_ p

  def SignatureWithEqual (S : Signature) : Signature where
    Func := S.Func
    FuncArity := S.FuncArity
    Pred := WithEqual.pred S.Pred
    PredArity := WithEqual.arity S.PredArity

  def lift_term : Term S → Term (SignatureWithEqual S)
  | .var x => .var x
  | .func f args => .func f (fun i => lift_term (args i))

  def lift_formula : Formula S → Formula (SignatureWithEqual S)
  | .bot => .bot
  | .land φ ψ => .land (lift_formula φ) (lift_formula ψ)
  | .imply φ ψ => .imply (lift_formula φ) (lift_formula ψ)
  | .pred p args => .pred (pred.other p) (fun i => lift_term (args i))
  | .lforall x φ => .lforall x (lift_formula φ)

  def equal (t s : Term (SignatureWithEqual S)) : Formula (SignatureWithEqual S) :=
    .pred (pred.equal : pred S.Pred) (fun i => if (i : Nat) = 0 then t else s)

  open Formula

  variable {t s u : Term (SignatureWithEqual S)}
  variable {φ : Formula (SignatureWithEqual S)}

  axiom eq_reflexive :
    top vdash (equal t t)

  axiom eq_subst :
    (substitute x t φ) land (equal t s) vdash (substitute x s φ)

  theorem eq_symmetry :
    (equal t s) vdash (equal s t)
  := by
    let x := VarSet.fresh (Term.vars t)
    have x_nfree_t : x ∉ Term.vars t := by
      show x ∈ Term.vars t -> False
      intro x_free_t
      exact (VarSet.fresh_not_mem x_free_t) (by simp [x])
    have subst_equal (u : Term (SignatureWithEqual S)) :
      (substitute x u (equal (Term.var x) t)) = (equal u t)
    := by
      have same_t : (Term.substitute x u t) = t := by
        exact Term.subst_same x_nfree_t
      unfold equal
      simp [substitute]
      funext i
      cases i using Fin.cases with
      | zero =>
        simp [Term.substitute]
      | succ j =>
        simp [same_t]
    calc
      (equal t s) vdash (substitute x t (equal (Term.var x) t)) land (equal t s) := by
        apply intro_and
        . calc
            (equal t s) vdash top := intro_top
            _ vdash (equal t t) := eq_reflexive
            _ vdash (substitute x t (equal (Term.var x) t)) := by
              simpa [subst_equal] using ax
        . exact ax
      _ vdash (substitute x s (equal (Term.var x) t)) := eq_subst
      _ vdash (equal s t) := by simpa [subst_equal] using ax

  theorem eq_transitive :
    (equal t s) land (equal s u) vdash (equal t u)
  := by
    let x := VarSet.fresh (Term.vars t)
    have x_nfree_t : x ∉ Term.vars t := by
      show x ∈ Term.vars t -> False
      intro x_free_t
      exact (VarSet.fresh_not_mem x_free_t) (by simp [x])
    have subst_equal (v : Term (SignatureWithEqual S)) :
      (substitute x v (equal t (Term.var x))) = (equal t v)
    := by
      have same_t : (Term.substitute x v t) = t := by
        exact Term.subst_same x_nfree_t
      unfold equal
      simp [substitute]
      funext i
      cases i using Fin.cases with
      | zero =>
        simp [same_t]
      | succ j =>
        simp [Term.substitute]
    calc
      (equal t s) land (equal s u) vdash (substitute x s (equal t (Term.var x))) land (equal s u) := by
        apply intro_and
        . simpa [subst_equal] using elim_and1
        . exact elim_and2
      _ vdash (substitute x u (equal t (Term.var x))) := eq_subst
      _ vdash (equal t u) := by simpa [subst_equal] using ax

  theorem neq_symmetry :
    lnot (equal t s) vdash lnot (equal s t)
  := proof_contraposition.2 eq_symmetry

end WithEqual

end FirstOrderLogic
