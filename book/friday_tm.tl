friday_tm
: ∀(n: Nat) (Equal Nat (halve (double n)) n)
= λn
  def T = λx(Equal Nat (halve (double x)) x)
  def if_succ = λnp (cong Nat Nat (halve (double np)) np succ (friday_tm np))
  def if_zero = (refl Nat zero)
  (~n T if_succ if_zero)
