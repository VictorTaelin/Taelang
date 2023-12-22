double
: ∀(n: Nat) Nat
= λn
  def T = λn(Nat)
  def if_succ = λp(succ (succ (double p)))
  def if_zero = zero
  (~n T if_succ if_zero)
