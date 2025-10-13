namespace Option

theorem lt_getD [LT α] (lty : ∀ y, y? = some y → x < y) (ltz : y? = none → x < z)
  : x < Option.getD (α := α) y? z := match y? with
  | some y => lty y rfl
  | none => ltz rfl

end Option
