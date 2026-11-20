(program 1.1.0
  (lam rate (lam amount (lam metadata (lam bonus
    [(builtin iData)
      [[(builtin addInteger)
        [[(builtin divideInteger) [[(builtin multiplyInteger) amount] rate]] (con integer 10000)]]
        bonus]])))))
