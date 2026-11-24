(program
  1.1.0
  [
    (lam
      forced-38
      (lam
        x-37
        (case
          (constr
            0
            (con bool True)
            (con integer 1)
            [ [ (builtin divideInteger) (con integer 1) ] x-37 ]
          )
          forced-38
        )
      )
    )
    (force (builtin ifThenElse))
  ]
)