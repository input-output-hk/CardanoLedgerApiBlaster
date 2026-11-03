(program
  1.1.0
  (lam
    x-0
    [
      [ [ (force (builtin ifThenElse)) (con bool True) ] (con integer 7) ]
      [
        (builtin unIData)
        [
          [
            [
              (force (builtin ifThenElse))
              [ [ (builtin equalsInteger) x-0 ] (con integer 42) ]
            ]
            (con data (B #00))
          ]
          (con data (I 0))
        ]
      ]
    ]
  )
)