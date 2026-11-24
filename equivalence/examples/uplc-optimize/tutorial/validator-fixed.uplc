(program
  1.1.0
  (case
    (constr
      0
      (force (builtin tailList))
      (force (builtin ifThenElse))
      (force (force (builtin sndPair)))
      (force (builtin headList))
    )
    (lam
      forced-80
      (lam
        forced-81
        (lam
          forced-82
          (lam
            forced-83
            (lam
              context-78
              [
                (lam result-79 (con unit ()))
                (case
                  (constr
                    0
                    (con bool True)
                    (con integer 1)
                    [
                      [ (builtin divideInteger) (con integer 1) ]
                      [
                        [
                          (builtin subtractInteger)
                          [
                            (builtin unIData)
                            [
                              forced-83
                              [
                                forced-82
                                [
                                  (builtin unConstrData)
                                  [
                                    forced-83
                                    [
                                      forced-80
                                      [
                                        forced-82
                                        [
                                          (builtin unConstrData)
                                          [
                                            forced-83
                                            [
                                              forced-80
                                              [
                                                forced-80
                                                [
                                                  forced-82
                                                  [
                                                    (builtin unConstrData)
                                                    context-78
                                                  ]
                                                ]
                                              ]
                                            ]
                                          ]
                                        ]
                                      ]
                                    ]
                                  ]
                                ]
                              ]
                            ]
                          ]
                        ]
                        (con integer 1)
                      ]
                    ]
                  )
                  forced-81
                )
              ]
            )
          )
        )
      )
    )
  )
)