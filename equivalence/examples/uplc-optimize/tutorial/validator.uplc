(program 1.1.0
  (lam context
    [(lam datum
      [(lam result (con unit ()))
        [[[(force (builtin ifThenElse)) (con bool True)]
          (con integer 1)]
          [[(builtin divideInteger) (con integer 1)]
            [[(builtin subtractInteger) [(builtin unIData) datum]]
              (con integer 1)]]]])
      [(force (builtin headList)) [(force (force (builtin sndPair))) [(builtin unConstrData) [(force (builtin headList)) [(force (builtin tailList)) [(force (force (builtin sndPair))) [(builtin unConstrData) [(force (builtin headList)) [(force (builtin tailList)) [(force (builtin tailList)) [(force (force (builtin sndPair))) [(builtin unConstrData) context]]]]]]]]]]]]]))
