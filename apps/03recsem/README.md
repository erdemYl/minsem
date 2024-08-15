Minimal record semantic subtyping framework
=====

* Type grammar: 
   *              t = true | (t, t) | rec | t & t | !t
   *              rec = { true => t, (Any,Any) => t } 
                      | { true := t, (Any,Any) => t }