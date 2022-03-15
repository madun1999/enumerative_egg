(set-logic BV)

(synth-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4)
    ((Start (_ BitVec 4)))
    ((Start (_ BitVec 4) (s t #x0 #x8 #x7 (bvneg Start) (bvnot Start) (bvadd Start Start)))))

(declare-var s (_ BitVec 4))
(declare-var t (_ BitVec 4))

(constraint (= (inv s t) (bvadd s t)))

(check-synth)

