(set-logic BV)

(synth-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4)
    ((Start (_ BitVec 4)))
    ((Start (_ BitVec 4) (s #x0 #x8 #x7 (bvneg Start) (bvnot Start) (bvadd Start Start) (bvsub Start Start) (bvand Start Start) (bvlshr Start Start) (bvor Start Start) (bvshl Start Start)))))

(declare-var s (_ BitVec 4))

(constraint (= (inv s #x8) (bvand (bvnot (bvadd s #x8)) #x8)))

(check-synth)

