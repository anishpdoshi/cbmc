; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)

(declare-fun |inv_8| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> true 
    (|inv_8| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_4| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_8| |main::1::1::y_1| |main::1::x_1|)
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (_ bv0 32) |main::1::x|)) 
    (|inv_4| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_7| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_4| |main::1::1::y| |main::1::x|)
       (not (bvsge |main::1::x| (_ bv3 32)))) 
    (|inv_7| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_5| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_7| |main::1::1::y_1| |main::1::x_1|)
       (= (_ bv0 32) |main::1::1::y|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_5| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_6| ((_ BitVec 32) (_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_5| |main::1::1::y| |main::1::x|)
       (not (bvsge |main::1::1::y| (_ bv3 32)))) 
    (|inv_6| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_6| |main::1::1::y_1| |main::1::x_1|)
       (= (bvadd |main::1::1::y_1| (_ bv1 32)) |main::1::1::y|)
       (= |main::1::x_1| |main::1::x|)) 
    (|inv_5| |main::1::1::y| |main::1::x|))))

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::1::y_1| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)) (|main::1::x_1| (_ BitVec 32)))
  (=> (and 
    (|inv_5| |main::1::1::y_1| |main::1::x_1|)
       (not (not (bvsge |main::1::1::y_1| (_ bv3 32))))
       (= |main::1::1::y_1| |main::1::1::y|)
       (= (bvadd |main::1::x_1| |main::1::1::y_1|) |main::1::x|)) 
    (|inv_4| |main::1::1::y| |main::1::x|))))

(declare-fun |inv_3| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::1::y| (_ BitVec 32)) (|main::1::x| (_ BitVec 32)))
  (=> 
    (|inv_4| |main::1::1::y| |main::1::x|) 
    (|inv_3| |main::1::x|))))

(declare-fun |inv_2| ((_ BitVec 32) ) Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_3| |main::1::x|)
       (not (not (bvsge |main::1::x| (_ bv3 32))))) 
    (|inv_2| |main::1::x|))))

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (not (= |main::1::x| (_ bv0 32)))) false)))

(declare-fun |inv_1| () Bool)

(assert (forall ((|main::1::x| (_ BitVec 32)))
  (=> (and 
    (|inv_2| |main::1::x|)
       (= |main::1::x| (_ bv0 32))) 
    |inv_1|)))

(assert (=> 
    |inv_1| true))

(check-sat)