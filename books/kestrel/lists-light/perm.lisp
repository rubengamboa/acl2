; Theorems about perm
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "perm-def")
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove1-equal" :dir :system))

(defthm perm-self
  (perm x x)
  :hints (("Goal" :in-theory (enable perm))))

(defthmd memberp-when-perm
  (implies (perm x y)
           (equal (memberp a x)
                  (memberp a y)))
  :hints (("Goal" :in-theory (enable perm))
          ("subgoal *1/2" :cases ((equal a (car x))))))

(defthm perm-of-remove1-equal-and-remove1-equal
  (implies (perm x y)
           (perm (remove1-equal a x)
                 (remove1-equal a y)))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-transitive-1
  (implies (and (perm x y) ;y is a free var
                (perm y z))
           (perm x z))
  :hints (("Goal" :in-theory (enable perm))
          ("subgoal *1/5" :use (:instance memberp-when-perm
                                           (a (car x))
                                           (x y)
                                           (y z)))))

(defthm perm-transitive-2
  (implies (and (perm y z) ;y is a free var
                (perm x y))
           (perm x z))
  :hints (("Goal" :use (:instance perm-transitive-1)
           :in-theory (disable perm-transitive-1))))

(defthm perm-symmetric
  (implies (perm x y)
           (perm y x))
  :hints (("Goal" :induct (PERM Y X) :in-theory (enable perm))
          ("subgoal *1/2" :use (:instance perm-of-remove1-equal-and-remove1-equal
                                          (a (car y)))
           :in-theory (e/d (perm) (perm-of-remove1-equal-and-remove1-equal)))
          ("subgoal *1/3" :use (:instance memberp-when-perm
                                          (a (car y))))))

(defequiv perm)

(defcong perm equal (memberp a x) 2
  :hints (("Goal" :use (:instance memberp-when-perm (y x-equiv)))))

(defcong perm perm (remove1-equal a x) 2)

;; (defcong perm equal (subsetp-equal x y) 1)

(defthm perm-of-true-list-fix-arg1
  (equal (perm (true-list-fix x) y)
         (perm x y))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-of-true-list-fix-arg2
  (equal (perm x (true-list-fix y))
         (perm x y))
  :hints (("Goal" :in-theory (enable perm))))

;; Uses perm as the equivalence relation.
(defthm perm-of-true-list-fix
  (perm (true-list-fix x) x)
  :hints (("Goal" :in-theory (enable perm))))

(defcong perm equal (perm x y) 1)
(defcong perm equal (perm x y) 2)

(defthm perm-of-cons-arg1
  (equal (perm (cons a x) y)
         (and (memberp a y)
              (perm (remove1-equal a y) x)))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-of-cons-arg2
  (equal (perm x (cons a y))
         (and (memberp a x)
              (perm (remove1-equal a x) y)))
  :hints (("Goal" :in-theory (enable perm))))

;; Uses perm as the equivalence relation.  Our normal form brings the conses to
;; the front.
(defthm perm-of-append-of-cons
  (perm (append x (cons a y))
        (cons a (append x y)))
  :hints (("Goal" :in-theory (enable perm append))))

(defthm perm-of-append-of-cdr-and-cons-of-car
  (implies (consp x)
           (perm (append (cdr x) (cons (car x) y))
                 (append x y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm perm-of-append
  (perm (append x y)
        (append y x))
  :hints (("Goal" :in-theory (e/d (perm append remove1-equal)
                                  (remove1-equal-of-append)))))


(defthmd perm-when-not-consp-arg1
  (implies (not (consp x))
           (equal (perm x y)
                  (not (consp y))))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (equal (perm x y)
                  (not (consp y))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable perm))))

(defthmd perm-when-not-consp-arg2
  (implies (not (consp y))
           (equal (perm x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-when-not-consp-arg2-cheap
  (implies (not (consp y))
           (equal (perm x y)
                  (not (consp x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable perm))))

;; TODO: add a backchain-limit?
(defthm perm-of-append-when-not-consp
  (implies (not (consp y))
           (perm (append x y)
                 x))
  :hints (("Goal" :in-theory (enable perm append))))

(defcong perm perm (append x y) 1
  :hints (("Goal" :in-theory (enable perm))))

(defcong perm perm (append x y) 2
  :hints (("Goal" :in-theory (enable perm))))

;; This is kind of like moving a subtraction from one side of an equality to
;; become an addition on the other side.
(defthmd perm-of-remove1-equal
  (equal (perm (remove1-equal a x) y)
         (if (memberp a x)
             (perm x (cons a y))
           (perm x y)))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-of-append-of-nthcdr-and-take
  (implies (<= (nfix n) (len x))
           (perm (append (nthcdr n x) (take n x))
                 x))
  :hints (("Goal" :in-theory (enable perm append))))

(defthm perm-of-list-of-car-self
  (equal (perm x (list (car x)))
         (equal 1 (len x)))
  :hints (("Goal" :in-theory (enable perm))))

;; TODO: move
(defthm no-duplicatesp-equal-of-remove1-equal-when-at-most-one
  (implies (not (memberp a (remove1-equal a x))) ;there is at most one copy of a in x
           (equal (no-duplicatesp-equal (remove1-equal a x))
                  (no-duplicatesp-equal x))))

(defthmd no-duplicatesp-equal-when-perm-1
  (implies (and (perm l1 l2)
                (no-duplicatesp-equal l1))
           (no-duplicatesp-equal l2))
  :hints (("Goal" :in-theory (enable perm no-duplicatesp-equal))))

(defthmd no-duplicatesp-equal-when-perm-2
  (implies (and (perm l2 l1)
                (no-duplicatesp-equal l1))
           (no-duplicatesp-equal l2))
  :hints (("Goal" :in-theory (enable perm no-duplicatesp-equal))))

(defcong perm equal (no-duplicatesp-equal x) 1
  :hints (("Goal" :in-theory (enable perm))))
