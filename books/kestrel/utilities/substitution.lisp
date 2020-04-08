; Utilities that perform substitution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;This version is simpler than sublis-var and, unlike sublis-var, doesn't evaluate ground terms.
;we could change this to not build ground terms (instead just evaluate the function on its constant arguments)
;also, if the test for an if is a ground term (which evals to a constant), don't build both branches of the if..
;well, now we have my-sublis-var-and-eval...
;if there are variables in form that are not bound in alist, they are left alone (for some uses it may be better to throw an error?)
(mutual-recursion
 (defun my-sublis-var (alist form) ;todo: call this 'term'?
   (declare (xargs :measure (acl2-count form)
                   :guard (and (symbol-alistp alist)
                               (pseudo-termp form))))
   (cond ((variablep form)
          (let ((a (assoc-eq form alist)))
            (cond (a (cdr a)) (t form))))
         ((fquotep form) form)
         (t (cons ;try fcons-term
             (ffn-symb form)
             (my-sublis-var-lst alist (fargs form))))))

 (defun my-sublis-var-lst (alist l)
   (declare (xargs :measure (acl2-count l)
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp l))))
   (if (endp l) ;(null l)
       nil
     (cons (my-sublis-var alist (car l))
           (my-sublis-var-lst alist (cdr l))))))

(defun my-sublis-var-induction (flg alist form)
  (if (atom form)
      (list flg alist form)
    (if flg ; i.e., if x is a list of terms
        (list (my-sublis-var-induction nil alist (car form))
              (my-sublis-var-induction t alist (cdr form)))
      (my-sublis-var-induction t alist (fargs form)))))

(defthm my-sublis-var-of-nil-helper
  (if flg
      (implies (pseudo-term-listp term)
               (equal (my-sublis-var-lst nil term)
                      term))
    (implies (pseudo-termp term)
             (equal (my-sublis-var nil term)
                    term)))
  :rule-classes nil
  :hints (("Goal" :induct (my-sublis-var-induction flg nil term)
           :in-theory (enable my-sublis-var))))

(defthm my-sublis-var-lst-of-nil
  (implies (pseudo-term-listp l)
           (equal (my-sublis-var-lst nil l)
                  l))
  :hints (("Goal" :use (:instance my-sublis-var-of-nil-helper (term l) (flg t)))))

(defthm my-sublis-var-of-nil
  (implies (pseudo-termp form)
           (equal (my-sublis-var nil form)
                  form))
  :hints (("Goal" :use (:instance my-sublis-var-of-nil-helper (term form) (flg nil)))))

(defthm true-listp-of-my-sublis-var-lst
  (true-listp (my-sublis-var-lst alist terms)))

(defthm len-of-my-sublis-var-lst
  (equal (len (my-sublis-var-lst alist l))
         (len l)))

(defthm pseudo-termp-of-assoc-equal
  (implies (and (pseudo-term-listp (strip-cdrs alist))
                (assoc-equal term alist))
           (pseudo-termp (cdr (assoc-equal term alist))))
  :hints (("Goal" :in-theory (enable assoc-equal strip-cdrs))))

(defthm pseudo-termp-of-my-sublis-var-helper
  (if flg
      (implies (and (pseudo-term-listp term)
                    (pseudo-term-listp (strip-cdrs alist)))
               (pseudo-term-listp (my-sublis-var-lst alist term)))
    (implies (and (pseudo-termp term)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-termp (my-sublis-var alist term))))
  :rule-classes nil
  :hints (("Goal" :induct (my-sublis-var-induction flg nil term)
           :expand ((pseudo-termp (cons (car term)
                                        (my-sublis-var-lst alist (cdr term)))))
           :in-theory (enable my-sublis-var))))

(defthm pseudo-term-listp-of-my-sublis-var
  (implies (and (pseudo-term-listp terms)
                (pseudo-term-listp (strip-cdrs alist)))
           (pseudo-term-listp (my-sublis-var-lst alist terms)))
  :hints (("Goal" :use (:instance pseudo-termp-of-my-sublis-var-helper (flg t) (term terms)))))

;see also a version in terms.lisp
(defthm pseudo-termp-of-my-sublis-var2
  (implies (and (pseudo-termp form)
                (pseudo-term-listp (strip-cdrs alist)))
           (pseudo-termp (my-sublis-var alist form)))
  :hints (("Goal" :use (:instance pseudo-termp-of-my-sublis-var-helper (term form) (flg nil)))))
