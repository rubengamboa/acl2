; Utilities for processing defthm forms
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

;; Utilities for manipulating defthm events

;; TODO: Rename to defthm-forms.lisp

(defconst *defthm-types* '(defthm defthmd))

(defund defthm-formp (defthm)
  (declare (xargs :guard t))
  (and (true-listp defthm)
       (>= (len defthm) 3)
       (member-eq (first defthm) *defthm-types*)
       (symbolp (second defthm))     ;the theorem name
       ;; what to say about the body?  may contain macros?
       (keyword-value-listp (cdr (cdr (cdr defthm)))) ;skip the defthm, name, and body.
       ))

;; Drops :hints, :otf-flg, and :instructions from DEFTHM.
;; Also removes :flags used for make-flag
;todo: rename clean-up-defthm (since we delete more than just the hints)
(defund clean-up-defthm (defthm)
  (declare (xargs :guard (defthm-formp defthm)
                  :guard-hints (("Goal" :in-theory (enable defthm-formp)))))
  (let* ((defthm-variant (first defthm))
         (name (second defthm))
         (body (third defthm))
         (keyword-value-list (cdddr defthm))
         (rule-classes-supplied (assoc-keyword :rule-classes keyword-value-list))
         (rule-classes (cadr rule-classes-supplied)))
    `(,defthm-variant ,name
       ,body
       ,@(and rule-classes-supplied `(:rule-classes ,rule-classes)))))

;removes :hints, etc and also the :flag arguments
(defun clean-up-defthms (defthms)
  (if (atom defthms)
      nil
    (cons (clean-up-defthm (first defthms))
          (clean-up-defthms (rest defthms)))))

(defun defthm-form-listp (forms)
  (declare (xargs :guard t))
  (if (atom forms)
      (null forms)
    (and (defthm-formp (first forms))
         (defthm-form-listp (rest forms)))))
